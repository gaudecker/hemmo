(ns hemmo.core
  (:require [clojure.string :as str]
            [clojure.core.match :refer [match]]
            [clojure.walk :refer [postwalk]]
            [clojure.pprint :as pp]
            [clojure.main :as main]
            [hemmo.env :as env]))

(defn with-type
  "Returns `form` with `type` assigned to its metadata."
  [form type]
  (assert (map? type) (format "type must be a map, got %s" type))
  (vary-meta (if (var? form) (var-get form) form) assoc :kind type))

(defn macro?
  "Returns `true` if the given form is a macro."
  [form]
  (cond (var? form) (:macro (meta form) false)
        (symbol? form) (:macro (meta (ns-resolve *ns* form)) false)
        :else false))

(defn metable?
  "Returns `true` for any form that is able to hold meta data."
  [form]
  (instance? clojure.lang.IMeta form))

(defn constant? [form]
  (not (metable? form)))

(declare kind)

(defn resolve-type
  "Returns the type of a given `symbol` in enviroment `env`."
  ([symbol] (resolve *ns* symbol))
  ([env symbol]
   (get @env symbol (when-let [var (clojure.core/resolve symbol)]
                      (kind var)))))

(defn destructuring-bindings
  "Returns a vector of bound symbols from a destructuring form."
  [form]
  (cond
    (symbol? form) [form]
    (vector? form) (reduce (fn [bindings form]
                             (concat bindings (destructuring-bindings form)))
                           [] form)
    (map? form) (reduce (fn [bindings [val key]]
                          (cond
                            (and (= val :or) (map? key)) bindings
                            (and (= val :as) (symbol? key)) (conj bindings key)
                            (keyword? key) (concat bindings (destructuring-bindings val))
                            :else (throw (ex-info "invalid map destructuring pair" {:left val :right key}))))
                        [] form)
    :else (throw (ex-info "invalid destructuring form" {:form form}))))

(comment
  (destructuring-bindings 'foo)
  (destructuring-bindings '{foo :foo {bar :bar} :baz :as all})
  (destructuring-bindings '[foo bar {a :a [b c] :d :or {a "baz"} :as third}]))

(defn args-to-env
  "Maps bound symbols from given argument vector `args` to their type."
  [args]
  (->> (map #(vector % (kind %)) (destructuring-bindings args))
       (into {})))

(declare assign-destructuring-type assign-fn-type assign-def-type)

(defn assign-type
  "Assigns symbolic type for given `form` and its subforms in the given `env`."
  [env form]
  (match form
    (['def name doc init] :seq) (assign-def-type env name init doc)
    (['def name init] :seq) (assign-def-type env name init)
    ([(:or 'clojure.core/fn 'fn) & _rest] :seq) (assign-fn-type env form)
    (['if & rest] :seq) (with-type `(~(assign-type env 'if) ~@(map #(assign-type env %) rest))
                          (env/make-tvar env))
    (['let bindings body] :seq) (let [formt (env/make-tvar env)
                                      bindings (map (fn [[binding value]]
                                                      [(assign-destructuring-type env binding)
                                                       (assign-type env value)])
                                                    (map vec (partition 2 bindings)))
                                      locals (reduce (fn [locals [binding _]]
                                                       (conj locals (args-to-env binding)))
                                                     {} bindings)
                                      local-env (env/copy env locals)
                                      body (assign-type local-env body)]
                                  (with-type (list 'let (with-type (vec (apply concat bindings)) (env/make-tvar env)) body) formt))
    (['do & forms] :seq) (with-type `(do ~@(map #(assign-type env %) forms)) (env/make-tvar env))
    :else
    (cond
      (list? form) (let [exp (macroexpand-1 form)]
                     (if (not= form exp)
                       (assign-type env exp)
                       (with-type (apply list (map #(assign-type env %) exp)) (env/make-tvar env))))
      (vector? form) (let [items (mapv #(assign-type env %) form)]
                       (with-type items (env/make-tvar env)))
      (map? form) (let [content (->> (map (fn [[key val]]
                                            [(assign-type env key)
                                             (assign-type env val)])
                                          form)
                                     (into {}))]
                    (with-type content (env/make-tvar env)))
      (symbol? form) (with-type form (or (resolve-type env form)
                                         (env/make-tvar env)))
      (constant? form) form
      :else (throw (ex-info "unhandled form" {:form form})))))

(defn assign-def-type
  "Assigns symbolic type for a def form."
  ([env name init] (assign-def-type env name init nil))
  ([env name init doc?]
   (let [typed-name (with-type name (env/make-tvar env))
         ;; bind name to env for self refences / recursion
         local-env (env/copy env {typed-name (kind typed-name)})
         typed-init (assign-type local-env init)
         form (if doc?
                (list 'def typed-name doc? typed-init)
                (list 'def typed-name typed-init))]
     (with-type form (env/make-tvar env)))))

(defn assign-fn-type
  "Assigns symbolic type for an fn form."
  [env form]
  (let [form-type (env/make-tvar env)
        [name & decls] (cond
                       (and (-> form second symbol?) (-> form (nth 2) list?)) (rest form)
                       (and (-> form second symbol?) (-> form (nth 2) vector?)) [(second form) (list (nth form 2) (nth form 3))]
                       (-> form second list?) [nil (second form)]
                       (-> form second vector?) [nil (list (second form) (nth form 2))]
                       :else (throw (ex-info "unexpected fn form" {:form form})))
        typed-name (when name (with-type name (env/make-tvar env)))
        [args body] (first decls)
        typed-args (mapv #(assign-destructuring-type env %) args)
        argv (with-type typed-args {:kind :vector :items (mapv kind typed-args)})
        condj ((remove nil?) conj)
        local-env (env/copy env (condj (args-to-env typed-args) (when typed-name {typed-name (kind typed-name)})))
        typed-body (assign-type local-env body)]
    (println "local env" local-env)
    (with-type (if typed-name
                 (list 'fn typed-name argv typed-body)
                 (list 'fn argv typed-body))
      form-type)))

(defn assign-destructuring-type
  "Assigns symbolic type for a destructuring form."
  [env form]
  (cond
    (symbol? form) (with-type form (env/make-tvar env))
    (vector? form) (with-type (mapv #(assign-destructuring-type env %) form) (env/make-tvar env))
    (map? form) (let [locals (atom {})]
                  (with-type (->> (map (fn [[val key]]
                                         (cond
                                           (= val :or) [:or (->> (map (fn [[val binding]]
                                                                        (let [env (env/copy env @locals)]
                                                                          [(assign-type env val) (assign-type env binding)]))
                                                                      key)
                                                                 (into {}))]
                                           (= val :as) [:as (with-type key (env/make-tvar env))]
                                           (keyword? key) (let [val (assign-destructuring-type env val)]
                                                            (when (symbol? val)
                                                              (swap! locals assoc val (kind val)))
                                                            [val key])
                                           :else (throw (ex-info "invalid map destructuring pair" {:left val :right key}))))
                                       form)
                                  (into {}))
                    (env/make-tvar env)))
    :else (throw (ex-info "invalid argument form" {:form form}))))

(declare format-kind)

(defn print-type-assignments
  [form]
  (let [assignments (atom [])]
    (postwalk (fn [f]
                (when (kind f)
                  (swap! assignments conj {:form f :type (format-kind (kind f))}))
                f)
              form)
    (print "Type assignments:")
    (pp/print-table @assignments)))

(defn applicable?
  "Returns true if the given `type` is applicable." ; TODO: Consider keywords, vectors, maps as applicable
  [type]
  (or (= (:kind type) :tvar) (= (:kind type) :fn)))

(defn gen-destructuring-type-equations
  [form]
  (cond
    (symbol? form) []
    (vector? form) (conj (reduce #(concat %1 (gen-destructuring-type-equations %2)) [] form)
                         [(kind form) {:kind :vector :items (mapv kind form)}])
    (map? form) (conj (reduce (fn [eqs [val key]]
                                (cond
                                  ;; :as binding gets the type of the surrounding map form
                                  (and (= val :as) (symbol? key)) (conj eqs [(kind key) (kind form)])
                                  ;; :or symbols get the type of their form
                                  (and (= val :or) (map? key)) (reduce (fn [eqs [sym val]]
                                                                         (conj eqs [(kind sym) {:kind :option :value (kind val) :default true}]))
                                                                       eqs key)
                                  ;; keyword binding gets destructured further (val is either sym, vec, or map)
                                  (keyword? key) (gen-destructuring-type-equations val)
                                  :else (throw (ex-info "invalid map destructuring form" {:key val :value key :form form}))))
                              [] form)
                      [(kind form) {:kind :map :pairs (->> (filter #(and (not= (first %) :or) (not= (first %) :as)) form)
                                                           (map #(vector (kind (second %)) (kind (first %))))
                                                           (into {}))}])
    :else (throw (ex-info "invalid destructuring form" {:form form}))))

(comment
  (gen-destructuring-type-equations (assign-type (env/make) '{a :a :or {a 1}})))

(declare gen-fn-type-equations gen-def-type-equations)

(defn gen-type-equations
  "Returns a vector of type equations for the given `form` and its subforms.

  A type equation is a vector with two expressions [left right]."
  [form]
  (match form
    (['def _name _value] :seq) (gen-def-type-equations form)
    (['def _name _doc _value] :seq) (gen-def-type-equations form)
    (['fn args body] :seq) (gen-fn-type-equations form args body)
    (['fn name args body] :seq) (gen-fn-type-equations form name args body)
    (['if cond then else] :seq) (conj (concat (gen-type-equations cond)
                                              (gen-type-equations then)
                                              (gen-type-equations else))
                                      [(kind cond) {:kind :boolean}]
                                      [(kind form) (kind then)]
                                      [(kind form) (kind else)])
    (['let bindings body] :seq) (let [binding-eqs (reduce (fn [eqs [binding value]]
                                                            (println "binding from" binding (kind binding) "to" value (kind value))
                                                            (conj (concat eqs
                                                                          (gen-destructuring-type-equations binding)
                                                                          (gen-type-equations value)
                                        ;(gen-let-binding-type-equations binding value)
                                                                          )
                                        ; TODO: binding symbol -> type of symbol in value recursively
                                                                  [(kind binding) (kind value)]))
                                                          [] (partition 2 bindings))
                                      body-eqs (gen-type-equations body)]
                                  (conj (concat body-eqs binding-eqs) [(kind form) (kind body)]))
    (['do & forms] :seq) (conj (reduce #(concat %1 (gen-type-equations %2)) [] forms)
                               [(kind form) (kind (last forms))])
    :else
    (cond
      (list? form) (let [[first & rest] form
                         eqs (concat (gen-type-equations first)
                                     (reduce #(concat %1 (gen-type-equations %2)) [] rest))
                         optype (kind first)]
                     (cond
                       (applicable? optype) (conj eqs [optype {:kind :app :args (mapv kind rest) :ret (kind form)}])
                       :else (conj eqs [(kind form) {:kind :list :items (map kind form)}])))
      (vector? form) (conj (reduce #(concat %1 (gen-type-equations %2)) [] form)
                           [(kind form) {:kind :vector :items (mapv kind form)}])
      (map? form) (conj (reduce (fn [eqs [key val]]
                                  (concat eqs (gen-type-equations key) (gen-type-equations val)))
                                [] form)
                        [(kind form) {:kind :map :pairs (->> (map #(vector (kind (first %)) (kind (second %))) form) (into {}))}])
      (number? form) [[(kind form) {:kind :number}]]
      (string? form) [[(kind form) {:kind :string}]]
      (boolean? form) [[(kind form) {:kind :boolean}]]
      (keyword? form) [[(kind form) {:kind :keyword :name (str form)}]]
      (symbol? form) []
      :else (throw (ex-info "unsupported form" {:form form})))))

(defn gen-def-type-equations
  "Generates type equations for a def form."
  [[_ name value :as form]]
  (println "name" name "value" value)
  (conj (gen-type-equations value)
        [(kind form) (kind value)]
        [(kind name) (kind value)]))

(defn gen-fn-type-equations
  "Generates type equations for a function form."
  ([form args body] (gen-fn-type-equations form nil args body))
  ([form name args body]
   (let [eqs (conj (concat (reduce #(concat %1 (gen-destructuring-type-equations %2)) [] args)
                           (gen-type-equations body))
                   [(kind form) {:kind :fn :args (mapv kind args) :ret (kind body)}])]
     (if name (conj eqs [(kind name) (kind form)]) eqs))))

(declare seq-kind=)

(defn kind=
  "Returns `true` if given types are equal."
  [t1 t2]
  (match [t1 t2]
    [{:kind :number} {:kind :number}] true
    [{:kind :string} {:kind :string}] true
    [{:kind :boolean} {:kind :boolean}] true
    [{:kind :keyword :name n1} {:kind :keyword :name n2}] (= n1 n2)
    [{:kind :tvar :value v1 :scope s1} {:kind :tvar :value v2 :scope s2}] (and (= v1 v2) (= s1 s2))
    [{:kind :list :items i1} {:kind :list :items i2}] (seq-kind= i1 i2)
    [{:kind :vec :items i1} {:kind :vec :items i2}] (seq-kind= i1 i2)
    [{:kind :map :pairs p1} {:kind :map :pairs p2}] (= p1 p2)
    [{:kind :fn :args a1 :ret r1} {:kind :fn :args a2 :ret r2}] (and (kind= r1 r2) (seq-kind= a1 a2))
    [{:kind :fn :args a1 :ret r1} {:kind :app :args a2 :ret r2}] (and (kind= r1 r2) (seq-kind= a1 a2))
    [{:kind :app :args a1 :ret r1} {:kind :app :args a2 :ret r2}] (and (kind= r1 r2) (seq-kind= a1 a2))
    [{:kind :app :args a1 :ret r1} {:kind :fn :args a2 :ret r2}] (and (kind= r1 r2) (seq-kind= a1 a2))
    :else (cond
            (every? constant? [t1 t2]) (= t1 t2)
            :else false)))

(defn seq-kind= [s1 s2]
  (and (= (count s1) (count s2))
       (every? (fn [[a b]] (kind= a b)) (map list s1 s2))))

(defn occurs-in? [var type subst]
  (cond
    (kind= var type) true
    (and (= (:kind type) :tvar)
         (contains? subst type)) (occurs-in? var (get subst type) subst)
    (= (:kind type) :fn) (or (occurs-in? var (:ret type) subst)
                             (some #(occurs-in? var % subst) (:args type)))
    (= (:kind type) :vector) (some #(occurs-in? var % subst) (:items type))
    (= (:kind type) :map) (or (some #(occurs-in? var % subst) (keys type))
                              (some #(occurs-in? var % subst) (vals type)))
    :else false))

(declare unify)

(defn unify-var
  "Unifies variable `var` with `type` using substitution map `subst`.

  Returns an updated substitution map."
  [var type subst]
  (assert (= (:kind var) :tvar) "var must be a type variable")
  (cond
    (contains? subst var) (unify (get subst var) type subst)
    (and (= (:kind type) :tvar) (contains? subst type)) (unify var (get subst type) subst)
    (occurs-in? var type subst) nil
    :else (assoc subst var type)))

(defn unify-maps
  "Unifies two maps `t1` and `t2` using substitution map `subst`.

  Returns an updated substitution map."
  [t1 t2 subst]
  (let [p1 (:pairs t1) p2 (:pairs t2)]
    (if (<= (count p1) (count p2))
      (reduce (fn [subst key]
                (cond (contains? p2 key) (conj subst (unify (get p1 key) (get p2 key) subst))
                      (= (:kind (get p1 key)) :option) subst
                  :else
                  (throw (ex-info (format "type mismatch: expected %s, got %s" (format-kind t1) (format-kind t2)) {:t1 t1 :t2 t2}))))
              subst (keys p1))
      (throw (ex-info (format "type mismatch: expected %s, got %s" (format-kind t1) (format-kind t2))
                      {:t1 t1 :t2 t2})))))

(defn unify-option
  "Unifies option type `opt` with `type` using substitution map `subst`.

  Returns an updated substitution map."
  [opt type subst]
  (if (:default opt) ;; if the option has default value (it is :or bound) we can unify with its unwrapped type.
    (unify (:value opt) type subst)
    (throw (ex-info (format "type mismatch: expected %s, got %s" (format-kind opt) (format-kind type)) {:t1 opt :t2 type}))))

(defn unify-fn-app
  "Unifies function or application types `t1` and `t2`.
  
  Returns an updated substitution map."
  [t1 t2 subst]
  (if (= (count (:args t1))
         (count (:args t2)))
    (let [subst (unify (:ret t1) (:ret t2) subst)
          args (map vector (:args t1) (:args t2))]
      (reduce (fn [subst [a1 a2]] (unify a1 a2 subst)) subst args))
    (throw (ex-info (format "arity exception: expected %d arguments, got %d" (count (:args t1)) (count (:args t2)))
                    {:t1 (format-kind t1) :t2 (format-kind t2)}))))

(defn unify
  "Unifies two types `t1` and `t2` with initial substitution map `subst`.

  Returns a substitution map {name -> type} that unifies `t1` and `t2`,
  or `nil` if the types can't be unified."
  [t1 t2 subst]
  (cond
    (= t1 t2) subst
    (= (:kind t1) :tvar) (unify-var t1 t2 subst)
    (= (:kind t2) :tvar) (unify-var t2 t1 subst)
    (= (:kind t1) :option) (unify-option t1 t2 subst)
    (= (:kind t2) :option) (unify-option t2 t1 subst)
    (and (= (:kind t1) :app) (= (:kind t2) :fn)) (unify-fn-app t2 t1 subst)
    (and (= (:kind t2) :app) (= (:kind t1) :fn)) (unify-fn-app t1 t2 subst)
    (and (= (:kind t1) :fn) (= (:kind t2) :fn)) (unify-fn-app t1 t2 subst)
    (and (= (:kind t1) :vector)
         (= (:kind t2) :vector)) (if (= (count (:items t1))
                                        (count (:items t2)))
                                   (reduce (fn [subst [i1 i2]] (unify i1 i2 subst)) subst (map list (:items t1) (:items t2)))
                                   (throw (ex-info (format "incompatible vectors: expected %d items, got %d" (count (:items t1)) (count (:items t2)))
                                                   {:t1 t1 :t2 t2})))
    (and (= (:kind t1) :map)
         (= (:kind t2) :map)) (unify-maps t2 t1 subst)
    :else (throw (ex-info (format "type mismatch. expected %s, got %s"
                                  (format-kind t1) (format-kind t2))
                          {:t1 t1 :t2 t2}))))

(defn unify-eqs
  "Unifies all equations. Returns a substitution map."
  [equations]
  (reduce (fn [subst [left right]]
            (if-let [subst (unify left right subst)]
              subst
              (reduced subst)))
          {} equations))

(defn substitute-type
  "Applies the substitution map `subst` to `type`.

  Returns a type where all occurrences of variables found in `subst`
  are recursively replaced."
  ([type subst] (substitute-type type subst #{}))
  ([type subst visited]
   (assert (map? subst) "subst must be a map")
   (cond
     (empty? subst) type
     (= (:kind type) :boolean) type
     (= (:kind type) :number) type
     (= (:kind type) :string) type
     (= (:kind type) :macro) type
     (= (:kind type) :keyword) type
     (= (:kind type) :option) type
     (= (:kind type) :special-form) type
     (= (:kind type) :vector) {:kind :vector :items (mapv #(substitute-type % subst (conj visited type)) (:items type))}
     (= (:kind type) :map) {:kind :map :pairs (->> (map (fn [[key val]] [(substitute-type key subst (conj visited type))
                                                                         (substitute-type val subst (conj visited type))])
                                                       (:pairs type))
                                                  (into {}))}
     (= (:kind type) :tvar) (if (and (contains? subst type) (not (contains? visited type)))
                              (substitute-type (get subst type) subst (conj visited type))
                              type)
     (= (:kind type) :fn) {:kind :fn
                           :args (mapv #(substitute-type % subst (conj visited type)) (:args type))
                           :ret (substitute-type (:ret type) subst (conj visited type))}
     (= (:kind type) :app) {:kind :app
                            :args (mapv #(substitute-type % subst (conj visited type)) (:args type))
                            :ret (substitute-type (:ret type) subst (conj visited type))}
     :else (throw (ex-info (format "cannot substitute type %s" (format-kind type)) {:type type :subst subst :visited visited})))))

(defn rename
  "Renames all type variables in the given `type` sequentially starting from A.

  For example, type E → F → G becomes A → B → C."
  [type names]
  (match type
    {:kind :tvar} (get @names type
                       (let [value {:kind :tvar :value (:count (meta names) 0) :scope (:scope type)}]
                         (alter-meta! names update :count inc)
                         (swap! names assoc type value value value)
                         value))
    {:kind :fn :args args :ret ret} (let [value {:kind :fn :args (mapv #(rename % names) args) :ret (rename ret names)}]
                                      (swap! names assoc type value value value)
                                      value)
    {:kind :app :args args :ret ret} (let [value {:kind :fn :args (mapv #(rename % names) args) :ret (rename ret names)}]
                                       (swap! names assoc type value value value)
                                       value)
    {:kind :vector :items items} (let [value {:kind :vector :items (map #(rename % names) items)}]
                                   (swap! names assoc type value value value)
                                   value)
    {:kind :map :pairs pairs} (let [value {:kind :map :pairs (->> (map (fn [[key val]] [(rename key names) (rename val names)])
                                                                       pairs)
                                                                  (into {}))}]
                                (swap! names assoc type value value value)
                                value)
    :else type))

(defn retype
  "Assigns the true type of the given `form` and its subforms using the
  substitution map `subst`."
  [form subst names]
  (if (metable? form)
    (with-type form (-> (substitute-type (kind form) subst)
                        (rename names)))
    form))

(defn kind
  "Returns the type information of a given `form`."
  [form]
  (cond
    (number? form) {:kind :number}
    (boolean? form) {:kind :boolean}
    (string? form) {:kind :string}
    (keyword? form) {:kind :keyword :name (str form)}
    :else (-> form meta :kind)))

(defn format-kind
  "Formats given type `t` for printing."
  [t]
  (match t
    {:kind :fn :args args :ret ret} (format "(%s → %s)" (str/join " → " (map format-kind args)) (format-kind ret))
    {:kind :app :args args :ret ret} (format "app (%s → %s)" (str/join " → " (map format-kind args)) (format-kind ret))
    {:kind :list :items items} (format "(%s)" (str/join " " (map format-kind items)))
    {:kind :vector :items items} (format "[%s]" (str/join " " (map format-kind items)))
    {:kind :map :pairs pairs} (format "{%s}" (str/join ", " (map #(str (format-kind (first %)) " " (format-kind (second %))) pairs)))
    {:kind :number} (format "Num")
    {:kind :string} (format "Str")
    {:kind :boolean} (format "Bool")
    {:kind :keyword :name name} (str name)
    {:kind :tvar :value val} (str (char (+ val 65))) ;(format "t%d" val)
    {:kind :tvar :value val :scope scope} (format "%s/t%d" (str scope) val)
    {:kind :option :value val} (format "%s?" (format-kind val))
    {:kind :option :value val :default d} (format "%s? = %s" (format-kind val) (format-kind d))
    :else (when ((some-fn number? boolean? string? keyword?) t)
            (format-kind (kind t)))))

(defn print-substitutions [subst]
  (when (> (count subst) 0)
    (print "Substitutions:")
    (pp/print-table (mapv (fn [s] {:from (format-kind (first s)) :to (format-kind (second s))})
                          subst))))

(defn print-type-equations
  "Prints a sequence of type equations as a table."
  [eqs]
  (print "Type equations:")
  (pp/print-table
   (map (fn [[l r]] {:from (format-kind l) :to (format-kind r)}) eqs)))

(defn eval-and-bind
  "Evaluates typed form `tform` and conditionally binds the result in a var so its type can be assigned."
  [form]
  (assert (kind form) "type cannot be nil")
  (let [result (eval (if (metable? form)
                       (vary-meta form dissoc :kind)
                       form))
        bound (if (fn? result) ; Bind anonymous functions so we can store their type
                (intern *ns* (symbol (str "fn-" (hash result))) result)
                result)]
    (cond
      (or (instance? clojure.lang.Ref bound)
          (var? bound)) (do (alter-meta! bound assoc :kind (kind form))
                            bound)
      (coll? bound) (vary-meta bound assoc :kind (kind form))
      :else bound)))

(defn fold
  "Folds (evaluate & replace) form and its subforms conditionally."
  [form top-level]
  (match form
    (['fn _args _body] :seq) (if top-level
                               (with-type (eval-and-bind form) (kind form))
                               (vary-meta form dissoc :kind))
    :else
    (cond
      (list? form) (with-type (map #(fold % false) form) (kind form))
      (vector? form) (with-type (mapv #(fold % false) form) (kind form))
      :else form)))

(defn typed-eval
  [form]
  (let [form (assign-type (env/make env/*core-ctx*) form)
        eqts (gen-type-equations form)
        subst (unify-eqs eqts)
        names (atom {})]
    (print-type-assignments form)
    (print-type-equations eqts)
    (print-substitutions subst)
    (alter-meta! names assoc :count 0)
    (let [typed-form (retype form subst names)
          folded-form (fold typed-form true)]
      (eval-and-bind folded-form))))

(defn- repl [_args]
  (main/repl :eval #(typed-eval %)))
