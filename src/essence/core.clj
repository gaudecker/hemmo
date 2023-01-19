(ns essence.core
  (:require [clojure.string :as str]
            [clojure.core.match :refer [match]]
            [clojure.walk :refer [postwalk]]
            [essence.env :as env]))

(declare with-type assign-type assign-fn-type print-type-assignments eqt
         applicable? gen-type-equations gen-fn-type-equations unify unify-var
         check-occurrence unify-eqs substitute-type retype rename type= seq-type= type
         format-type print-substitutions print-type-equations eval fold-fns)

(defn with-type
  "Returns `form` with `type` assigned to its metadata."
  [form type]
  (assert (map? type) (format "type must be a map, got %s" type))
  (vary-meta (if (var? form) (var-get form) form) assoc :kind type))

(defn assign-type
  "Assigns symbolic type for given `form` and its subforms in the given `env`."
  ([env form] (assign-type env form (ns-name *ns*)))
  ([env form scope]
   (match form
     (['defn name args body] :seq) (assign-fn-type env 'defn scope args body name)
     (['defn docstring name args body] :seq) (assign-fn-type env 'defn scope args body name docstring)
     (['fn args body] :seq) (assign-fn-type env 'fn (str "fn-" (hash form)) args body)
     (['if & rest] :seq) (with-type `(~(assign-type env 'if scope) ~@(map #(assign-type env % scope) rest))
                           (env/make-tvar env scope))
     ;; TODO: Replace with arg destructuring & macros
     (['let bindings body] :seq) (let [formt (env/make-tvar env scope)
                                       bindings (map (fn [[name value]]
                                                       [(with-type name (env/make-tvar env scope))
                                                        (assign-type env value)])
                                                     (map vec (partition 2 bindings)))
                                       locals (into {} (map (fn [[name value]]
                                                              [name (type value)])
                                                            bindings))
                                       local-env (env/copy env locals)
                                       body (assign-type local-env body scope)]
                                   (with-type (list 'let (vec (apply concat bindings)) body) formt))
     :else
     (cond
       (list? form) (let [items (map #(assign-type env % scope) form)]
                      (with-type (into () (reverse items)) (env/make-tvar env)))
       (vector? form) (let [items (mapv #(assign-type env % scope) form)]
                        (with-type items (env/make-tvar env)))
       (map? form) (let [content (->> (map (fn [[key val]]
                                            [(assign-type env key scope)
                                             (assign-type env val scope)])
                                          form)
                                     (into {}))]
                     (with-type content (env/make-tvar env scope)))
       (symbol? form) (with-type form (or (env/resolve env form)
                                          (env/make-tvar env scope)))
       ((some-fn string? number? boolean? keyword?) form) form
       :else (throw (ex-info "unhandled form" {:form form}))))))

(defn assign-fn-type
  "Assigns symbolic type for a function form."
  ([env t scope args body] (assign-fn-type env t scope args body nil nil))
  ([env t scope args body name?] (assign-fn-type env t scope args body name? nil))
  ([env t scope args body name? docstring?]
   (let [formt (env/make-tvar env)
         name (when name? (with-type name? (env/make-tvar env)))
         args (mapv #(assign-destructuring-type env % scope) args)
         argv (with-type args {:kind :vector :items args})
         local-env (env/copy env (args-to-env args))
         body (assign-type local-env body scope)
         sym (with-type t (env/resolve env t))]
     (with-type (cond
                  (= sym 'defn) (if docstring?
                                  (list sym docstring? name argv body)
                                  (list sym name argv body))
                  (= sym 'fn) (list sym argv body))
       formt))))

(defn assign-destructuring-type
  "Assigns symbolic type for a destructuring form."
  [env form scope]
  (cond
    (symbol? form) (with-type form (env/make-tvar env scope))
    (vector? form) (with-type (mapv #(assign-destructuring-type env % scope) form) (env/make-tvar env scope))
    (map? form) (let [locals (atom {})]
                  (with-type (->> (map (fn [[val key]]
                                         (cond
                                           (= val :or) [:or (->> (map (fn [[val binding]]
                                                                        (let [env (env/copy env @locals)]
                                                                          [(assign-type env val scope) (assign-type env binding scope)]))
                                                                      key)
                                                                 (into {}))]
                                           (= val :as) [:as (with-type key (env/make-tvar env scope))]
                                           (keyword? key) (let [val (assign-destructuring-type env val scope)]
                                                            (when (symbol? val)
                                                              (swap! locals assoc val (type val)))
                                                            [val key])
                                           :else (throw (ex-info "invalid map destructuring pair" {:left val :right key}))))
                                       form)
                                  (into {}))
                    (env/make-tvar env scope)))
    :else (throw (ex-info "invalid argument form" {:form form}))))

(defn destructuring-bindings
  "Returns a vector of bound symbols from a destructuring form."
  ([form] (destructuring-bindings form []))
  ([form bindings]
   (cond
     (symbol? form) (conj bindings form)
     (vector? form) (reduce (fn [bindings form]
                              (concat bindings (destructuring-bindings form)))
                            bindings form)
     (map? form) (reduce (fn [bindings [val key]]
                           (cond
                             (and (= val :or) (map? key)) bindings
                             (and (= val :as) (symbol? key)) (conj bindings key)
                             (keyword? key) (concat bindings (destructuring-bindings val))
                             :else (throw (ex-info "invalid map destructuring pair" {:left val :right key}))))
                         bindings form)
     :else (throw (ex-info "invalid destructuring form" {:form form})))))

(comment
  (destructuring-bindings 'foo)
  (destructuring-bindings '{foo :foo {bar :bar} :baz :as all})
  (destructuring-bindings '[foo bar {a :a [b c] :d :or {a "baz"} :as third}]))

(defn args-to-env
  "Maps bound symbols from given argument vector `args` to their type."
  ([args] (args-to-env args {}))
  ([args env]
   (->> (map #(vector % (type %)) (destructuring-bindings args))
        (into {}))))

(comment
  (args-to-env (->> '[a [b c] {d :d :as all}]
                    (assign-type (env/from-ns)))))

(defn print-type-assignments
  [form]
  (let [assignments (atom [])]
    (clojure.walk/postwalk (fn [f]
                             (when (type f)
                               (swap! assignments conj {:form f :type (format-type (type f))}))
                             f)
                           form)
    (print "Type assignments:")
    (clojure.pprint/print-table @assignments)))

(defn applicable?
  "Returns true if the given `type` is applicable." ; TODO: Consider keywords as applicable
  [type]
  (or (= (:kind type) :tvar) (= (:kind type) :fn)))

(defn gen-type-equations
  "Returns a map of type equations for the given `form` and its subforms."
  ([form] (gen-type-equations form {}))
  ([form equations]
   (match form
     (['defn docstring name args body] :seq) (gen-fn-type-equations form args body equations)
     (['defn name args body] :seq) (gen-fn-type-equations form args body equations)
     (['fn args body] :seq) (gen-fn-type-equations form args body equations)
     (['if cond then else] :seq) (let [eqs (->> (gen-type-equations cond equations)
                                                (gen-type-equations then)
                                                (gen-type-equations else))]
                                   (assoc eqs
                                         (type cond) {:kind :boolean}
                                         (type form) (type then)
                                         (type form) (type else)))
     (['let bindings body] :seq) (let [eqs (gen-type-equations body equations)
                                       binding-eqs (reduce (fn [eqs [binding value]]
                                                             (let [eqs (->> (gen-type-equations binding eqs)
                                                                            (gen-type-equations value))]
                                                               (assoc eqs (type binding) (type value))))
                                                           eqs (partition 2 bindings))]
                                   (assoc binding-eqs (type form) (type body)))
     :else
     (cond
       (list? form) (let [[first & rest] form
                          eqs (conj (gen-type-equations first equations)
                                    (reduce (fn [eqs n] (gen-type-equations n eqs)) {} rest))
                          optype (type first)]
                      (cond
                        (applicable? optype) (assoc eqs (type first) {:kind :app :args (mapv type rest) :ret (type form)})
                        :else (assoc eqs (type form) {:kind :list :items (map type form)})))
       (vector? form) (let [eqs (reduce #(gen-type-equations %2 %1) equations form)]
                        (assoc eqs (type form) {:kind :vector :items (map type form)}))
       (map? form) (let [eqs (reduce (fn [eqs [key val]]
                                       (conj eqs (gen-type-equations key) (gen-type-equations val)))
                                     equations form)]
                     (assoc eqs (type form) {:kind :map :pairs (->> (map #(vector (type (first %)) (type (second %))) form) (into {}))}))
       (number? form) (assoc equations (type form) {:kind :number})
       (string? form) (assoc equations (type form) {:kind :string})
       (boolean? form) (assoc equations (type form) {:kind :boolean})
       (keyword? form) (assoc equations (type form) {:kind :keyword :name (str form)})
       (symbol? form) equations
       :else (throw (ex-info "unsupported form" {:form form}))))))

(defn gen-fn-type-equations
  "Generates type equations for a function form."
  [form args body equations]
  (let [eqs (->> (reduce #(gen-destructuring-type-equations %2 %1) equations args)
                 (gen-type-equations body))]
    (assoc eqs (type form) {:kind :fn :args (mapv type args) :ret (type body)})))

(defn gen-destructuring-type-equations
  ([form] (gen-destructuring-type-equations form {}))
  ([form equations]
   (cond
     (symbol? form) equations
     (vector? form) (assoc (reduce #(gen-destructuring-type-equations %2 %1) equations form)
                           (type form) {:kind :vector :items (mapv type form)})
     (map? form) (let [eqs (reduce (fn [eqs [val key]]
                                     (cond
                                       ;; :as binding gets the type of the surrounding map form
                                       (and (= val :as) (symbol? key)) (assoc eqs (type key) (type form))
                                       ;; :or symbols get the type of their form
                                       (and (= val :or) (map? key)) (reduce (fn [eqs [sym val]]
                                                                              (assoc eqs (type sym) {:kind :option :value (type val) :default true}))
                                                                            eqs key)
                                       ;; keyword binding gets destructured further (val is either sym, vec, or map)
                                       (keyword? key) (gen-destructuring-type-equations val eqs)
                                       :else (throw (ex-info "invalid map destructuring form" {:key val :value key :form form}))))
                                   equations form)]
                   (assoc eqs (type form) {:kind :map :pairs (->> (filter #(and (not= (first %) :or) (not= (first %) :as)) form)
                                                                 (map #(vector (type (second %)) (type (first %))))
                                                                 (into {}))}))
     :else (throw (ex-info "invalid destructuring form" {:form form})))))

(comment
  (gen-destructuring-type-equations (assign-type (env/from-ns) '{a :a :or {a 1}})))

(defn occurs-in? [var type subst]
  (cond
    (type= var type) true
    (and (= (:kind type) :tvar)
         (contains? subst type)) (occurs-in? var (get subst type) subst)
    (= (:kind type) :fn) (or (occurs-in? var (:ret type) subst)
                             (some #(occurs-in? var % subst) (:args type)))
    (= (:kind type) :vector) (some #(occurs-in? var % subst) (:items type))
    (= (:kind type) :map) (or (some #(occurs-in? var % subst) (keys type))
                              (some #(occurs-in? var % subst) (vals type)))
    :else false))

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
                  (throw (ex-info (format "type mismatch: expected %s, got %s" (format-type t1) (format-type t2)) {:t1 t1 :t2 t2}))))
              subst (keys p1))
      (throw (ex-info (format "type mismatch: expected %s, got %s" (format-type t1) (format-type t2))
                      {:t1 t1 :t2 t2})))))

(defn unify-option
  "Unifies option type `opt` with `type` using substitution map `subst`.

  Returns an updated substitution map."
  [opt type subst]
  (if (:default opt) ;; if the option has default value (it is :or bound) we can unify with its unwrapped type.
    (unify (:value opt) type subst)
    (throw (ex-info (format "type mismatch: expected %s, got %s" (format-type opt) (format-type type)) {:t1 opt :t2 type}))))

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
                    {:t1 (format-type t1) :t2 (format-type t2)}))))

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
                                  (format-type t1) (format-type t2))
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
     :else (throw (ex-info (format "cannot substitute type %s" (format-type type)) {:type type :subst subst :visited visited})))))

(defn retype
  "Assigns the true type of the given `form` and its subforms using the
  substitution map `subst`."
  [form subst names]
  (with-type form (-> (substitute-type (type form) subst)
                      (rename names))))

(defn rename
  "Renames all type variables in the given `type` sequentially starting from zero.

  For example, type t4 → t5 → t6 becomes t0 → t1 → t2."
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
    {:kind :vector :items items} (let [value {:kind :vector :items (map #(rename % names) items)}]
                                   (swap! names assoc type value value value)
                                   value)
    {:kind :map :pairs pairs} (let [value {:kind :map :pairs (->> (map (fn [[key val]] [(rename key names) (rename val names)])
                                                                       (:pairs type))
                                                                  (into {}))}]
                                (swap! names assoc type value value value)
                                value)
    :else type))

(defn type=
  "Returns `true` if given types are equal."
  [t1 t2]
  (match [t1 t2]
    [{:kind :number} {:kind :number}] true
    [{:kind :string} {:kind :string}] true
    [{:kind :boolean} {:kind :boolean}] true
    [{:kind :keyword :name n1} {:kind :keyword :name n2}] (= n1 n2)
    [{:kind :tvar :value v1 :scope s1} {:kind :tvar :value v2 :scope s2}] (and (= v1 v2) (= s1 s2))
    [{:kind :list :items i1} {:kind :list :items i2}] (seq-type= i1 i2)
    [{:kind :vec :items i1} {:kind :vec :items i2}] (seq-type= i1 i2)
    [{:kind :map :pairs p1} {:kind :map :pairs p2}] (= p1 p2)
    [{:kind :fn :args a1 :ret r1} {:kind :fn :args a2 :ret r2}] (and (type= r1 r2) (seq-type= a1 a2))
    :else (cond
            (every? (some-fn keyword? number? string? boolean?) [t1 t2]) (= t1 t2)
            :else false)))

(defn seq-type= [s1 s2]
  (and (= (count s1) (count s2))
       (every? (fn [[a b]] (type= a b)) (map list s1 s2))))

(defn type
  "Returns the type information of a given `form`."
  [form]
  (cond
    (number? form) {:kind :number}
    (boolean? form) {:kind :boolean}
    (string? form) {:kind :string}
    (keyword? form) {:kind :keyword :name (str form)}
    :else (-> form meta :kind)))

(defn format-type
  "Formats given type `t` for printing."
  [t]
  (match t
    {:kind :fn :args args :ret ret} (format "(%s → %s)" (str/join " → " (map format-type args)) (format-type ret))
    {:kind :app :args args :ret ret} (format "app (%s → %s)" (str/join " → " (map format-type args)) (format-type ret))
    {:kind :list :items items} (format "(%s)" (str/join " " (map format-type items)))
    {:kind :vector :items items} (format "[%s]" (str/join " " (map format-type items)))
    {:kind :map :pairs pairs} (format "{%s}" (str/join ", " (map #(str (format-type (first %)) " " (format-type (second %))) pairs)))
    {:kind :number} (format "Num")
    {:kind :string} (format "Str")
    {:kind :boolean} (format "Bool")
    {:kind :keyword :name name} (str name)
    {:kind :tvar :value val} (str (char (+ val 65))) ;(format "t%d" val)
    {:kind :tvar :value val :scope scope} (format "%s/t%d" (str scope) val)
    {:kind :option :value val} (format "%s?" (format-type val))
    {:kind :option :value val :default d} (format "%s?" (format-type val))
    :else (when ((some-fn number? boolean? string? keyword?) t)
            (format-type (type t)))))
            ;(throw (ex-info "unsupported type" {:type t})))))

(defn print-substitutions [subst]
  (print "Substitutions:")
  (clojure.pprint/print-table (mapv (fn [s] {:from (format-type (first s)) :to (format-type (second s))}) subst)))

(defn print-type-equations
  "Prints a sequence of type equations as a table."
  [eqs]
  (print "Type equations:")
  (clojure.pprint/print-table
   (map (fn [[l r]] {:from (format-type l) :to (format-type r)}) eqs)))

(defn eval-and-bind
  "Evaluates typed form `tform` and conditionally binds the result in a var so its type can be assigned."
  [form]
  (assert (type form) "type cannot be nil")
  (let [result (clojure.core/eval (vary-meta form dissoc :kind))
        bound (if (fn? result) ; Bind anonymous functions so we can store their type
                (intern *ns* (symbol (str "fn-" (hash result))) result)
                result)]
    (cond
      (or (instance? clojure.lang.Ref bound)
          ((some-fn var? symbol?) bound)) (do (alter-meta! bound assoc :kind (type form))
                                              bound)
      (coll? bound) (vary-meta bound assoc :kind (type form))
      :else bound)))

(defn eval
  ([form] (eval form (env/from-ns)))
  ([form env]
   (let [form (assign-type env form)
         eqts (gen-type-equations form)
         subst (unify-eqs eqts)
         names (atom {})]
     (print-type-assignments form)
     (print-type-equations eqts)
     (print-substitutions subst)
     (alter-meta! names assoc :count 0)
     (let [typed-form (retype form subst names)
           folded-form (fold typed-form true)]
       (eval-and-bind folded-form)))))

(defn fold
  "Folds (evaluate & replace) form and its subforms conditionally."
  [form top-level]
  (match form
    (['fn args body] :seq) (if top-level
                             (with-type (eval-and-bind form) (type form))
                             (vary-meta form dissoc :kind))
    :else
    (cond
      (list? form) (with-type (apply list (map #(fold % false) form)) (type form))
      (vector? form) (with-type (mapv #(fold % false) form) (type form))
      :else form)))

;; Demo
(comment
  (alter-meta! *ns* assoc :env (env/make env/*core-ctx*))

  (-> '(defn foo [f g x]
         (if (f (= x 1))
           (g x)
           20))
      eval type format-type)

  (-> '((fn [x] (+ x 1)) 1) eval type format-type)
  
  (-> '(if true [1 2] [1 3]) eval type format-type)
  (-> '{:foo 1 :bar true} eval type format-type)
  (-> '(if true {:foo 1} {:foo 2}) eval type format-type)

  (-> '(fn [[a b]] (+ a b)) eval type format-type)
  (-> '(fn [{a :a b :b :or {a 1}}] (+ a b)) eval type format-type)
  
  (-> '(defn square [x] (* x x)) eval type format-type)
  (-> '(foo false? (fn [x] (* x x)) 5) eval)
  
  (-> '(defn foo [f] (f 5)) eval type format-type)
  (-> 'identity env/resolve format-type)
  (-> '(foo identity) eval)

  (-> '(defn foo [f x]
         (- (f 3) (f x)))
      eval type format-type)

  (-> '(fn [f]
         (fn [t] (f t)))
      eval type format-type)

  (-> '(defn foo [f x]
         (if x
           (fn [t] (f t))
           (fn [j] (f x))))
      eval type format-type)
  )
