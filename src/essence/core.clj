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
  (assert (map? type) "type must be a map")
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
         args (mapv #(with-type % (env/make-tvar env scope)) args)
         argv (with-type args {:kind :vector :items args})
         local-env (env/copy env (->> (map #(vector % (type %)) args)
                                      (into {})))
         body (assign-type local-env body scope)
         sym (with-type t (env/resolve env t))]
     (with-type (cond
                  (= sym 'defn) (if docstring?
                                  (list sym docstring? name argv body)
                                  (list sym name argv body))
                  (= sym 'fn) (list sym argv body))
       formt))))

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

(defn eqt
  "Returns a type equation with a `left` and `right` expressions and a reference
  `form`."
  [left right form]
  {:left left :right right :form form})

(defn applicable?
  "Returns true if the given `type` is applicable." ; TODO: Consider keywords as applicable
  [type]
  (or (= (:kind type) :tvar) (= (:kind type) :fn)))

(defn gen-type-equations
  "Returns a vector of type equations for the given `form` and its subforms."
  ([form] (gen-type-equations form []))
  ([form equations]
   (match form
     (['defn docstring name args body] :seq) (gen-fn-type-equations form args body equations)
     (['defn name args body] :seq) (gen-fn-type-equations form args body equations)
     (['fn args body] :seq) (gen-fn-type-equations form args body equations)
     (['if cond then else] :seq) (let [eqs (->> (gen-type-equations cond equations)
                                                (gen-type-equations then)
                                                (gen-type-equations else))]
                                   (conj eqs
                                         (eqt (type cond) {:kind :boolean} cond)
                                         (eqt (type form) (type then) then)
                                         (eqt (type form) (type else) else)))
     (['let bindings body] :seq) (let [eqs (gen-type-equations body equations)
                                       binding-eqs (mapcat (fn [[binding value :as form]]
                                                             (let [eqs (->> (gen-type-equations binding)
                                                                            (gen-type-equations value))]
                                                               (conj eqs (eqt (type binding)
                                                                              (type value)
                                                                              form))))
                                                           (partition 2 bindings))]
                                   (concat (conj eqs (eqt (type form) (type body) form))
                                           binding-eqs))
     :else
     (cond
       (list? form) (let [[first & rest] form
                          eqs (concat (gen-type-equations first equations)
                                      (mapcat gen-type-equations rest))
                          optype (type first)]
                      (cond
                        (applicable? optype) (conj eqs
                                                   (eqt (type first) {:kind :fn :args (mapv type rest) :ret (type form)} form))
                        :else (conj eqs
                                    (eqt (type form) {:kind :list :items (map type form)} form))))
       (vector? form) (let [eqs (concat equations (mapcat gen-type-equations form))]
                        (conj eqs
                              (eqt (type form) {:kind :vector :items (map type form)} form)))
       (number? form) (conj equations (eqt (type form) {:kind :number} form))
       (string? form) (conj equations (eqt (type form) {:kind :string} form))
       (boolean? form) (conj equations (eqt (type form) {:kind :boolean} form))
       (keyword? form) (conj equations (eqt (type form) {:kind :keyword :name (str form)} form))
       (symbol? form) equations
       :else (throw (ex-info "unsupported form" {:form form}))))))

(defn gen-fn-type-equations
  "Generates type equations for a function form."
  [form args body equations]
  (let [eqs (gen-type-equations body equations)]
    (conj eqs 
          (eqt (type form) {:kind :fn :args (mapv type args) :ret (type body)} form))))

(defn occurs-in? [var type subst]
  (cond
    (type= var type) true
    (and (= (:kind type) :tvar)
         (contains? subst type)) (occurs-in? var (get subst type) subst)
    (= (:kind type) :fn) (or (occurs-in? var (:ret type) subst)
                             (some #(occurs-in? var % subst) (:args type)))
    (= (:kind type) :vector) (some #(occurs-in? var % subst) (:items type))
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

(defn unify
  "Unifies two types `t1` and `t2` with initial substitution map `subst`.

  Returns a substitution map {name type} that unifies `t1` and `t2`,
  or `nil` if the types can't be unified."
  [t1 t2 subst]
  (println "unifying t1" (format-type t1) "t2" (format-type t2))
  (cond
    (= t1 t2) subst
    (= (:kind t1) :tvar) (unify-var t1 t2 subst)
    (= (:kind t2) :tvar) (unify-var t2 t1 subst)
    (and (= (:kind t1) :fn)
         (= (:kind t2) :fn)) (if (= (count (:args t1))
                                      (count (:args t2)))
                               (let [subst (unify (:ret t1) (:ret t2) subst)
                                     args (map list (:args t1) (:args t2))]
                                 (reduce (fn [subst [a1 a2]] (unify a1 a2 subst)) subst args))
                               (throw (ex-info (format "arity exception: expected %d arguments, got %d" (count (:args t1)) (count (:args t2)))
                                               {:t1 (format-type t1) :t2 (format-type t2)})))
    (and (= (:kind t1) :vector)
         (= (:kind t2) :vector)) (if (= (count (:items t1))
                                        (count (:items t2)))
                                   (reduce (fn [subst [i1 i2]] (unify i1 i2 subst)) subst (map list (:items t1) (:items t2)))
                                   (throw (ex-info (format "incompatible vectors: expected %d items, got %d" (count (:items t1)) (count (:items t2)))
                                                   {:t1 t1 :t2 t2})))
    :else (throw (ex-info (format "type mismatch. expected %s, got %s"
                                  (format-type t1) (format-type t2))
                          {:t1 t1 :t2 t2}))))

(defn unify-eqs
  "Unifies all equations. Returns a substitution map."
  [equations]
  (reduce (fn [subst {left :left right :right}]
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
     (= (:kind type) :special-form) type
     (= (:kind type) :vector) {:kind :vector :items (mapv #(substitute-type % subst (conj visited type)) (:items type))}
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

  For example, type [t4 t5] -> t6 becomes [t0 t1] -> t2."
  [type names]
  (match type
    {:kind :tvar} (get @names type
                       (let [value {:kind :tvar :value (:count (meta names) 0) :scope (:scope type)}]
                         (alter-meta! names update :count inc)
                         (swap! names assoc type value value value)
                         value))
    {:kind :fn :args args :ret ret} (let [value {:kind :fn
                                                 :args (map #(rename % names) args)
                                                 :ret (rename ret names)}]
                                      (swap! names assoc type value value value)
                                      value)
    {:kind :vector :items items} (let [value {:kind :vector
                                              :items (map #(rename % names) items)}]
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
    [{:kind :fn :args a1 :ret r1} {:kind :fn :args a2 :ret r2}] (and (type= r1 r2) (seq-type= a1 a2))
    :else false))

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
  "Formats given type `t` for pretty printing."
  [t]
  (match t
    {:kind :fn :args args :ret ret} (format "[%s] → %s" (str/join ", " (map format-type args)) (format-type ret))
    {:kind :list :items items} (format "(%s)" (str/join " " (map format-type items)))
    {:kind :vector :items items} (format "[%s]" (str/join " " (map format-type items)))
    {:kind :number} (format "Num")
    {:kind :string} (format "Str")
    {:kind :boolean} (format "Bool")
    {:kind :keyword :name name} (format name)
    {:kind :tvar :value val} (str (char (+ val 65))) ;(format "t%d" val)
    {:kind :tvar :value val :scope scope} (format "%s/t%d" (str scope) val)
    :else (when ((some-fn number? boolean? string? keyword?) t)
            (format-type (type t)))))

(defn print-substitutions [subst]
  (print "Substitutions:")
  (clojure.pprint/print-table (mapv (fn [s] {:from (format-type (first s)) :to (format-type (second s))}) subst)))

(defn print-type-equations
  "Prints a sequence of type equations as a table."
  [eqs]
  (print "Type equations:")
  (clojure.pprint/print-table
   (map (fn [{l :left r :right f :form}]
          { "form" f "left" (format-type l) "right" (format-type r)})
        eqs)))

(defn eval-and-bind
  "Evaluates typed form `tform` and conditionally binds the result in a var so its type can be assigned."
  [tform]
  (assert (type tform) "type cannot be nil")
  (let [result (clojure.core/eval (vary-meta tform dissoc :kind))
        bound (if (fn? result) ; Bind anonymous functions so we can store their type
                (intern *ns* (symbol (str "fn-" (hash result))) result)
                result)]
    (cond
      (or (instance? clojure.lang.Ref bound)
          ((some-fn var? symbol?) bound)) (do (alter-meta! bound assoc :kind (type tform))
                                              bound)
      (coll? bound) (vary-meta bound assoc :kind (type tform))
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
       (println "typed" typed-form (format-type (type typed-form)))
       (println "flded" folded-form (format-type (type folded-form)))
       (eval-and-bind folded-form)))))

(defn fold [form top-level]
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
  
  (-> '(if true [1 2] [1 true]) eval type format-type)
  (-> '{:foo 1 :bar true} eval)
  
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
