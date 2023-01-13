(ns essence.env)

(defn make
  "Returns a new type environment."
  ([] (make {}))
  ([values] (atom (conj {} values))))

(defn copy
  ([env] (copy env {}))
  ([env values] (let [new (atom (conj values @env))]
                  (alter-meta! new assoc :tvar-count (:tvar-count (meta env)))
                  new)))

(defn make-tvar
  "Returns a unique type variable and maps it to the given `symbol` in the given enviroment `env`."
  ([env] (make-tvar env nil))
  ([env scope]
   (let [count (:tvar-count (meta env) 0)]
     (alter-meta! env assoc :tvar-count (inc count))
     {:kind :tvar :value count :scope scope})))

(defn resolve
  "Returns the type of a given `symbol` in enviroment `env`."
  [env symbol]
  (get @env symbol nil))

(defn from-ns [ns]
  (if (contains? (meta ns) :env)
    (-> (meta ns) :env)
    (do (alter-meta! ns assoc :env (make essence.core/*core-ctx*))
        (from-ns ns))))
