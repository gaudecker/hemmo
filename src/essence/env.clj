(ns essence.env)

(def ^:dynamic *core-ctx*
  "Core function types."
  {'defn {:kind :macro}
   'fn {:kind :special-form}
   'let {:kind :special-form}
   'if {:kind :special-form}
   '+ {:kind :fn :args [{:kind :number} {:kind :number}] :ret {:kind :number}}
   '- {:kind :fn :args [{:kind :number} {:kind :number}] :ret {:kind :number}}
   '* {:kind :fn :args [{:kind :number} {:kind :number}] :ret {:kind :number}}
   '/ {:kind :fn :args [{:kind :number} {:kind :number}] :ret {:kind :number}}
   '< {:kind :fn :args [{:kind :number} {:kind :number}] :ret {:kind :boolean}}
   '<= {:kind :fn :args [{:kind :number} {:kind :number}] :ret {:kind :boolean}}
   '> {:kind :fn :args [{:kind :number} {:kind :number}] :ret {:kind :boolean}}
   '>= {:kind :fn :args [{:kind :number} {:kind :number}] :ret {:kind :boolean}}
   '= {:kind :fn :args [{:kind :tvar :value 0 :scope '=} {:kind :tvar :value 0 :scope '=}] :ret {:kind :boolean}}
   'not= {:kind :fn :args [{:kind :tvar :value 0 :scope 'not=} {:kind :tvar :value 0 :scope 'not=}] :ret {:kind :boolean}}
   'and {:kind :fn :args [{:kind :boolean} {:kind :boolean}] :ret {:kind :boolean}}
   'or {:kind :fn :args [{:kind :boolean} {:kind :boolean}] :ret {:kind :boolean}}
   'true? {:kind :fn :args [{:kind :boolean}] :ret {:kind :boolean}}
   'false? {:kind :fn :args [{:kind :boolean}] :ret {:kind :boolean}}
   'identity {:kind :fn :args [{:kind :tvar :value 0 :scope 'identity}] :ret {:kind :tvar :value 0 :scope 'identity}}})

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
     {:kind :tvar :value count})))

(defn resolve
  "Returns the type of a given `symbol` in enviroment `env`."
  ([symbol] (resolve (from-ns) symbol))
  ([env symbol]
   (get @env symbol (if-let [var (clojure.core/resolve symbol)]
                      (essence.core/type var)))))
