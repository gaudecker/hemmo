(ns essence.core (:gen-class))

(def *special-forms* '[defmacro defn fn match ns let])

(defn read
  "Reads all forms from given string `str`. Returns a vector of read forms."
  [str]
  (let [reader (java.io.PushbackReader. (java.io.StringReader. str))]
    (binding [*read-eval* false]
      (loop [forms []]
          (let [form (try (clojure.core/read reader)
                          (catch Exception e (println (ex-message e))))]
            (if form
              (recur (conj forms form))
              forms))))))

(defn special-form?
  "Returns `true` if given symbol `form` is a special form."
  [form]
  (and (symbol? form)
       (some #(= % form) *special-forms*)))
  
(defn parse
  "Parses given `form` into an AST."
  [form]
  (cond
    (list? form) (let [[first & rest :as all] form]
                   (println "list form of" first "and" rest)
                   (cond
                     (special-form? first) (parse-special-form first rest)
                     (ifn? first) {:type :application
                                   :operator (parse first)
                                   :arguments (map parse rest)}
                     :else {:type :list :items (map parse all)}))
    (vector? form) {:type :vector :items (map parse form)}
    (map? form) {:type :map :pairs (map (fn [[key value]] [(parse key) (parse value)]) form)}
    (keyword? form) {:type :keyword :value form :const true}
    (symbol? form) {:type :symbol :value form}
    (string? form) {:type :string :value form :const true}
    (number? form) {:type :number :value form :const true}
    (boolean? form) {:type :boolean :value form :const true}))

(defn parse-special-form [name args]
  (cond
    (= name 'let) {:type :let :arguments (map parse args)}
    (= name 'match) {:type :match :arguments (map parse args)}
    (= name 'defn) {:type :defn :arguments (map parse args)}
    (= name 'defmacro) {:defmacro :match :arguments (map parse args)}
    (= name 'fn) {:type :fn :arguments (map parse args)}
    (= name 'ns) {:type :ns :arguments (map parse args)}))

(defn validate-arity
  "Returns true if the arity of given list `form` based on the given `template` vector is valid."
  [ctx form template]
  (let [arity (count template)]))

(defn assign-type
  "Assigns type for given `form` in the given context `ctx`."
  [ctx form])
