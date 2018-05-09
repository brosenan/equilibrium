(ns equilibrium.core
  (:require [clojure.string :as str]))

(def all-names (atom #{}))

(defmacro data [& forms]
  `(do
     ~@(for [[ctor & args] forms]
         (let [funcname (symbol (str (name ctor) "#" (count args)))]
           `(defn ~funcname [~@args]
              (with-meta
                (list '~ctor ~@args)
                {:ctor ~(str (symbol (str *ns*) (name funcname)))}))))))

(defn- variable? [x]
  (and (symbol? x)
       (str/starts-with? (name x) "?")))

(defn- form-to-clj [form]
  (let [[sym & args] form]
    (when-not (symbol? sym)
      (throw (Exception. (str "Symbol expected at the beginning of a form. '" (pr-str sym) "' found in " (meta form)))))
    (cond
      (= sym 'if) (cons 'if (map to-clj args))
      :else
      (let [name-arity (str (name sym) "#" (count args))
            sym' (symbol (namespace sym) name-arity)
            ns (-> sym' resolve meta :ns)]
        (when (nil? ns)
          (throw (Exception. (str "Symbol " sym " cannot be resolved for arity " (count args) " in " (meta form)))))
        (cons (symbol (str ns) name-arity) (map to-clj args))))))

(defn to-clj [x]
  (cond (seq? x) (form-to-clj x)
        :else x))

(defn lhs-to-clj [pattern]
  (cond
    (seq? pattern) (vec (map lhs-to-clj pattern))
    (variable? pattern) pattern
    :else
    (symbol (str "$" (rand-int 1000000000)))))

(defn- ctor-key [[ctor & args]]
  (str (or (namespace ctor) *ns*) "/" (name ctor) "#" (count args)))

(defn- uniform-func [a b name]
  `(do
     (def ~(name "-code") (atom '~[a b]))
     (def ~(name "-comp") (atom (fn [~@(lhs-to-clj (rest a))] ~(to-clj b))))
     (defn ~(name "") [~@(rest a)] ~(cons `(deref ~(name "-comp")) (rest a)))))

(defn- polymorphic-func [a b name]
  `(do
     ~(when-not (contains? @all-names [(str *ns*) (name "")])
        (swap! all-names conj [(str *ns*) (name "")])
        `(do
           (def ~(name "-code") (atom {}))
           (def ~(name "-comp") (atom {}))
           (defn ~(name "") [& args#])))
     (swap! ~(name "-code") assoc ~(-> a second ctor-key) '~[a b])
     (swap! ~(name "-comp") assoc ~(-> a second ctor-key) (fn []))))

(defn- eq [a b]
  (if (symbol? a)
    `(def ~a ~b)
    ;; else
    (let [name (fn [suff]
                 (symbol (str (-> a first name) "#" (-> a rest count) suff)))]
      (if (variable? (second a))
        (uniform-func a b name)
        ;; else
        (polymorphic-func a b name)))))

;; Standatd library
(defn +#2 [a b]
  (+ a b))
(defn *#2 [a b]
  (* a b))

;; Keep this at the end of this module because it overrides = in this module.
(defmacro = [a b]
  (eq a b))
