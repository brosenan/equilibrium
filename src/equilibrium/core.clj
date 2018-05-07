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

(defn- ctor-key [[ctor & args]]
  (str (or (namespace ctor) *ns*) "/" (name ctor) "#" (count args)))

(defn- uniform-func [a b name]
  `(do
     (def ~(name "-code") (atom '~[a b]))
     (def ~(name "-comp") (atom (fn [~@(rest a)] ~b)))
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

;; Keep this at the end of this module because it overrides = in this module.
(defmacro = [a b]
  (eq a b))
