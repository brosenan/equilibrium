(ns equilibrium.core
  (:require [clojure.string :as str]))

(def ^:dynamic *curr-func*)

(defmacro data [& forms]
  `(do
     ~@(for [[ctor & args] forms]
         (let [funcname (symbol (str (name ctor) "#" (count args)))]
           `(defn ~funcname [~@args]
              (list '~(symbol (str *ns*) (str ctor "#" (count args))) ~@args))))))

(defn- variable? [x]
  (and (symbol? x)
       (str/starts-with? (name x) "?")))

(defn canonical-symbol [form]
  (let [[sym & args] form]
    (when-not (symbol? sym)
      (throw (Exception. (str "Symbol expected at the beginning of a form. '" (pr-str sym) "' found in " (meta form)))))
    (let [arity (count args)
          name-arity (str (name sym) "#" arity)
          sym' (symbol (namespace sym) name-arity)
          ns (-> sym' resolve meta :ns)]
      (if (= sym' *curr-func*)
        (symbol (str *ns*) (str sym'))
        ;; else
        (do
          (when (nil? ns)
            (throw (Exception. (str "Symbol " sym " cannot be resolved for arity " arity " in " (meta form)))))
          (symbol (str ns) name-arity))))))

(declare to-clj)

(defn- form-to-clj [form]
  (let [[sym & args] form]
    (cond
      (= sym 'if) (cons 'if (map to-clj args))
      :else
      (cons (canonical-symbol form) (map to-clj args)))))

(defn to-clj [x]
  (cond (seq? x) (form-to-clj x)
        :else x))

(defn lhs-to-clj [pattern]
  (cond
    (seq? pattern) (vec (map lhs-to-clj pattern))
    (variable? pattern) pattern
    :else
    (symbol (str "$" (rand-int 1000000000)))))
(defn trace [x]
  (prn x)
  x)

(defn tre [expr sym]
  (if (= (and (seq? expr) (canonical-symbol expr)) sym)
    (list 'equilibrium.core/recur (vec (rest expr)))
    ;; else
    (list 'equilibrium.core/return expr)))

(data (return ?val)
      (recur ?args))

(defn- uniform-func [a b name]
  `(do
     (def ~(name "-code") (atom '~[a b]))
     (def ~(name "-comp") (atom (fn [~@(lhs-to-clj (rest a))] ~(to-clj b))))
     (defn ~(name "") [~@(rest a)] ~(cons `(deref ~(name "-comp")) (rest a)))))

(defn- polymorphic-func [a b name]
  (let [dummy-args (vec (for [i (range (count (rest a)))]
                              (symbol (str "$" i))))
        [key & args] dummy-args]
    `(do
       ~(when (nil? (resolve (name "")))
          `(do
             (def ~(name "-code") (atom {}))
             (def ~(name "-comp") (atom {}))
             (defn ~(name "") [~key ~@args]
               (let [func# (get @~(name "-comp") (first ~key))]
                 (when (nil? func#)
                   (throw (Exception. (str "No equation for " (first ~key) " in function " ~(str (first a)) ". Options are: " (keys @~(name "-comp"))))))
                 (let [[op# val#] (func# ~key ~@args)]
                   (cond
                     (= op# 'equilibrium.core/return#1) val#
                     (= op# 'equilibrium.core/recur#1)
                     (let [~dummy-args val#]
                       (recur ~@dummy-args))))))))
       (swap! ~(name "-code") assoc '~(-> a second to-clj first) '~[a b])
       (swap! ~(name "-comp") assoc '~(-> a second to-clj first)
              (fn ~(lhs-to-clj (rest a))
                ~(-> b (tre (canonical-symbol a)) to-clj))))))

(defn- eq [a b]
  (if (symbol? a)
    `(def ~a ~b)
    ;; else
    (let [name (fn [suff]
                 (symbol (str (-> a first name) "#" (-> a rest count) suff)))]
      (binding [*curr-func* (name "")]
        (if (variable? (second a))
          (uniform-func a b name)
          ;; else
          (polymorphic-func a b name))))))

;; Standatd library
(defn +#2 [a b]
  (+ a b))
(defn *#2 [a b]
  (* a b))

;; Keep this at the end of this module because it overrides = in this module.
(defmacro = [a b]
  (eq a b))

