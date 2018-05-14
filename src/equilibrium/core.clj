(ns equilibrium.core
  (:require [clojure.string :as str]
            [clojure.walk :as walk]
            [clojure.set :as set]
            [clojure.core.unify :as unify]))

(def ^:dynamic *curr-func* (atom #{}))
(def ^:dynamic *defs*)
(def ^:dynamic *eq-id* nil)
(def dbg-inject-uuids (atom (list)))

(defn uuid []
  (if (empty? @dbg-inject-uuids)
    (apply str (for [i (range 12)]
                 (rand-nth "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789")))
    ;; else
    (let [id (first @dbg-inject-uuids)]
      (swap! dbg-inject-uuids rest)
      id)))

(defmacro data [& forms]
  `(do
     ~@(for [[ctor & args] forms]
         (let [funcname (symbol (str (name ctor) "#" (count args)))]
           `(defn ~funcname [~@args]
              (list '~(symbol (str *ns*) (str ctor "#" (count args))) ~@args))))))

(defn variable? [x]
  (and (symbol? x)
       (or (Character/isUpperCase (first (name x)))
           (= (first (name x)) \_))))

(def unifier (unify/make-unifier-fn variable?))
(def unify (unify/make-unify-fn variable?))

(defn canonical-symbol [form]
  (let [[sym & args] form]
    (when-not (symbol? sym)
      (throw (Exception. (str "Symbol expected at the beginning of a form. '" (pr-str sym) "' found in " (meta form)))))
    (if (= sym 'if)
      sym
      ;; else
      (let [sym-name (-> sym name (str/split #"#") (get 0))
            arity (count args)
            name-arity (str sym-name "#" arity)
            sym' (symbol (namespace sym) name-arity)
            ns (-> sym' resolve meta :ns)]
        (if (and (or (= (namespace sym') (str *ns*))
                     (nil? (namespace sym')))
                 (@*curr-func* (symbol name-arity)))
          (symbol (str *ns*) name-arity)
          ;; else
          (do
            (when (nil? ns)
              (throw (Exception. (str "Symbol " sym-name " cannot be resolved for arity " arity " in " (meta form)))))
            (symbol (str ns) name-arity)))))))

(declare canonicalize)

(defn- form-canonicalize [form]
  (let [[sym & args] form]
    (cond
      (= sym 'if) (cons 'if (map canonicalize args))
      :else
      (cons (canonical-symbol form) (doall (map canonicalize args))))))

(defn- var-canonicalize [x]
  (if (or (nil? *eq-id*)
          (re-find #"[?]" (name x)))
    x
    ;; else
    (symbol (str (name x) "?" *eq-id*))))

(defn canonicalize [x]
  (cond (seq? x) (with-meta (form-canonicalize x) (meta x))
        :else x))

(defn lhs-to-clj [pattern]
  (cond
    (seq? pattern) (vec (map lhs-to-clj pattern))
    (variable? pattern) pattern
    :else
    (symbol (str "$" (uuid)))))
(defn trace [x]
  (prn x)
  x)

(defn tre [expr sym]
  (cond
    (and (seq? expr) (= (canonical-symbol expr) sym)) (list 'equilibrium.core/recur (vec (rest expr)))
    (and (seq? expr) (= (first expr) 'if)) (let [[if' cond then else] expr]
                                             (list if' cond (tre then sym) (tre else sym)))
    :else (list 'equilibrium.core/return expr)))

(data (return ?val)
      (recur ?args))

(defn- uniform-func [a b name]
  `(do
     (def ~(name "-code") (atom '~[a b]))
     (def ~(name "-comp") (atom (fn [~@(lhs-to-clj (rest a))] ~b)))
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
       (swap! ~(name "-code") assoc '~(-> a second canonicalize first) '~[(canonicalize a) (canonicalize b)])
       (swap! ~(name "-comp") assoc '~(-> a second canonicalize first)
              (fn ~(lhs-to-clj (rest a))
                ~(-> b (tre (canonical-symbol a)) canonicalize))))))

(defn- eq [a b]
  (if (symbol? a)
        `(def ~a ~b)
        ;; else
        (let [func-name-arity (str (-> a first name) "#" (count (rest a)))]
          (binding [*eq-id* (uuid)
                    *curr-func* (atom #{(symbol func-name-arity)})]
            (let [a (canonicalize a)
                  b (canonicalize b)]
              (let [name (fn [suff]
                           (symbol (str (-> a first name) suff)))]
                (if (variable? (second a))
                  (uniform-func a b name)
                  ;; else
                  (polymorphic-func a b name))))))))

(defmacro abstract [form & eqs]
  (let [[sym & args] form]
    `(def ~(symbol (str sym "#" (count args)))
       (with-meta '~(for [[a b] eqs]
                      [(canonicalize a) (canonicalize b)])
         {:abstract true}))))

(defn find-abstract-components
  ([expr] (find-abstract-components expr []))
  ([expr addr]
   (cond
     (not (seq? expr)) []
     (let [sym (first expr)]
       (and (resolve sym) (-> sym resolve deref meta :abstract))) [addr]
     :else (mapcat (fn [[i elem]]
                     (find-abstract-components elem (conj addr i)))
                   (map-indexed vector expr)))))

(defn vars-in-expr [expr]
  (walk/postwalk (fn [x]
                   (cond
                     (variable? x) #{x}
                     (seq? x) (apply set/union x)
                     :else #{})) expr))

 (defn- at-path [expr path]
   (if (empty? path)
     expr
     ;; else
     (recur (nth expr (first path)) (rest path))))
 
 (defn- update-at-nth [seq n val]
   (if (> n 0)
     (cons (first seq) (update-at-nth (rest seq) (dec n) val))
     ;; else
     (cons val (rest seq))))
 
 (defn- set-at-path [expr path subexpr]
   (if (empty? path)
     subexpr
     ;; else
     (let [subexpr (nth expr (first path))]
       (update-at-nth expr (first path) (set-at-path subexpr (rest path))))))

(defn replace-abstract [[lhs rhs]]
  (loop [rhs rhs
         abstracts (find-abstract-components rhs)]
    (if (empty? abstracts)
      [lhs rhs]
      ;; else
      (let [path (first abstracts)
            subexpr (at-path rhs path)
            ctor-name (-> subexpr first name (str/split #"#") (get 0))
            new-ctor (symbol (str ctor-name "-" (uuid)))
            vars (set/intersection (vars-in-expr subexpr) (vars-in-expr lhs))
            new-subexpr (cons new-ctor vars)
            new-subexpr-canon (canonicalize new-subexpr)]
        (comment (swap! *curr-func* conj (symbol (str new-ctor "#" (count vars)))))
        (swap! *defs* conj `(data ~new-subexpr))
        (recur (set-at-path rhs path new-subexpr-canon) (rest abstracts))))))

(defn scope-vars [expr]
  (let [id (uuid)]
    (walk/postwalk #(if (= % '_)
                      (symbol (str "_?" (uuid)))
                      ;; else
                      (if (and (variable? %)
                               (not (re-find #"[?]" (name %))))
                        (symbol (str (name %) "?" id))
                        ;; else
                        %)) expr)))

(defn complete-term-to-match [subterm path term]
  (if (empty? path)
    subterm
    ;; else
    (let [index (first path)
          elems (for [i (range (count term))]
                  (if (= i index)
                    (complete-term-to-match subterm (rest path) (nth term index))
                    ;; else
                    '_))]
      (cond
        (vector? term) (vec elems)
        :else elems))))

(defn unify-subterm [term subterm path]
  (let [term' (complete-term-to-match subterm path term)
        term (scope-vars term)
        term' (scope-vars term')]
    (if (nil? (unify term term'))
      nil
      ;; else
      (unifier term term'))))

;; Standatd library
(defn +#2 [a b]
  (+ a b))
(defn *#2 [a b]
  (* a b))

;; Keep this at the end of this module because it overrides = in this module.
(defmacro = [a b]
  (eq a b))


