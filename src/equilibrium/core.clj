(ns equilibrium.core
  (:require [clojure.string :as str]
            [clojure.walk :as walk]
            [clojure.set :as set]
            [clojure.core.unify :as unify]))

(def ^:dynamic *trace-depth* 0)

(defmacro trace [x]
  `(do
     (apply print (for [i# (range *trace-depth*)]
                    "  "))
     (pr '~x)
     (println " =>")
     (let [x# (binding [*trace-depth* (inc *trace-depth*)]
                ~x)]
       (apply print (for [i# (range *trace-depth*)]
                      "  "))
       (print "=> ")
       (prn x#)
       x#)))

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
(def subst (unify/make-subst-fn variable?))

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
        (map? x) (into {} (for [[k v] x]
                            [(canonicalize k) (canonicalize v)]))
        (vector? x) (vec (map canonicalize x))
        (set? x) (set (map canonicalize x))
        :else x))

(defn lhs-to-clj [pattern]
  (cond
    (seq? pattern) (vec (map lhs-to-clj pattern))
    (variable? pattern) pattern
    :else
    (symbol (str "$" (uuid)))))


(defn tre [expr sym]
  (cond
    (and (seq? expr) (= (canonical-symbol expr) sym)) (list 'equilibrium.core/recur#1 (vec (rest expr)))
    (and (seq? expr) (= (first expr) 'if)) (let [[if' cond then else] expr]
                                             (list if' cond (tre then sym) (tre else sym)))
    :else (list 'equilibrium.core/return#1 expr)))

(defn saturate [expr]
  (walk/postwalk #(if (variable? %)
                    (symbol (str "!SAT!" (name %)))
                    ;; else
                    %) expr))

(defn- saturated? [sym]
  (and (symbol? sym)
       (str/starts-with? (name sym) "!SAT!")))

(defn unsaturate [expr]
  (walk/prewalk  #(if (saturated? %)
                    (symbol (subs (name %) 5))
                    ;; else
                    %) expr))

(declare partial-eval)

(defn- partial-eval-call [form]
  (let [[f & args] form
        pairs (map partial-eval args)
        form (cons f (for [[expr const] pairs]
                       expr))
        const (every? second pairs)
        code-sym (symbol (namespace f) (str (name f) "-code"))
        code-var (resolve code-sym)]
    (if const
      [(eval form) true]
      ;; else
      (if (nil? code-var)
        [form const]
        ;; else
        (let [code @@code-var
              equation (cond
                         (vector? code) code
                         (and (seq? (second form))
                              (map? code)) (code (-> form second first))
                         :else nil)]
          (if (nil? equation)
            [form const]
            ;; else
            (let [[lhs rhs] equation
                  binds (unify lhs form)]
              (partial-eval (subst rhs binds)))))))))

(defn- partial-eval-if [[_if cond then else]]
  (let [[cond known] (partial-eval cond)]
    (if known
      (if cond
        (partial-eval then)
        ;; else
        (partial-eval else))
      ;; else
      `[(if ~cond ~then ~else) false])))

(defn partial-eval [expr]
  (cond
    (seq? expr) (if (= (first expr) 'if)
                  (partial-eval-if expr)
                  ;; else
                  (partial-eval-call expr))
    (vector? expr) (let [pairs (map partial-eval expr)]
                     [(vec (map first pairs)) (every? second pairs)])
    (set? expr) (let [pairs (map partial-eval expr)]
                     [(set (map first pairs)) (every? second pairs)])
    (map? expr) (let [quads (for [[k v] expr]
                              [(partial-eval k) (partial-eval v)])
                      expr (into {} (for [[[k kc] [v vc]] quads]
                                      [k v]))
                      const (every? second (for [q quads
                                                 x q] x))]
                  [expr const])
    (and (symbol? expr)
         (not (nil? (resolve expr)))) [@(resolve expr) true]
    :else [expr (not (saturated? expr))]))

(defn compile [[lhs rhs]]
  (let [rhs (-> rhs saturate partial-eval first unsaturate)]
    [[lhs rhs] `(fn ~(lhs-to-clj (rest lhs)) ~(tre rhs (first lhs)))]))

(defn jit [eq set-eq set-fn]
  (let [[eq func] (compile eq)
        func (eval func)]
    (fn [& args]
      (set-eq eq)
      (set-fn func)
      (apply func args))))

(data (return ?val)
      (recur ?args))

(defn- uniform-func [a b name]
  (let [dummy-args (vec (for [i (range (count (rest a)))]
                              (symbol (str "$" i))))]
    `(do
       (declare ~(name ""))
       (def ~(name "-code") (atom '~[a b]))
       (def ~(name "-comp") (atom (jit '~[a b]
                                       (partial reset! ~(name "-code"))
                                       (partial reset! ~(name "-comp")))))
       (defn ~(name "") [~@(rest a)]
         (let [[op# val#] ~(cons `(deref ~(name "-comp")) (rest a))]
           (cond
             (= op# 'equilibrium.core/return#1) val#
             (= op# 'equilibrium.core/recur#1)
             (let [~dummy-args val#]
               (recur ~@dummy-args))))))))

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
       (swap! ~(name "-code") assoc '~(-> a second canonicalize first) '~[a b])
       (swap! ~(name "-comp") assoc '~(-> a second canonicalize first)
              (jit '~[a b]
                   (partial swap! ~(name "-code") assoc '~(-> a second canonicalize first))
                   (partial swap! ~(name "-comp") assoc '~(-> a second canonicalize first)))))))


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
                     (sequential? x) (apply set/union x)
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
     (let [expr' (nth expr (first path))]
       (update-at-nth expr (first path) (set-at-path expr' (rest path) subexpr)))))

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
        term' (scope-vars term')
        bindings (unify term term')]
    (if (nil? bindings)
      nil
      ;; else
      (let [bindings (unify/flatten-bindings bindings)]
        (subst term' bindings)))))

(defn enumerate-vars [term]
  (let [vars (vars-in-expr term)
        varmap (into {} (for [[i var] (map-indexed vector vars)]
                          [var (symbol (str "V" (inc i)))]))]
    (walk/postwalk-replace varmap term)))

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
            ctor-def (resolve (first subexpr))
            equations @ctor-def]
        (swap! *curr-func* conj (symbol (str (name new-ctor) "#" (count vars))))
        (let [new-subexpr-canon (canonicalize new-subexpr)]
          (swap! *defs* conj `(data ~new-subexpr))
          (doseq [equation equations]
            (let [[subexpr new-subexpr] (scope-vars [subexpr new-subexpr])
                  [lhs' rhs'] (unify-subterm equation subexpr [0 1])
                  lhs' (set-at-path lhs' [1] new-subexpr)
                  [lhs' rhs'] (enumerate-vars [lhs' rhs'])]
              (swap! *defs* conj (list 'equilibrium.core/= lhs' rhs'))))
          (recur (set-at-path rhs path new-subexpr-canon) (rest abstracts)))))))

(defn- curr-func [a]
  (if (symbol? a)
    #{}
    ;; else
    (let [func-name-arity (str (-> a first name) "#" (count (rest a)))]
      #{(symbol func-name-arity)})))

(defn- eq [a b]
  (binding [*eq-id* (uuid)
            *curr-func* (atom (curr-func a))]
    (when-not (seq? a)
      (throw (Exception. (str "The left-hand-side of an equation needs to be a form. Found: " a))))
    (let [b (canonicalize b)
          defs (atom [])
          [a b] (binding [*defs* defs]
                  (replace-abstract [a b]))]
      `(do
         ~@ @defs
        ~(let [a (canonicalize a)]
           (let [name (fn [suff]
                        (symbol (str (-> a first name) suff)))]
             (if (or (= (count a) 1)
                     (variable? (second a)))
               (uniform-func a b name)
               ;; else
               (polymorphic-func a b name))))))))

;; Standatd library
(defn +#2 [a b]
  (+ a b))
(defn *#2 [a b]
  (* a b))
(defn <#2 [a b]
  (< a b))

;; Keep this at the end of this module because it overrides = in this module.
(defmacro = [a b]
  (eq a b))



