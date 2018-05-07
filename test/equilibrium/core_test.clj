(ns equilibrium.core-test
  (:require [midje.sweet :refer :all]
            [equilibrium.core :as eq]))


;; # Constructors

;; The macro eq/data defines a constructor. Constructors are
;; self-evaluating functions, i.e., functions that evaluate to
;; themselves. The macro takes any number of forms, each consisting of
;; a name and example arguments.
(eq/data (lst ?val ?next)
         (empty))

;; Each such form defines a Clojure function that returns the original
;; s-expr (modulo the arguments, which are given as values). The
;; function name is derived from the constructor, with `#` followed by
;; the arity (number of arguments) added as suffix.
(fact
 (lst#2 1 (lst#2 (inc 1) (empty#0))) => '(lst 1 (lst 2 (empty))))

;; ### Under the Hood The expression returned by the constructor holds
;; a `:ctor` meta-field, that uniquely identifies the constructor that
;; created it.
(fact
 (-> (lst#2 1 (empty#0)) meta :ctor) => "equilibrium.core-test/lst#2")


;; # Equations
;; Equations are defined using the eq/= form.

;; ## Constants

;; When the left-hand-side of an equation is a symbol, the equation
;; defines this symbol, similar to a Clojure def.
(eq/= x 2)
(fact
 x => 2)

;; ## Uniform Functions

;; When the left-hand-side is a form, a function of the same name is
;; being defined. When the first argument to that form is a variable
;; (a symbol starting with `?`), the equation defines a _uniform
;; function_.

;; The Clojure function being defined receives a suffix that includes
;; a hash sign (`#`) followed by the function's arity (number of
;; arguments). This is to say that functions of the same name but
;; different arities are distinct.
(eq/= (f ?x) (+ ?x 2))
(fact
 (f#1 3) => 5)

;; ### Under the Hood

;; All functions (uniform functions included) are accompanied by two atoms:
;; - A _code_ atom (with the `-code` suffix), containing a vector of two elements -- the s-expressions on the two sides of the equation, and
;; - A _compiled_ atom (with the `-comp` suffix), containing a closure with the function definition.
(fact
 @f#1-code => '[(f ?x) (+ ?x 2)]
 @f#1-comp => fn?
 (@f#1-comp 4) => 6)

;; The compiled function in the `-comp` atom is the only actual
;; implementation of the function. The base function (without the
;; `-comp` suffix) is merely a proxy. If the function in the atom gets
;; updated, the meaning of the function changes.
(fact
 (reset! f#1-comp (fn [?x] (- ?x 2)))
 (f#1 3) => 1)

;; ## Polimorphic Functions

;; Polymorphic functions are defined across multiple equations, each
;; contributing a solution for the case where the first argument is of
;; a specific constructor.
(eq/= (sum (lst ?v ?r)) (+ ?v (sum ?r)))
(eq/= (sum (empty)) 0)
(comment (fact
          (sum#1 (lst#2 1 (lst#2 2 (empty#0)))) => 3))

;; ### Under the Hood

;; The `-code` and `-comp` atoms exist for polymorphic functions as
;; well, but this time, they contain maps. Instead of holding
;; expressions (`-code`) and closures (`-comp`), they hold maps for
;; which the keys are strings corresponding to the `:ctor` meta-fields
;; of the different constructors, and the values are either
;; expressions or closures, as appropriate.
(fact
 @sum#1-code => map?
 @sum#1-comp => map?
 (@sum#1-code "equilibrium.core-test/lst#2") => '[(sum (lst ?v ?r)) (+ ?v (sum ?r))]
 (@sum#1-comp "equilibrium.core-test/lst#2") => fn?)

