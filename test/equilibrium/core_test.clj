(ns equilibrium.core-test
  (:require [midje.sweet :refer :all]
            [equilibrium.core :as eq :refer [+#2 *#2]]))


;; # Variables

;; Variables are symbols that begin with a capital letter or an underscore.
(fact
 (eq/variable? 'Foo) => true
 (eq/variable? '_) => true
 (eq/variable? 'foo) => false)

;; # Constructors

;; The macro eq/data defines a constructor. Constructors are
;; self-evaluating functions, i.e., functions that evaluate to
;; themselves. The macro takes any number of forms, each consisting of
;; a name and example arguments.
(eq/data (list Val Next)
         (empty))

;; Each such form defines a Clojure function that returns the original
;; s-expr, with the symbol replaced with the canonical
;; namespace/name#arity format. The function name is derived from the
;; constructor, with `#` followed by the arity (number of arguments)
;; added as suffix.
(fact
 (list#2 1 (list#2 (inc 1) (empty#0))) =>
 '(equilibrium.core-test/list#2 1 (equilibrium.core-test/list#2 2 (equilibrium.core-test/empty#0))))

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
;; (a symbol starting with a capital letter or an underscore), the
;; equation defines a _uniform function_.

;; The Clojure function being defined receives a suffix that includes
;; a hash sign (`#`) followed by the function's arity (number of
;; arguments). This is to say that functions of the same name but
;; different arities are distinct.
(eq/= (f X) (+ X 2))
(fact
 (f#1 3) => 5)

;; ### Under the Hood

;; All functions (uniform functions included) are accompanied by two atoms:
;; - A _code_ atom (with the `-code` suffix), containing a vector of two elements -- the s-expressions on the two sides of the equation (canonicalized), and
;; - A _compiled_ atom (with the `-comp` suffix), containing a closure with the function definition.
(fact
 @f#1-code => '[(equilibrium.core-test/f#1 X) (equilibrium.core/+#2 X 2)]
 @f#1-comp => fn?
 (@f#1-comp 4) => 6)

;; The compiled function in the `-comp` atom is the only actual
;; implementation of the function. The base function (without the
;; `-comp` suffix) is merely a proxy. If the function in the atom gets
;; updated, the meaning of the function changes.
(fact
 (reset! f#1-comp (fn [X] (- X 2)))
 (f#1 3) => 1)

;; ## Polimorphic Functions

;; Polymorphic functions are defined across multiple equations, each
;; contributing a solution for the case where the first argument is of
;; a specific constructor.
(eq/= (sum (list V R)) (+ V (sum R)))
(eq/= (sum (empty)) 0)
(fact
 (sum#1 (list#2 1 (list#2 2 (empty#0)))) => 3)

;; ### Under the Hood

;; The `-code` and `-comp` atoms exist for polymorphic functions as
;; well, but this time, they contain maps. Instead of holding
;; expressions (`-code`) and closures (`-comp`), they hold maps for
;; which the keys are the canonical symbols generated by the different
;; constructors, and the values are either expressions or closures, as
;; appropriate.
(fact
 @sum#1-code => map?
 @sum#1-comp => map?
 (@sum#1-code 'equilibrium.core-test/list#2) => '[(equilibrium.core-test/sum#1 (equilibrium.core-test/list#2 V R))
                                                  (equilibrium.core/+#2 V (equilibrium.core-test/sum#1 R))]
 (@sum#1-comp 'equilibrium.core-test/list#2) => fn?)

;; # Abstract constructors

;; While Equilibrium resembles functional programming languages, it
;; does not have a concept of functions in the sense they exist, e.g.,
;; in Clojure. Instead, equations provide the meaning of expressions directly.

;; While a function does not exist as a concept, it can be
;; defined. Specifically, we can define closures by specifying how
;; they are applied.

;; For example, we can define the `apply` function, and define how
;; different "functions" are applied:
(eq/data (inc) (dec))
(eq/= (apply (inc) X) (+ X 1))
(eq/= (apply (dec) X) (+ X -1))

;; Now, we can apply these functions to values. This will behave as we expect.
(fact
 (apply#2 (inc#0) 2) => 3
 (apply#2 (dec#0) 2) => 1)

;; Here, `(inc)` and `(dec)` behave like true functions, in the sense
;; functions are given in functional programming. They are values, and
;; can be passed along to other functions. However, there is something
;; a bit awkward there. We had do define them through the eyes of the
;; `apply` function, and moreover, we needed to name them. This is
;; unlike lambda abstractions, which could have made these functions
;; anonimous. For example, instead of using `(inc)`, why couldn't we
;; use something like `(lambda N (+ N 1))`?

;; Well, we can. But to do so, we need to first define `lambda`, as an
;; `abstract` concept, and provide the equation(s) that define its meaning.
(eq/abstract (lambda X Y)
             [(apply (lambda X Y) X) Y])

;; The reason why we need `lambda` to be abstract, and not simple
;; `data`, is because we expect `X` to be bound to a free variable,
;; like `N` in the above example. This variable will be introduced at
;; the right-hand-side of an equation. Because Equilibrium focuses on
;; compiling its code to efficient Clojure code, new variables cannot
;; be introduced at the right-hand-side of an equation (the body of a
;; function), _unless they are introduced within an abstract concept_.

;; In the `abstract` form, we provide the new abstract form (`(lambda
;; X Y)`, in our case), and any number of equations that define its
;; meaning. In our case, we provided one equation (given as a 2-tuple)
;; defining how a `lambda` is to be applied. Note that `X` and `Y`
;; appear twice (each) in this equation. Having a variable apear more
;; than once means it shares a value. First, we share the parameter
;; value given to `apply` with the argument in `lambda`. Then, we bind
;; the expression defining the function's value to the value returned
;; by `apply`.

;; ### Under the Hood

;; Abstract concepts are represented as variables containing the
;; sequence of equations defined for them. The equations are
;; canonicalized to make them valid across namespaces.
(fact
 lambda#2 => ['[(equilibrium.core-test/apply#2 (equilibrium.core-test/lambda#2 X Y) X) Y]])

;; The abstract concept has a `:abstract` meta attribute to make it
;; easy to identify as abstract.
(fact
 (-> lambda#2 meta :abstract) => true)

;; The function `find-abstract-components` takes a canonical
;; expression and returns a sequence of indicies in which abstract
;; concepts are located within that expression.

;; If no abstract concepts are present, it returns an empty sequence.
(fact
 (eq/find-abstract-components (eq/canonicalize
                               '(eq/+ 1 2))) => [])

;; For each abstract concept, it returns a vector of indecies that
;; leads to it.
(fact
 (eq/find-abstract-components (eq/canonicalize
                               '(list (lambda N (eq/+ N 1))
                                      (list (lambda N (eq/+ N -1))
                                            (empty)))))
 => [[1] [2 1]])

;; The function `vars-in-expr` traverses an expression and returns a
;; set containing all the variables within that expression.
(fact
 (eq/vars-in-expr (eq/canonicalize
                   '(apply (lambda X Y) X))) => #{'X 'Y})

;; The function `external-vars` take an expression and a path to a
;; sub-expression. It returns the set of variables that appear both
;; inside and outside the sub-expression. In the following example,
;; the sub-expression is `(lambda X Y)`. It uses both X and Y, but Y
;; is not shared with the larger expression.
(fact
 (eq/external-vars (eq/canonicalize
                    '(apply (lambda X Y) X)) [1]) => #{'X})

;; The function `replace-abstract` replaces abstract concepts with newly-created concrete constructors. The constructors take 

;; # Under the Hood

;; ## canonical-symbol

;; The `canonical-symbol` function takes a form, and returns a
;; canonical symbol of the form `namespace/name#arity`, representing
;; its name and arity.
(fact
 (eq/canonical-symbol '(list 1 (empty))) => 'equilibrium.core-test/list#2)

;; If the sequence is not a proper form, i.e., does not start with a
;; symbol, an exception is thrown.
(fact
 (eq/canonical-symbol '(1 2 3)) => (throws #"Symbol expected at the beginning of a form. '1' found in .*"))

;; If a symbol cannot be resolved for that arity, an exception is thrown.
(fact
 (eq/canonical-symbol '(+ 1 2 3)) => (throws #"Symbol [+] cannot be resolved for arity 3 in .*"))

;; ## canonicalize

;; This function converts symbols in an s-expression to their
;; canonical form. In many cases, this will make the expression a
;; valid Clojure expression.

;; Literals are kept unchanged.
(fact
 (eq/canonicalize 3) => 3
 (eq/canonicalize "foo") => "foo")

;; In forms (sequences that begin with a symbol), a `#` followed by
;; the arity (number of args) is appended to the symbol. A full
;; namespace is extracted based on resolution.
(fact
 (eq/canonicalize '(+ 1 2)) => '(equilibrium.core/+#2 1 2))

;; canonicalize works recursively.
(fact
 (eq/canonicalize '(+ (* 1 2) 3)) => '(equilibrium.core/+#2 (equilibrium.core/*#2 1 2) 3))

;; ### Special forms

;; The `if` form translates to a Clojure `if` form.
(fact
 (eq/canonicalize '(if true (+ 1 2) 3)) => '(if true (equilibrium.core/+#2 1 2) 3))

;; ## lhs-to-clj

;; Unlike canonicalize, which translates right-hand-side expressions (i.e.,
;; values), lhs-to-clj translates left-hand-side patterns.

;; It operates on a sequence of arguments. If all are valid variables, they are returned as a Clojure vector.
(fact
 (eq/lhs-to-clj '(A B C)) => '[A B C])

;; Literals and non-variable symbols are replaced with dummy variables. Nested sequences are taken as vectors.
(fact
 (eq/lhs-to-clj '(1 "two" (three Four 5))) => '[$1 $2 [$3 Four $5]]
 (provided
  (rand-int 1000000000) =streams=> [1 2 3 5]))

;; ## Tail Recursion Elimination (TRE)

;; TRE is a common optimization in functional programming languages,
;; and is essential when recursion is used in place of loops. Without
;; TRE, the depth of recursion is limited to the depth of the
;; stack. TRE, however, converts tail recursion into loops, and
;; therefore allows them to be used without limitation.

;; For example, while the `sum` function defined above does not use a
;; tail recursion (the last operation it performs is `+`, which is
;; performed after the recursion is complete), The following
;; alternative definition does use tail recursion:
(eq/= (tre-sum (list V L) S) (tre-sum L (+ S V)))
(eq/= (tre-sum (empty) S) S)
(eq/= (tre-sum L) (tre-sum L 0))

;; The `tre` function takes an Equilibrium right-hand expression and a
;; canonical symbol representing the function this expression defines,
;; and returns a different expression.

;; If the top-level expression is a function-call, and the function is
;; not the given one, a `:return` tuple is returned, with the original
;; expression as the return value.
(fact
 (eq/tre '(+ V (sum R)) 'equilibrium.core-test/sum#1) => '(equilibrium.core/return (+ V (sum R))))

;; If the top-level is a call to the given function, a `:recur` tuple
;; is returned, with the arguments to call on the next iteration.
(fact
 (eq/tre '(tre-sum L (+ S V)) 'equilibrium.core-test/tre-sum#2) => '(equilibrium.core/recur [L (+ S V)]))

;; So by calling `tre-sum` we get the same result as we would for
;; `sum`, only that no recursion is involved.
(fact
 (tre-sum#1 (list#2 1 (list#2 2 (empty#0)))) => 3)
