```clojure
(ns equilibrium.core-test
  (:require [midje.sweet :refer :all]
            [equilibrium.core :as eq :refer [+#2 *#2 <#2]]))


```
# Variables

Variables are symbols that begin with a capital letter or an underscore.
```clojure
(fact
 (eq/variable? 'Foo) => true
 (eq/variable? '_) => true
 (eq/variable? '_foo) => true
 (eq/variable? 'foo) => false)

```
# Constructors

The macro eq/data defines a constructor. Constructors are
self-evaluating functions, i.e., functions that evaluate to
themselves. The macro takes any number of forms, each consisting of
a name and example arguments.
```clojure
(eq/data (list Val Next)
         (empty))

```
Each such form defines a Clojure function that returns the original
s-expr, with the symbol replaced with the canonical
namespace/name#arity format. The function name is derived from the
constructor, with `#` followed by the arity (number of arguments)
added as suffix.
```clojure
(fact
 (list#2 1 (list#2 (inc 1) (empty#0))) =>
 '(equilibrium.core-test/list#2 1 (equilibrium.core-test/list#2 2 (equilibrium.core-test/empty#0))))

```
# Equations

Equations are defined using the eq/= form. Equations define
_functions_, which, like Clojure functions are enclosed in a
list. Unlike Clojure, in which functions are defined using special
forms, in Equilibrium, functions are defined using equations, where
an "invocation" of the function appears on the left-hand-side, and
its meaning appears on the right-hand side.

## Constants

Functions may take zero or more arguments. The number of arguments
is considered the function's arity. Functions with arity of zero
are considered constants.

For example, the following equation defines the constant `x` to be
2.
```clojure
(eq/= (x) 2)

```
Equilibrium functions can be called from Clojure by adding their
arity to their name, delimited by a `#`.
```clojure
(fact
 (x#0) => 2)

```
## Uniform Functions

When the left-hand-side is a form, a function of the same name is
being defined. When the first argument to that form is a variable
(a symbol starting with a capital letter or an underscore), the
equation defines a _uniform function_.

The Clojure function being defined receives a suffix that includes
a hash sign (`#`) followed by the function's arity (number of
arguments). This is to say that functions of the same name but
different arities are distinct.
```clojure
(reset! eq/dbg-inject-uuids ["my-eqid"]) ;; Inject an ID for this equation
(eq/= (f X) (+ X 2))
(fact
 (f#1 3) => 5)

```
A uniform function can be recursive
```clojure
(eq/= (range A B) (if (< A B)
                    (list A (range (+ A 1) B))
                    ;; else
                    (empty)))
(fact
 (range#2 1 3) => (eq/canonicalize '(list 1 (list 2 (empty)))))

```
### Under the Hood

All functions (uniform functions included) are accompanied by two atoms:
- A _code_ atom (with the `-code` suffix), containing a vector of two elements -- the s-expressions on the two sides of the equation (canonicalized), and
- A _compiled_ atom (with the `-comp` suffix), containing a closure with the function definition.
```clojure
(fact
 @f#1-code => '[(equilibrium.core-test/f#1 X) (equilibrium.core/+#2 X 2)]
 @f#1-comp => fn?
 (@f#1-comp 4) => '(equilibrium.core/return#1 6))

```
The compiled function in the `-comp` atom is the only actual
implementation of the function. The base function (without the
`-comp` suffix) is merely a proxy. If the function in the atom gets
updated, the meaning of the function changes.
```clojure
(fact
 (reset! f#1-comp (fn [X] (eq/return#1 (- X 2))))
 (f#1 3) => 1)

```
## Polimorphic Functions

Polymorphic functions are defined across multiple equations, each
contributing a solution for the case where the first argument is of
a specific constructor.
```clojure
(reset! eq/dbg-inject-uuids ["eqid1" "eqid2"]) ;; Inject an ID for this equation
(eq/= (sum (list V R)) (+ V (sum R)))
(eq/= (sum (empty)) 0)
(fact
 (sum#1 (list#2 1 (list#2 2 (empty#0)))) => 3)

```
### Under the Hood

The `-code` and `-comp` atoms exist for polymorphic functions as
well, but this time, they contain maps. Instead of holding
expressions (`-code`) and closures (`-comp`), they hold maps for
which the keys are the canonical symbols generated by the different
constructors, and the values are either expressions or closures, as
appropriate.
```clojure
(fact
 @sum#1-code => map?
 @sum#1-comp => map?
 (@sum#1-code 'equilibrium.core-test/list#2)
 => '[(equilibrium.core-test/sum#1 (equilibrium.core-test/list#2 V R))
      (equilibrium.core/+#2 V (equilibrium.core-test/sum#1 R))]
 (@sum#1-comp 'equilibrium.core-test/list#2) => fn?)

```
# Abstract Constructors

While Equilibrium resembles functional programming languages, it
does not have a concept of functions in the sense they exist, e.g.,
in Clojure. Instead, equations provide the meaning of expressions directly.

While a function does not exist as a concept, it can be
defined. Specifically, we can define closures by specifying how
they are applied.

For example, we can define the `apply` function, and define how
different "functions" are applied:
```clojure
(eq/data (inc) (dec))
(eq/= (apply (inc) X) (+ X 1))
(eq/= (apply (dec) X) (+ X -1))

```
Now, we can apply these functions to values. This will behave as we expect.
```clojure
(fact
 (apply#2 (inc#0) 2) => 3
 (apply#2 (dec#0) 2) => 1)

```
Here, `(inc)` and `(dec)` behave like true functions, in the sense
functions are given in functional programming. They are values, and
can be passed along to other functions. However, there is something
a bit awkward there. We had do define them through the eyes of the
`apply` function, and moreover, we needed to name them. This is
unlike lambda abstractions, which could have made these functions
anonimous. For example, instead of using `(inc)`, why couldn't we
use something like `(lambda N (+ N 1))`?

Well, we can. But to do so, we need to first define `lambda`, as an
`abstract` concept, and provide the equation(s) that define its meaning.
```clojure
(eq/abstract (lambda X Y)
             [(apply (lambda X Y) X) Y])

```
The reason why we need `lambda` to be abstract, and not simple
`data`, is because we expect `X` to be bound to a free variable,
like `N` in the above example. This variable will be introduced at
the right-hand-side of an equation. Because Equilibrium focuses on
compiling its code to efficient Clojure code, new variables cannot
be introduced at the right-hand-side of an equation (the body of a
function), _unless they are introduced within an abstract concept_.

In the `abstract` form, we provide the new abstract form (`(lambda
X Y)`, in our case), and any number of equations that define its
meaning. In our case, we provided one equation (given as a 2-tuple)
defining how a `lambda` is to be applied. Note that `X` and `Y`
appear twice (each) in this equation. Having a variable apear more
than once means it shares a value. First, we share the parameter
value given to `apply` with the argument in `lambda`. Then, we bind
the expression defining the function's value to the value returned
by `apply`.

For example, by defining the equation:
```clojure
(eq/= (adder N) (lambda X (+ X N)))
```
we actually define a higher-order function, so that if we define:
```clojure
(eq/= (my-inc) (adder 1))
```
`my-inc` becomes a function on which we can call `apply`, to add 1
to a number.
```clojure
(fact
 (apply#2 (my-inc#0) 3) => 4)

```
This can also be done directly:
```clojure
(eq/= (my-dec) (lambda X (+ X -1)))
(fact
 (apply#2 (my-dec#0) 5) => 4)


```
### Under the Hood

Abstract concepts are represented as variables containing the
sequence of equations defined for them. The equations are
canonicalized to make them valid across namespaces.
```clojure
(fact
 lambda#2 => ['[(equilibrium.core-test/apply#2 (equilibrium.core-test/lambda#2 X Y) X) Y]])

```
The abstract concept has a `:abstract` meta attribute to make it
easy to identify as abstract.
```clojure
(fact
 (-> lambda#2 meta :abstract) => true)

```
The function `find-abstract-components` takes a canonical
expression and returns a sequence of indicies in which abstract
concepts are located within that expression.

If no abstract concepts are present, it returns an empty sequence.
```clojure
(fact
 (eq/find-abstract-components (eq/canonicalize
                               '(eq/+ 1 2))) => [])

```
For each abstract concept, it returns a vector of indecies that
leads to it.
```clojure
(fact
 (eq/find-abstract-components (eq/canonicalize
                               '(list (lambda N (eq/+ N 1))
                                      (list (lambda N (eq/+ N -1))
                                            (empty)))))
 => [[1] [2 1]])

```
The function `vars-in-expr` traverses an expression and returns a
set containing all the variables within that expression.
```clojure
(fact
 (eq/vars-in-expr (eq/canonicalize
                   '(apply (lambda X Y) X))) => #{'X 'Y}
 (eq/vars-in-expr '[X Y [Z Y] X]) => #{'X 'Y 'Z})

```
The function `replace-abstract` takes an equation, and returns a
revised equation, where abstract concepts used on the
right-hand-side are removed, and replaced with newly-defined
concrete constructors. For equations that do not include abstract
concepts, the equation is returned unmodified.
```clojure
(fact
 (eq/replace-abstract '[(sum (empty)) 0]) => '[(sum (empty)) 0])

```
When abstract concepts exist, they are replaced by newly-defined
ones.
```clojure
(def defs (atom []))
(fact
 (reset! eq/dbg-inject-uuids (concat ["12345"] (map str (range 10))))
 (binding [eq/*defs* defs
           eq/*curr-func* (atom #{'adder#1})]
   (eq/replace-abstract [(eq/canonicalize '(adder N))
                         (eq/canonicalize '(lambda X (eq/+ X N)))])
   => '[(equilibrium.core-test/adder#1 N)
        (equilibrium.core-test/lambda-12345#1 N)]))

```
A definition of the new constructor, along with equations
defining its meaning according to the `abstract` definition are
appended to a `*defs*` atom, which is passed to this function as a
dynamic variable.
```clojure
(fact
 @defs => '[(equilibrium.core/data (lambda-12345 N))
            (equilibrium.core/= (equilibrium.core-test/apply#2 (lambda-12345 V1) V2) (equilibrium.core/+#2 V2 V1))])

```
# Under the Hood

## canonical-symbol

The `canonical-symbol` function takes a form, and returns a
canonical symbol of the form `namespace/name#arity`, representing
its name and arity.
```clojure
(fact
 (eq/canonical-symbol '(list 1 (empty))) => 'equilibrium.core-test/list#2)

```
If the sequence is not a proper form, i.e., does not start with a
symbol, an exception is thrown.
```clojure
(fact
 (eq/canonical-symbol '(1 2 3))
 => (throws #"Symbol expected at the beginning of a form. '1' found in .*"))

```
If a symbol cannot be resolved for that arity, an exception is thrown.
```clojure
(fact
 (eq/canonical-symbol '(+ 1 2 3))
 => (throws #"Symbol [+] cannot be resolved for arity 3 in .*"))

```
`canonical-symbol` ignores the arity already indicated in a
symbol. If the symbol at the beginning of the sequence already has
a `#arity` suffix, it is ignored.
```clojure
(fact
 (eq/canonical-symbol '(list#3 1 (empty#7))) => 'equilibrium.core-test/list#2)

```
## canonicalize

This function converts symbols in an s-expression to their
canonical form. In many cases, this will make the expression a
valid Clojure expression.

Literals are kept unchanged.
```clojure
(fact
 (eq/canonicalize 3) => 3
 (eq/canonicalize "foo") => "foo")

```
In forms (sequences that begin with a symbol), a `#` followed by
the arity (number of args) is appended to the symbol. A full
namespace is extracted based on resolution.
```clojure
(fact
 (eq/canonicalize '(+ 1 2)) => '(equilibrium.core/+#2 1 2))

```
`canonicalize` works recursively.
```clojure
(fact
 (eq/canonicalize '(+ (* 1 2) 3)) => '(equilibrium.core/+#2 (equilibrium.core/*#2 1 2) 3))

```
`canonicalize` can operate (and leave unchanged) canonical input.
```clojure
(fact
 (eq/canonicalize (eq/canonicalize '(+ (* 1 2) 3))) => (eq/canonicalize '(+ (* 1 2) 3)))

```
### Special forms

The `if` form translates to a Clojure `if` form.
```clojure
(fact
 (eq/canonicalize '(if true (+ 1 2) 3)) => '(if true (equilibrium.core/+#2 1 2) 3))

```
### Clojure Collections

`canonicalize` recurses through Clojure collections: vectors, maps
and sets.
```clojure
(fact
 (eq/canonicalize '{"one" 1 "two" (+ 1 1)})
 => '{"one" 1 "two" (equilibrium.core/+#2 1 1)}
 (eq/canonicalize '[(f X) (f Y)])
 => '[(equilibrium.core-test/f#1 X) (equilibrium.core-test/f#1 Y)]
 (eq/canonicalize '#{(f X) (f Y)})
 => '#{(equilibrium.core-test/f#1 X) (equilibrium.core-test/f#1 Y)})

```
## lhs-to-clj

Unlike canonicalize, which translates right-hand-side expressions (i.e.,
values), lhs-to-clj translates left-hand-side patterns.

It operates on a sequence of arguments. If all are valid variables, they are returned as a Clojure vector.
```clojure
(fact
 (eq/lhs-to-clj '(A B C)) => '[A B C])

```
Literals and non-variable symbols are replaced with dummy variables. Nested sequences are taken as vectors.
```clojure
(fact
 (eq/lhs-to-clj '(1 "two" (three Four 5))) => '[$1 $2 [$3 Four $5]]
 (provided
  (eq/uuid) =streams=> ["1" "2" "3" "5"]))

```
## Tail Recursion Elimination (TRE)

TRE is a common optimization in functional programming languages,
and is essential when recursion is used in place of loops. Without
TRE, the depth of recursion is limited to the depth of the
stack. TRE, however, converts tail recursion into loops, and
therefore allows them to be used without limitation.

For example, while the `sum` function defined above does not use a
tail recursion (the last operation it performs is `+`, which is
performed after the recursion is complete), The following
alternative definition does use tail recursion:
```clojure
(eq/= (tre-sum (list V L) S) (tre-sum L (+ S V)))
(eq/= (tre-sum (empty) S) S)
(eq/= (tre-sum L) (tre-sum L 0))

```
The `tre` function takes an Equilibrium right-hand expression and a
canonical symbol representing the function this expression defines,
and returns a different expression.

If the top-level expression is a function-call, and the function is
not the given one, a `:return` tuple is returned, with the original
expression as the return value.
```clojure
(fact
 (eq/tre '(+ V (sum R)) 'equilibrium.core-test/sum#1) => '(equilibrium.core/return#1 (+ V (sum R))))

```
If the top-level is a call to the given function, a `:recur` tuple
is returned, with the arguments to call on the next iteration.
```clojure
(fact
 (eq/tre '(tre-sum L (+ S V)) 'equilibrium.core-test/tre-sum#2) => '(equilibrium.core/recur#1 [L (+ S V)]))

```
So by calling `tre-sum` we get the same result as we would for
`sum`, only that no recursion is involved.
```clojure
(fact
 (tre-sum#1 (list#2 1 (list#2 2 (empty#0)))) => 3)

```
TRE handles `if` forms by recursing to both cases.
```clojure
(fact
 (eq/tre '(if X
            (sum L)
            ;; else
            Y) 'equilibrium.core-test/sum#1)
 => '(if X
       (equilibrium.core/recur#1 [L])
       ;; else
       (equilibrium.core/return#1 Y)))

```
## Unification

Unification of two terms is solving the equation of their
equality. The process involves finding values, that when assigned
to variables in either term, will make the terms equal.

### Scoping Variables

As a first step towards unification, variables in either term must
be made unique. This is because variables are scoped within a
single equation. For example, consider two different equations both
using variable `X`. Although named the same, each equation defines
a different variable `X`, since variables are scoped within a
single equation. An attempt to syntactically unify both equations
will result in considering `X` as a single variable, trying to
unify its value on both ends, leading to a wrong result. To avoid
that, we first pre-process each term (or equation), providing the
variables on each side a unique suffix, so that variables sharing a
name on both sides are not confused to be the same.

The function `scope-vars` augments a term by adding suffix to each
variable. The suffix is unique to that term.
```clojure
(fact
 (reset! eq/dbg-inject-uuids ["my-uuid"])
 (eq/scope-vars '[(apply [lambda X Y] X) Y])
 => '[(apply [lambda X?my-uuid Y?my-uuid] X?my-uuid) Y?my-uuid])

```
Variables already assigned a unique ID are left unchanged.
```clojure
(fact
 (reset! eq/dbg-inject-uuids ["my-uuid"])
 (eq/scope-vars '[(apply [lambda X Y] X) Y?foo])
 => '[(apply [lambda X?my-uuid Y?my-uuid] X?my-uuid) Y?foo])

```
Underscore (`_`) represents a free, singleton variable. Even if
multiple underscores appear in the same term, each will receive its
own unique ID.
```clojure
(fact
 (reset! eq/dbg-inject-uuids ["my-uuid", "foo" "bar"])
 (eq/scope-vars '[(apply [lambda X _] X) _])
 => '[(apply [lambda X?my-uuid _?foo] X?my-uuid) _?bar])

```
### Completion

We sometimes want to unify a sub-term to a complete term. Consider
the way applying a function works. We unify the left-hand-side of
an equation defining the function with the function application,
and replace it by the right-hand-side of the euqation under this
unification. To do this, we need a way to compare apples to apples,
that is, to complete the smaller term to match the larger one.

The function `complete-term-to-match` takes a smaller term, a path,
and a larger term.

For an empty path, the first term is returned.
```clojure
(fact
 (eq/complete-term-to-match '[(foo X Y) Y] [] '[(foo Y X) X]) => '[(foo X Y) Y])

```
Given a non-empty path, the function returns a term for which the
smaller term is located in that path. The returned term contains
unbound variables (`_`) to match the larger term.
```clojure
(fact
 (eq/complete-term-to-match '(foo N (+ N 1)) [0] '[(foo X Y) Y]) => '[(foo N (+ N 1)) _]
 (eq/complete-term-to-match '(+ N 1) [1] '[(foo X Y) Y]) => '[_ (+ N 1)]
 (eq/complete-term-to-match '(+ N 1) [0 2] '[(foo X Y) Y]) => '[(_ _ (+ N 1)) _])

```
`complete-term-to-match` preserves the difference between vectors
and sequences
```clojure
(fact
 (eq/complete-term-to-match 'X [1] '[foo bar baz]) => vector?
 (eq/complete-term-to-match 'X [1] '(foo bar baz)) => seq?)

```
Unification

The function `unify-subterm` takes a term, a subterm and a path in
the term with which the subterm is to be unified. It returns the
complete term with all variables assigned.
```clojure
(fact
 (reset! eq/dbg-inject-uuids ["foo" "bar" "baz"])
 (eq/unify-subterm '[(foo X Y) Y] '(foo N (+ N 1)) [0])
 => '[(foo N?bar (+ N?bar 1)) (+ N?bar 1)])

```
`unify-subterm` returns `nil` if the terms do not unify.
```clojure
(fact
 (reset! eq/dbg-inject-uuids ["foo" "bar" "baz"])
 (eq/unify-subterm '[(foo X Y) Y] '(bar N (+ N 1)) [0])
 => nil)

```
### Back to Normal

While not explicitly part of the unification process, the
unification process leaves variables _scoped_, that is, with the
`?` character embedded in them. This character will prevent these
variables to be scoped again, which is what we want if we wish to
go on unifying the term with other terms. However, if we wish to
generate a new equation out of the new term, we need to change all
variables in the new equation into un-scoped ones.

The `enumerate-vars` function takes a term (s-expression) as input,
and returns an equivalent term, with _enumerated variables_, that
is, the variables `V1`, `V2`, `V3`, etc.
```clojure
(fact
 (let [term '[(foo X Y) (bar [Y X])]
       newterm (eq/enumerate-vars term)]
   (eq/unify term newterm) =not=> nil?
   (eq/vars-in-expr newterm) => #{'V1 'V2}))

```
## Partial Evaluation

Partial evaluation is a symbolic computation that takes place at
compile time. It starts with an expression that includes some
variables (unknowns), and results in another expression, where all
the computation that can be applied at that time is being
applied. This includes replacing references to functions with their
respective bodies (_inlining_), and calling functions for which all
arguments are known.

### Saturation

A first, important step in performing partial evaluation in
Equilibrium is _saturating_ all variables in the original
expression. Saturation is acheived using the `saturate` function.

Expressions that do not contain variables are trivially saturated.
```clojure
(fact
 (eq/saturate '(foo bar 3 4)) => '(foo bar 3 4))

```
Saturating a variable involves replacing it with a symbol that is
_not_ a variable, but maps uniquely to it. We perform this by
prepending the string `!SAT!` to the variable symbol.
```clojure
(fact
 (eq/saturate 'Foo) => '!SAT!Foo)

```
Expressions that contain variables are transformed so that the
variables are replaced, but the rest of the expression is
unchanged.
```clojure
(fact
 (eq/saturate '(foo bar X Y)) => '(foo bar !SAT!X !SAT!Y))

```
The `unsaturate` function replaces saturated variables back to the
original variable symbols.
```clojure
(fact
 (eq/unsaturate '(foo bar 3 4)) => '(foo bar 3 4)
 (eq/unsaturate '!SAT!Foo) => 'Foo
 (eq/unsaturate '(foo bar !SAT!X !SAT!Y)) => '(foo bar X Y))

```
### Primitives

The function `partial-eval` partially-evaluates a saturated,
canonical expression. It returns the evaluated expression and a
Boolean indicating if the value is a constant.

Primitives (numbers, strings, keywords, symbols, etc) are
partially-evaluated to themselves.
```clojure
(fact
 (eq/partial-eval 123) => [123 true]
 (eq/partial-eval "foo") => ["foo" true]
 (eq/partial-eval 'foo) => '[foo true]
 ;; Saturated variables are not constants
 (eq/partial-eval '!SAT!Foo) => '[!SAT!Foo false])

```
For the purpose of the rest of this discussion, we define the
function `cs`, which canonicalizes and then saturates an
expression:
```clojure
(defn- cs [expr]
  (-> expr eq/canonicalize eq/saturate))

```
### Uniform Functions

When invoking a uniform function, it is certain that the body of
the function (the equation's right-hand-side) will be evaluated. It
is therefore safe to replace the head with the function's body,
with parameters replaced with argument values.
```clojure
(fact
 (eq/partial-eval (cs '(f X)))
 => [(cs '(+ X 2)) false])

```
`partial-eval` is applied recursively to arguments.
```clojure
(fact
 (eq/partial-eval (cs '(f (f X))))
 => [(cs '(+ (+ X 2) 2)) false])

```
Partial evaluation operates recursively also on the right-hand-side
expression. Consider the function `g` defined as follows:
```clojure
(eq/= (g X) (f (f X)))

```
By evaluating `g` we get an invocation of `f`. Since we know `f` is
to be invoked subsequently, we can replace it as well, and get the
final form.
```clojure
(fact
 (eq/partial-eval (cs '(g X)))
 => [(cs '(+ (+ X 2) 2)) false])

```
### Constructors and Builtins

Constructors and Builtins are evaluated to themselves, but the
arguments are being evaluated recursively.
```clojure
(fact
 (eq/partial-eval (cs '(list (f X) (empty))))
 => [(cs '(list (+ X 2) (empty))) false])

```
### Polymorphic Functions

Inlining a polymorphic function requires knowledge of which of its
equations is to be invoked. This is known, if the first argument to
the function is a data form matching one of the equations. For
example, the `sum` function can be inlined if it is known that the
argument is either a `list` or `empty`.
```clojure
(fact
 (eq/partial-eval (cs '(sum (list A (list B (empty))))))
 => [(cs '(+ A (+ B 0))) false])

```
If the first argument to a function is not a sequence (e.g., a
saturated variable), inlining does not take place.
```clojure
(fact
 (eq/partial-eval (cs '(sum L))) => [(cs '(sum L)) false])

```
### Constant Propagation

A _constant expression_ is one that does not contain (saturated)
variables. Constant expressions can be computed ahead of time to
the level of a value.
```clojure
(fact
 (eq/partial-eval (cs '(+ 2 3))) => [5 true]
 (eq/partial-eval (cs '(sum (range 1 10)))) => [45 true])

```
### Variables

Symbols that are not saturated variables can be taken as Clojure
variables. if they are, we can replace them by their values.
```clojure
(fact
 (eq/partial-eval (cs '(x))) => [2 true])

```
### Conditionals

The `if` form requires special treatment. If we were to inline both
_then_ and _else_ branches of the `if` form, we would never
terminate in cases where `if` is used to check for termination
conditions in a recursion.

If the condition is known is a constant, the `if` form
reduces to one of its branches.
```clojure
(fact
 (eq/partial-eval (cs '(if (< 1 2) (f X) (g X))))
 => [(cs '(+ X 2)) false]
 (eq/partial-eval (cs '(if (< 2 1) (f X) (g X))))
 => [(cs '(+ (+ X 2) 2)) false])

```
If the condition is not a constant, Only the condition is being
partially evaluated. the two branches are left unchanged. This is
to avoid a situation when partial-evaluation of a terminating
program does not terminate.
```clojure
(fact
 (eq/partial-eval (cs '(if (< (f X) 3) (f X) (g X))))
 => [(cs '(if (< (+ X 2) 3) (f X) (g X))) false])

```
### Clojure Collections

Partial evaluation operates on Clojure collections by evaluating
their respective members.
```clojure
(fact
 (eq/partial-eval (cs '[1 2 3]))
 => [(cs '[1 2 3]) true]
 (eq/partial-eval (cs '[(f X) (g X)]))
 => [(cs '[(+ X 2) (+ (+ X 2) 2)]) false]
 (eq/partial-eval (cs '{1 2}))
 => [(cs '{1 2}) true]
 (eq/partial-eval (cs '{(f X) (g X)}))
 => [(cs '{(+ X 2) (+ (+ X 2) 2)}) false]
 (eq/partial-eval (cs '#{1 2 3}))
 => [(cs '#{1 2 3}) true]
 (eq/partial-eval (cs '#{(f X) (g X)}))
 => [(cs '#{(+ X 2) (+ (+ X 2) 2)}) false])

```
## Just-In-Time Compilation

### Compilation

Compiling an equation includes two steps:
1. Partial evaluation of the equation itself, and
2. Compiling the equation into a Clojure function.

The `compile` function takes a canonical, normalized equation as
input, and returns a pair `[[lhs rhs] func]`, where `lhs` and `rhs`
are the left- and right-hand sides of the partially-evaluated
equation, and `func` is an s-expression containing the Clojure
definition of a function corresponding to the equation.
```clojure
(fact
 (binding [eq/*curr-func* (atom #{'foo#1})]
   (let [[eq func] (eq/compile (eq/canonicalize '[(foo X) (sum (list X (list X (empty))))]))
         func' (eval func)]
     eq => (eq/canonicalize '[(foo X) (+ X (+ X 0))])
     (func' 3) => (equilibrium.core/return#1 6))))

```
### JIT

A Just-In-Time (JIT) compiler works by compiling code only when it
needs to run. Sometimes, as in the JVM, the JIT is invoked on a
function only after several invocations of that function to save
up-front compilation time. In the case of Equilibrium, however,
compilation is performed on the first invocation of a function.

We perform JIT compilation to make sure all the definitions
generated by the macros are already in place before we begin. This
goes, for example, for constructors that are defined by the `=`
macro to replace the use of abstract concepts.

The `jit` function takes three parameters:
1. `eq`, the (canonical) equation to compile,
2. `set-eq`, a closure to update the equation, after being partially-evaluated, and
3. `set-fn`, a closure to upate the function, replacing it with the compiled version.

`jit` returns a function that behaves like the generated one, that
is, an implementation of the equation.
```clojure
(fact
 (binding [eq/*curr-func* (atom #{'foo#1})]
   (let [func (eq/jit (eq/canonicalize '[(foo X) (sum (list X (list X (empty))))]) (fn [eq]) (fn [func]))]
     (func 3) => (equilibrium.core/return#1 6))))

```
Compilation is delayed until the first invocation of the returned
function. Once the returned function is called for the first time,
compilation takes place, and the two closures are called with the
equation and the compiled function.
```clojure
(fact
 (binding [eq/*curr-func* (atom #{'foo#1})]
   (let [eq-atom (atom nil)
         fn-atom (atom nil)
         func (eq/jit (eq/canonicalize '[(foo X) (sum (list X (list X (empty))))])
                      (partial reset! eq-atom) (partial reset! fn-atom))]
     @eq-atom => nil
     @fn-atom => nil
     (func 3) => (equilibrium.core/return#1 6)
     @eq-atom => (eq/canonicalize '[(foo X) (+ X (+ X 0))])
     @fn-atom => fn?
     ;; The new function behaves the same as the original function,
     ;; but runs faster since it does not have to compile itself.
     (@fn-atom 3) => (equilibrium.core/return#1 6))))
```
# Building a DSL

To build a DSL, we need to first define its primitives, using
`data` and `abstract` declarations. Then we define equations to
provide semantics to these primitives.

The DSL we define here has unary arithmetic operators. These
operators are applied to a number given to the semantic function.

The primitives include a `+` and a `*` operators, and a `seq` combinator.
```clojure
(eq/data (+ X) (* X) (seq A B))

```
We define its semantics through the `apply-op` function, which
takes the operator and a number, and applies the operator to the
number
```clojure
(eq/= (apply-op (+ X) N) (+ X N))
(eq/= (apply-op (* X) N) (* X N))

```
The semantics of the `seq` combinator is to first apply `A` to the
given number, and then `B`.
```clojure
(eq/= (apply-op (seq A B) N) (apply-op B (apply-op A N)))

```
Now we can define operations. For example, the `even` operation
which multiplies by 2, and the `odd` operation multiples a number
by 2, and then adds 1.
```clojure
(eq/= (even) (* 2))
(eq/= (odd) (seq (* 2) (+ 1)))
(eq/= (ten) (seq (odd) ;; 10(dec) = 1010(bin)
                 (seq (even)
                      (seq (odd)
                           (even)))))

```
We can evaluate this DSL by using its semanic function. We will
call it from Clojure, by adding the `#` suffix.

```clojure
(fact
 (apply-op#2 (ten#0) 0) => 10)

```
Although this DSL is relatively high-level, when we define a
function that uses its code (in this case, the `ten` "program" we
defined earlier), the generated code is reduced to plain
Equilibrium code, and the DSL layer disappears.
```clojure
(eq/= (apply-ten-to N) (apply-op (ten) N))
(fact
 ;; Partial evaluation is only done after the function has been called
 ;; once, due to JIT compilation.
 (apply-ten-to#1 0) => 10
 @apply-ten-to#1-code =>
 '[(equilibrium.core-test/apply-ten-to#1 N)
   (equilibrium.core/*#2
    2
    (equilibrium.core/+#2
     1
     (equilibrium.core/*#2
      2
      (equilibrium.core/*#2
       2
       (equilibrium.core/+#2
        1
        (equilibrium.core/*#2
         2 N))))))])

```
Specifically, the above generated code does not incur overhead for
dispatching.

### Higher-order Constructs

Now imagine we wish to take hold of the current value from within
the "program". We wish to bind the value at one point in the
program to a variable, and use it afterwards. This can be achieved
by defining an `abstract` concept.
```clojure
(eq/abstract (as X P)
             [(apply-op (as X P) X) (apply-op P X)])

```
This definition includes an equation defining the semantics of the
`as` construct. Its semantics is defined as binding the free
variable `X` with the number the program is applied to (the second
argument to `apply-op`), and then applying the rest of the program
(`P`) to the same value. Now, we can define the `square` operator
as follows:
```clojure
'(eq/= (square N) (apply-op (as X
                                (* X X)) N))

```

