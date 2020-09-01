Intro
=====

This program illustrates that we can guide domain specific language (DSL) users 
through the process of building complex expressions using function types.
It takes as input a list of functions constituting the DSL and their types.
Then, it iteratively proposes the user a list of functions to chose from until a
complete program is constructed. At each step, the program gives the user a
choice among the DSL functions whose types fit in the expression that is
being constructed. Thanks to constraining the expression building with type
information, the final expression is guaranteed to type check.


Usage
=====

Install `cargo`

    $ curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

and run

    $ cargo run


Motivation
==========

We design domain specific languages (DSL) to offer users flexibility and
expressivity and the ability to create solutions to a wide range of problems
within a certain domain. For example, the software [OpenMOLE](openmole.org) is a
simulation platform which proposes a DSL to build simulation experiments. The
DSL, however, is also a source of a hindrance because users, experts of the
targetted domain but not necessarily experienced computer programmers, must deal
with the complexity of computer programming: syntax, type and logic errors,
learning the language and developing experience with it.

The purpose of this project is to propose an alternative way to make
users interact with a DSL that does not require them to write code
while retaining the expressiveness and flexibility of the full fledged
DSL. The remaining of this section sketches the approach. It assumes
some familiarity of the readers with types and functions (e.g. function
composition) and that the DSL of interest is expressed as a set of
functions.

Notation: a function `f` that takes a value of type `a` and returns a value of 
type `b` is written `f: a -> b`. Function  application is written without 
parentheses; `f` applied to the arguments 1, 2 and 3 is written: `f 1 2 3`. 
Function are curried, such that a  function of `n` arguments can be written 
`f: a1 -> a2 -> ... -> an -> b` which  is equivalent to 
`f: a1 -> (a2 -> (... -> (an -> b)...))`: a function that returns a function that returns a function ... that returns a value of type `b`. This naturally leads to partial function application; a function
`g: Integer -> Integer -> Integer` applied  only to 1 argument gives a function
that takes one integer and returns an integers: `g 1: Integer -> Integer`.

Standard function composition combines functions together by feeding the result of one to another. Let's write `.` the usual infix function composition operator:

```
(g . f) x = g (f x)
```

We are looking for a generic way to chain two functions of arbitrary arity (including arity 0) in the form of an operator we call `using` such that:

```
using a g = g a
using f1 g x = g (f1 x)
using f2 g x y = g (f2 x y)
using f3 g x y z = g (f3 x y z)
etc.
```
 
where x is a value or nullary function and f1, f2, f3, etc. are respectively functions of arity 1, 2, 3, etc.

An expression like `using f`, with 
`f: a1 -> ... -> an -> b`, is a function that transforms any function 
`g: b -> c` into a function `a1 -> ... -> an -> c`. It uses `f` to construct `g`'s first argument from `f`'s arguments.

The operator `using` enables us to combine any set of functions together in a linear fashion. For example consider the following functions that may constitute a very limited DSL for 3D linear algebra:

```
min: Double -> Double -> Double
min a b = if a < b then a else b

norm: Double -> Double -> Double -> Double
norm x y z = (x^2 + y^2 + z^2) / 3
```

We can compute the minimum average of the norm of the vectors `(1, 2, 3)` and `(4, 5, 6)` like (recall that `.` is the standard function composition operator):

```
using min . using norm . using 1 . using 2 . using 3 
    . using norm . using 4 . using 5 . using 6
```

An expression `using f` can be composed with any expression `using g`
as long as the return type of the former matches the input type of the latter. 
For example, if `min`'s type is 
`Double -> Double -> Double`, the type of `using min` is 
`(Double -> a) -> (Double -> Double -> a)`. The parentheses on the 
right part were added to
illustrate that `using min` operates on a function of type `Double -> a`
(the input type) and returns a function of type `Double -> Double -> a`
(the output type). We can compose it to the right with any expression
`using f` whose argument type matches `Double -> Double -> a`, like we
did above with `using norm`, which is of type 
`(Double -> b) -> (Double -> Double -> Double -> b)`. Indeed, the return 
type of `using min`, `Double -> Double -> a` and the input type of 
`using norm`, `Double -> b` match because we can find a substitution of 
type variables such that both types are equal: replace `b` by 
`Double -> a`[Type matching].

This entails that at any point during the construction of the sequence
above, we can choose the next `using x` expression among those whose
types match. So, we can imagine a program that iteratively asks a user
which function to use, among candidates that type check, until a complete
program is composed. This is what this project demonstrates. 

Given a DSL expressed as a set of functions (see for example the file (./openmole.cons)), the program iteratively asks users what function (alternatively called constructor, for functions *construct* values) they want to use next, until we come to a complete program that solves a domain's problem.

Notice that given a set of specified functions `f, g, h, ...`, that
may for example constitute domain specific language, the set of `using
f, using g, using h, ...` define a graph where they are the edges and
types are the nodes. There might be interesting things to do with such a
graph, such as displaying it to make an overall map of a domain specific
language, make it possible for users to compose programs by clicking on
nodes, etc.



Type matching
=============

Two types match if there is a substitution `s` of type variables that makes them equal. Here are examples of types that match:

- `Double` and `Double`,
- `a` and `Double`,
- `a` and `b`,
- `Pair a b` and `Pair Double Double`,
- `a -> a` and `Double -> Double` ,

and examples of types that don't:

- `Double` and `Int`
- `Pair Double Double` `Pair Int a`
- `a -> a` and `Double -> Int`

A complete descriptions of the type machinery used here can be found
[here](https://web.cecs.pdx.edu/~mpj/thih/TypingHaskellInHaskell.html#tthFtNtAAB).
Part of this type system is implemented in <src/type_sy.md>.

The function `type_sy::mgu` computes a unifier between two types if
one exists. A unifier `s` is a sequence of substitutions such that
`apply_substitution s type1 = apply s type2`, where the function
`apply_substitution` simply returns a new type after having substituted
the type variables according to the given substituton. The function
`apply_substitution` is in `type_sy::Types`.



Construction of the operator "using"
====================================

Given a function `g: b -> c`, function application is the process of
feeding a value `x` to `g` to get it's return value. Let's write `&`
the function that does nothing else than to take a value, a function,
and then apply the latter to the former:

```
&: a -> (a -> b) -> b
& x f = f x
```

Notice that the partial application `& x: (a -> b) -> b` is a function
that transform a function from `a` to `b` into a value of type `b`, or
equivalently a nullary function that returns a `b`. Since we can see a
function as a constructor for a value of certain types given values of
other types, we will functions like `& x` constructor morphisms, i.e. a
function that morphs a constructor into another. We will look for more
constructor morphisms below.

If we don't have any value readily available to feed to `g` above but
have a function `f: a -> b`, we can use it to construct a value for
`g`'s argument.  This is simply function composition. Let's write the
common infix fonction composition operator `.` and its prefix version
`comp`:

```
comp g f = g (f x)
```

The expression `& f . comp` has the type `(b -> c) -> a -> c`. It turns a
function from `b` to `c` into a function from `a` to `c`. It is thus
also a constructor morphism. It is different from the previous one
in that it was constructed from any function that takes one argument,
`f: a -> b`, and returns a function that also takes a similar argument.

Going further, we can make constructor morphisms from any function that
takes two arguments `f2: a1 -> a2 -> b` with the expression 
`& f . comp . comp` 
which has the type `(b -> c) -> a1 -> a2 -> c`.

Generally, we can make a constructor morphism from any n-ary function 
`fn: a1 -> ... -> an -> b` by composing n times the function `& f` with `comp`.

Let's define the function `using` that takes a function of arity n and turns it into a constructor morphism such a defined above:

```
using f = & f               if n = 0 
          & f . comp        if n = 1 
          & f . comp . comp if n = 2
          etc.
```



Constructors
============

The functions of the DSL and the special constructors form the
*constructors*. The DSL is specified by the user (e.g. the file
<dsl/openmole.cons>). The input file parser is implemented in
<src/parse.rs>. The special constructors are functions that trigger some
actions such as asking for user input. Currently, they are:

- `ReadInt: Int`
- `ReadDouble: Double`
- `ReadFilePath: FilePath`
- `ReadText: Text`

Each special function can be reduced to a raw value with
`cons::SpecialCons::run`. For the special functions just mentionned,
it will ask for user input and return the given value to the special
function. Ideally, checks are performed on the input to ensure that the
value returned is conform to the special function return type.


Graph
=====

The nodes are types.

For any node in the graph of type `a -> b`, there is an edge out for
each function of the DSL or special function `f: x1 -> ... -> xn -> y`
if we can pass `f`'s result to any function of type `a -> b`, i.e. if there exists a unifier or substitution `s = mgu y a`, thence `apply_substitution s y = apply_substitution s a`. The target node of such an edge is the type
`xs1 -> ... -> xsn -> bs`, where for all i `xsi = apply_substitution s xi`, and
`bs = apply_substitution s b`.

Special care must be taken to avoid variable name capture when computing
(with `mgu`) and applying the substitution. To this end, the type
variables in `f`'s type are renamed to type variables absent from the
source node type. This is performed with the combined use of functions
`type_sy::quantify` and `type_sy::fresh_inst`.

The node `SCRIPT -> SCRIPT` belongs to the graph. It is the identity
morphism restricted to values of types `SCRIPT`. The other nodes of the
graph are all those encountered while recursively following all edges from this starting node. 

As a consequence, in order to have any other node at all, the DSL must contain
at least one function returning a value of type `SCRIPT`, such that there will be at least one edge leaving `SCRIPT -> SCRIPT`. For example `f: a -> b -> SCRIPT` will yield an edge between `SCRIPT -> SCRIPT` and `a -> b −> SCRIPT`. 

As edges are recursively traversed, a path in the graph can end up in the node `SCRIPT`, from which no edge leave. A path from `SCRIPT -> SCRIPT` to `SCRIPT` is considered complete. For example, given the functions

```
min_script :: Int -> SCRIPT
min_script x = "The minimum value is {x}"

min :: Int -> Int -> Int
min a b = if a < b then a else b
```

the sequence of edges

```
using min_script, using min, using ReadInt, using ReadInt
```

traverse the nodes

```
SCRIPT -> SCRIPT, Int -> SCRIPT, Int -> Int -> SCRIPT, Int -> SCRIPT, SCRIPT.
```



User interaction
================

Starting from node `SCRIPT -> SCRIPT`, the program iteratively asks the user what edge to follow by giving a choice among DSL functions and special functions attached to the candidate edges. It stops when encountering the node `SCRIPT`. When the traversing an edge representing one of the special function, it immediately triggers it's reduction to a value by executing the function `cons::SpecialCons::run`. That way the user is invited to input the raw values as the path on the graph is being made.



From paths to the DSL
=====================

A complete path in the graph previously defined represents the construction of an expression in the DSL, i.e. applications of functions to values or the results of other functions. To recover it we must first compose together all the expressions `using f` along the path with standard function composition, yielding the expression such as given in a previous example:

```
using min . using norm . using 1 . using 2 . using 3 
    . using norm . using 4 . using 5 . using 6
```

Then we must eliminate the `&`, `comp` and `.` functions that were introduced by the operator `using`. This is performed by `cons::uncat_cons`. The elimination rules are:

```
f . g = comp f g
comp f g x = f (g x)
& x f = f x
```

We are left with only DSL functions and special functions. [As
mentioned][Constructors], special functions can be reduced
to raw values with `cons::SpecialCons::run`.



From DSL to a script
====================

In the input DSL, each function defines a piece of text that assembled together can realize a full DSL program. At the end of the interaction with the user, the program reduces the path to the DSL following the [elimination rules][From paths to the DSL] and interprets the resulting applications of
DSL functions to produce and print the final script.

