# Motivation

We design domain specific languages (DSL) to offers users flexibility and expressivity and the ability to create solutions to a wide range of problems within a certain domain. For example, OpenMOLE proposes a DSL for the domain of simulation experiments. The DSL, however, is also a source of a hindrance because users, experts of the targetted domain but not necessarily experienced computer programmers, must deal with the complexity of computer 
programming: syntax, type and logic errors, learning the language and developing experience with it.

The purpose of this project is to propose an alternative way to make
users interact with a DSL that does not require them to write code while
retaining the expressiveness and flexibility of the full fledged DSL. The remaining of this section sketches the approach. It assumes some familiarity of the readers with types and functions (e.g. function composition) and that the DSL of interest is expressed as a set of functions.

Notation: a function `f` that takes a value of type `a` and returns a value of 
type `b` is written `f: a -> b`. Function are treated as curried, such that a 
function of `n` arguments can be written `f: a1 -> a2 -> ... -> an -> b` which 
is equivalent to `f: a1 -> (a2 -> (... -> (an -> b)...))`. Function 
application is written without parentheses; `f` applied to the arguments 1, 2
and 3 is written: `f 1 2 3`. We use partial function application; a function 
`g: Integer -> Integer -> Integer` applied only to 1 argument gives a function 
that takes one integer and returns an integers: `g 1: Integer -> Integer`.

We know how to combine functions together by feeding the result of one to another. This is what standard function composition. Let's write `.` the usual infix function composition operator:

```
(g . f) x = g (f x)
```

We are looking for a generic way to chain two functions of arbitrary arity (including arity 0) in the form of an operator we call `using` such that:

```
using x g = g x
using f1 g x = g (f1 x)
using f2 g x y = g (f2 x y)
using f3 g x y z = g (f3 x y z)
etc.
```
 
where x is a value or nullary function and f1, f2, f3, etc. are respectively functions of arity 1, 2, 3, etc.

An expression like `using f`, with 
`f: a1 -> ... -> an -> b`, is a function that transforms any function 
`g: b -> c` into a function `a1 -> ... -> an -> c`. It uses `f` to construct `g`'s first argument from `f`'s arguments.

The operator `using` enables us to combine any set of functions together in a linear fashion. For example consider the following functions that may constitute a very limited DSL:

```
min a b = if a < b then a else b
norm x y z = (x^2 + y^2 + z^2) / 3
```

We can compute the minimum average of the norm of the vectors `(1, 2, 3)` and `(4, 5, 6)` like:

```
using min . using norm . using 1 . using 2 . using 3 
    . using norm . using 4 . using 5 . using 6
```

An expression `using f` can be composed with any expression `using g`
as long as the return type of the former matches the input type of the latter. For example, if `min`'s type is 
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
`Double -> a`[^type_match].

[^type_match]: Details of type unification can be found in https://web.cecs.pdx.edu/~mpj/thih/TypingHaskellInHaskell.html#tthFtNtAAB

This entails that at any point during the construction of the sequence
above, we can choose the next `using x` expression among those whose
type match. So, we can imagine a program that iteratively asks a user
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


# Functions

list of functions
- user defined
- Special predefined constructors ReadInt...


# Constructors

 

# Constructor morphism 




## Method

Given a function `g: b -> c`, function application is the process of
feeding a value `x` to `g` to get it's return value. Let's write `&`
the function that does nothing else than to take a value, a function,
and the apply to the latter to the former:

```
&: a -> (a -> b) -> b
& x f = f x
```

Notice that the partial application `& x: (a -> b) -> b` is a function that transform a function from `a` to `b` into a value of type `b`, or equivalently a nullary function that returns a `b`. Since we can see a function as
a constructor for a value of certain types given values of other types, we
will functions like `& x` constructor morphisms, i.e. a function that morphs a constructor into another. We will look for more constructor morphisms below.

If we don't have any value readily available to feed to `g` above but have 
a function `f: a -> b`, we can use it to construct a value for `g`'s argument.
This is simply function composition. Let's write the common infix fonction composition operator `.` and its prefix version `comp`: 

```
comp g f = g (f x)
```

The expression `& f . comp` has the type `(b -> c) -> a -> c`. It turns a function from `b` to `c` into a function from `a` to `c`. It is thus also
a constructor morphism. It is different from the previous one in that it was constructed from any function that takes one argument, `f: a -> b`, and returns a function that also takes a similar argument. 

Going further, we can make constructor morphisms from any function that takes two arguments `f2: a1 -> a2 -> b` with the expression `& f . comp . comp` which has the type `(b -> c) -> a1 -> a2 -> c`.

Generally, we can make a constructor morphism from any n-ary function 
`fn: a1 -> ... -> an -> b` by composing n times the function `& f` with `comp`.

Let's define the function `using` that takes a function of arity n and turns it into a constructor morphism such a defined above:

```
using f = & f               if n = 0 
        & f . comp        if n = 1 
        & f . comp . comp if n = 2
        etc.
```


# Graph


Nodes are types.

The node `SCRIPT -> SCRIPT` belongs to the graph.

For any node in the graph of type `a` and for all morphism schemes `m` of type `b -> c` such that `a` and `b` have a mgu `u`, there is an edge `m` between node `a` and node `subst(u, c)`.


# From paths to constructors

The purpose is to remove the functions `&` et `comp` that were introduced when making the constructor morphisms.

