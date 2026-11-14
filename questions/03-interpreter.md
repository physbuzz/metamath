---
title: "Metamath Interpreters (Basics)"
display-path: Metamath
---

## Quiz Questions

### Question 1

In Metamath, what is the difference between a math symbol and a statement label? Can a label have the same name as a
math symbol? If a hypothesis is in a block, can we reuse the label of a hypothesis after its block has closed?

#### Answer

"Math symbol" refers to either a constant or variable, which must be declared with `$c` and `$v`.

Labels name the statements `$f $e $a $p` so we can refer to them in proofs.

Labels must be unique throughout the database, even when the statements they label are no longer active. 
Closing a block does not let us reuse its hypothesis labels. A label also can't share a name with any constant
or variable.

### Question 2

In Metamath, what does it mean for a math symbol to be active? Can symbols be declared again?

#### Answer

Math symbols are only constants or variables, and constants can only be declared at the topmost level of the proof
database, so constants are simple: they are active and can be used from the point they're declared to the end of the file.

A variable is active from the point it's declared to the end of its block. Inactive variables may be redeclared (see
[megill ch4](book/index.html#redeclaration-of-math-symbols)). Variables are also special because if they're used in
any statement, they must have a floating hypothesis associated with them defining the typecode, and the typecode of
the variable may not change upon redeclaration.

### Question 3

In the following database, which statements go inactive at the end of the block `$}`? 
What are `pass`'s mandatory hypotheses, and what does applying it in a proof outside of the block do?

```mm
$c term |- $.
$v t $.
ft $f term t $.
${
    $v x $.
    fx $f term x $.
    h $e |- x $.
    pass $a |- x $.
$}
```

#### Answer

Hypotheses `$f` and `$e` are active from their declaration until the end of the block. Assertions `$a` and `$p`
never go inactive.

There is no hitch to applying the axiom `pass`. It requires two mandatory hypotheses to be satisfied, so for example
if the proof stack contains the following:

```mm
term foo
|- foo
``` 

This would satisfy the two mandatory hypotheses of `pass` without issue.

### Question 4

In Metamath, can a variable have two active floating hypotheses? Can blocks shadow variables?

#### Answer

No on both counts. An active variable must have a single active floating hypothesis by the time it's used in a later
statement. We might think we could shadow a definition like this:

```mm
$v x $. $c term wff $.
tx $f term x $.
$( statement using x as a term here $)
${
    $v x $.
    wffx $f wff x $.
    $( statement using x as a wff here $)
$}
```

but this is not allowed. So scoping follows special semantics in Metamath that might not be familiar from other languages.

### Question 5

How do we determing a Metamath assertion's mandatory variables, and mandatory hypotheses and their order? 

How do we determine its 
optional hypotheses, and what are optional hypotheses? 

#### Answer

The mandatory variables of an assertion are any variables that occur in its list of math symbols or in any active
essential hypotheses. In the case of a proof, this *does not* include variables merely because they are referenced by
the statements after the `$=` sign. "Mandatory variable" is a term not introduced 'til
[Megill 4.1.3](book/index.html#4.1.3-basic-syntax).

The mandatory hypotheses of an assertion are all active essential hypotheses, and all the floating hypotheses
that define the typecode of each mandatory variable. They are ordered in the order that they appear in the database.

Optional hypotheses are remaining active floating hypotheses.
A theorem's proof may use them, but they do not need to be referred to later.
Every active essential hypothesis is mandatory; there are no optional essential hypotheses.

In this example, `th` has mandatory variable `P`, mandatory hypotheses `wp h` (in that order), and optional
hypothesis `wq`.

```mm
$c wff |- $. $v P Q $.
wp $f wff P $.
${
    wq $f wff Q $.
    h $e |- P $.
    th $p |- P $= h $.
$}
```

### Question 6

In the following Metamath database, what are the mandatory hypotheses of `rule`, in order? Give the
hypotheses in the order they must be satisfied on the proof stack, from bottom to top.

```mm
$c wff |- ( ) -> $.
$v x y z $.
wx $f wff x $.
hx $e |- x $.
wy $f wff y $.
wz $f wff z $.
hy $e |- y $.
rule $a |- ( x -> x ) $.
```

#### Answer

The mandatory hypotheses are, in order, `wx hx wy hy`. This means that the proof stack needs to have the following 
form at the time `rule` is applied:

```mm
wff x
|- x
wff y
|- y
```

(convention w/ stack growing downwards)

### Question 7

In Metamath, does an active essential hypothesis still become mandatory if it doesn't occur in a `$p`
statement's proof? What about if it doesn't share any math symbols with an `$a` statement?

#### Answer

Yes, in both cases. Active essential hypotheses are always mandatory hypotheses, even if the proof doesn't use them.
We still apply the same procedure when checking the proof, and such cases might be especially trivial but 
we still pop symbols off the proof stack and compare the symbols in the proof stack with the symbols in the 
mandatory hypothesis for consistency.

### Question 8

In Metamath, describe how the verifier processes the statement labels in a proof (ignoring disjoint variable restrictions).

#### Answer

First we initialize the proof stack to be empty, then we start reading the proof labels from left to right.

If we encounter a hypothesis, we push the expression onto the stack unchanged.

If we encounter an assertion, we must use the top entries on the proof stack to satisfy its mandatory hypotheses
in order, with the last mandatory hypothesis matching the most recent entry on the proof stack.

We then have to unify the mandatory hypotheses with the proof stack, which means finding a consistent replacement rule 
that replaces the variables in the mandatory hypothesis list with other lists of math symbols, such that we get the 
exact expressions on the proof stack in order with matching typecodes. In other languages "unification" can be 
complicated, but in this context unification is particularly simple, so we always either succeed or find that the 
statements can't be unified (in which case the proof is invalid).

Once a valid replacement is found, we make sure those elements we used are removed from the proof stack, then
we push the result of applying our replacement rule to the assertion's expression.

The proof succeeds if every step is valid and the final stack contains only the theorem's expression.

### Question 9

In Metamath, suppose we're in a database, in the middle of verifying a proof.
We have the following database: 

```mm
$c wff |- ( ) -> A B $.
$v P $.
wp $f wff P $.
${
    h $e |- ( P -> P ) $.
    rule $a |- P $.
$}
```

The proof stack looks like the following:

```text
wff A
|- ( A -> B )
```

Does applying `rule` to the stack succeed? If so, what gets pushed? If not, what could we change
on the stack to make it succeed?

#### Answer

The application fails. The floating hypothesis gives `P := A`, so the essential hypothesis requires `|- ( A -> A )`.
That cannot be unified with `|- ( A -> B )` because both occurrences of `P` must receive the same replacement.

If the second stack entry were `|- ( A -> A )`, the application would succeed. It would consume both entries and push
`|- A`.
