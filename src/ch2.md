---
title: "Chapter 2. Using the Metamath Program"
---

<h1 id="chapter-2-using-the-metamath-program" style="border-bottom: none;">Chapter 2. Using the Metamath Program</h1>

<nav class="nav">
    <span class="activenav"><a href="ch1.html">← Previous</a></span>
    <span class="activenav"><a href="index.html">↑ Up</a></span>
    <span class="activenav"><a href="ch3.html">Next →</a></span>
</nav>

[Book html](book/metamath.html#using-the-metamath-program) &nbsp;|&nbsp; [Book pdf](book/metamath.pdf#page=55)

@toc

## A few things to know and memorize:

- `$c` -- constants. User-defined, "meaningless"
- `$v` -- Variables. "Metavariables" or "placeholders"
- `$e` -- Essential hypothesis. ("logical hypothesis")
- `$f` -- Floating Hypothesis. ("variable type hypothesis") Must contain a constant followed by a variable.
- `$a` -- Axiomatic assertion. Constant followed by arbitrarily many math symbols.
- `$p` -- Provable assertion. Constant followed by arbitrarily many math symbols.

Notes while trying to understand the metamath proof in ch2:

 - `tze $a term 0 $.` This is an axiomatic hypothesis, as opposed to the floating hypotheses earlier. The floating hypotheses were not "axioms" because they refer to metavariables. But 0 is an actual term of the language (?) so we need an actual axiom.
- `tpl $a term ( t + r ) $.` Here even though the concept of parentheses aren't in the language, can I come up with an example where the addition of parentheses changes the way in which expression parsing occurs? 
- "$a is a constant followed by arbitrary seq of math symbols" -- The definition is this simple, no tricks. But it's not devoid of structure. I guess that structure is the consistency checks on popping from the stack and substituting all of the mandatory hypotheses?
- In the statement `tpl $a term ( t + r ) $.` constants `( + )` don't need any hypotheses. `t` and `r` need hypotheses because they are metavariables. This is satisfied by the hypotheses `$f term t $.` and `$f term r $.`

Metamath's show statement command can show you a statement's mandatory hypotheses.

## Running the ch2 example

@src-begin(mm, collapsed)
$( Declare the constant symbols we will use $)
    $c 0 + = -> ( ) term wff |- $.
$( Declare the metavariables we will use $)
    $v t r s P Q $.
$( Specify properties of the metavariables $)
    tt $f term t $.
    tr $f term r $.
    ts $f term s $.
    wp $f wff P $.
    wq $f wff Q $.
$( Define "term" and "wff" $)
    tze $a term 0 $.
    tpl $a term ( t + r ) $.
    weq $a wff t = r $.
    wim $a wff ( P -> Q ) $.
$( State the axioms $)
    a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.
    a2 $a |- ( t + 0 ) = t $.
$( Define the modus ponens inference rule $)
    ${
        min $e |- P $.
        maj $e |- ( P -> Q ) $.
        mp $a |- Q $.
    $}
$( Prove a theorem $)
    th1 $p |- t = t $=
    $( Here is its proof: $)
        tt tze tpl tt weq tt tt weq tt a2 tt tze tpl
        tt weq tt tze tpl tt weq tt tt weq wim tt a2
        tt tze tpl tt tt a1 mp mp
    $.
@src-end

## Working through the Proof without knowing Metamath

I had great success in looking at the central proof example in chapter 2, and saying with conviction, "this is a ridiculously simple interaction of a stack and a substitution system."
There are only so many ways you can parse through a stack and substitute stuff
as you read through the proof (the list of `tt tt weq tt ...` statements),
and so eventually you'll stumble on the correct algorithm.

For example, two sequences that occur a few times in the proof are:

- `tt tze tpl` (occurs 4 times)
- `tt weq` (occurs 5 times)

Let's look at the first one. First, `tt` is our floating hypothesis (`$f`) which
 declares `t` as a variable of typecode `term`, so `term t` is pushed to the stack. (Note: the word "typecode" is not used until chapter 4!! I thought of it as the "tag" for t, but typecode is the usual term)

Second, `term 0` is pushed to the stack.

Third, we want to push `tpl` to the stack. tpl's definition is `tpl $a term ( t + r ) $.`, which has two placeholders/variables t and r. The real way to phrase this is that we have two *mandatory hypotheses*. We pop from the stack to substitute our term 0 in for the second placeholder (the most recent mandatory hypothesis). We pop from the stack to substitute our secondmost recent mandatory hypothesis. And we're left with `term ( t + 0 )`. 

Up to the last two statements, this is the whole procedure of the proof. push terms, pop terms when we need to substitute variables. There are no surprises or nonsequiturs up until the modus ponens rules. Just before we parse the first `mp`, the stack looks like the following. All the impenetrable work has gone into building these expressions, and I cannot stress enough that it is not that interesting (which means if you're confused, you should work through this by hand to convince yourself yeah, it's just substituting stuff in). 

```
wff ( t + 0 ) = t
wff t = t
|- ( t + 0 ) = t 
wff ( t + 0 ) = t
wff ( ( t + 0 ) = t -> t = t ) 
|- ( t + 0 ) = t 
|- ( ( t + 0 ) = t -> ( ( t + 0 ) = t -> t = t ) ) 
```

When we parse `mp`, I initially thought we had two mandatory hypotheses meaning we pop two things from the stack (the most recent two turnstiles) and deduce what P and Q must be. But in fact, we don't do deductions like that in Metamath!
The substitutions for P and Q must be given explicitly, they are not deduced. 
Therefore we need to pop four things from the stack in total. In order, the things we pop (the four mandatory hypotheses for `mp`) are `|- ( P -> Q )`, `|- P`, `Q`, `P`. The order is because this is the reverse order of how they appear in the database. This is established on page 130, section 4.2.5, of the Metamath book. Okay, so we pop four things from the stack, do our substitutions, and push turnstile Q. The proof stack now looks like this:

```
wff ( t + 0 ) = t
wff t = t
|- ( t + 0 ) = t 
|- ( ( t + 0 ) = t -> t = t ) 
```

Same thing again. This time `t = t` is in the slot for `Q`, so:

```
|- t = t
```

QED!

## 2.3

## Quiz Questions

### Q
In Metamath, what does a typecode refer to?
#### A
A typecode is a constant defined first inside `$c mytypecode $.` It is used to assign a type in a floating hypothesis, `hypoth $f mytypecode x $.` This is a hypothesis which states that the variable `x` is of type `mytypecode`. Note that there is no complicated "type system", so this is really just a label that is associated with `x` whenever we apply `hypoth`.

### Q
In Metamath, what does the symbol `$c` mean, and how is it used?
#### A
c stands for constant. These are user-defined, and the user needs to define things like typecodes `wff`, `term`, and the other primitive symbols you want to define like `(`, `)`, `|-`, `->`. Like all Metamath statements, `$c` must be closed with a `$.` symbol. For example: `$c wff term ( ) |- -> $.` 

### Q
In Metamath, what does the symbol `$v` mean, and how is it used?
#### A
v stands for variable. These are user-defined. Every variable that you want to use must be declared. The statement `$v` must be closed with a `$.` symbol. For example, `$v t r s P Q $.` 

When variables occur in an essential hypothesis or axiom, they must be filled (satisfied) by other mandatory hypotheses. (??? Not sure if this is correct or if it's the correct phrasing of what I mean).

### Q
In Metamath, what does the symbol `$e` mean, and how is it used?
#### A
e stands for essential hypothesis. It is also called a logical hypothesis. It must have a label, and can be followed by any number of math symbols, eg.
`mytheorem $e |- ( P -> Q ) $.`
...

### Q
In Metamath, what does the symbol `$e` mean, and how is it used?





- `$e` -- Essential hypothesis. ("logical hypothesis")
- `$f` -- Floating Hypothesis. ("variable type hypothesis") Must contain a constant followed by a variable.
- `$a` -- Axiomatic assertion. Constant followed by arbitrarily many math symbols.
- `$p` -- Provable assertion. Constant followed by arbitrarily many math symbols.
