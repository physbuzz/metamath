---
title: "1. Working through a Metamath Proof by Hand (Megill ch2)"
---

<nav class="nav">
    <span class="activenav"><a href="00-rant.html">← Previous</a></span>
    <span class="activenav"><a href="index.html">↑ Up</a></span>
    <span class="activenav"><a href="02-sicp-logic.html">Next →</a></span>
</nav>

<h1 id="01-megillch2" style="border-bottom: none;">1. Working through a Metamath Proof by Hand (Megill ch2)</h1>


Notes while reading Megill ch. 2. Links: [Chapter html](book/index.html#using-the-metamath-program), [pdf on metamath.org](https://us.metamath.org/downloads/metamath.pdf#page=55).

@toc

## A few things to know and memorize:

- `$c` -- constants. User-defined, "meaningless"
- `$v` -- Variables. "Metavariables" or "placeholders"
- `$e` -- Essential hypothesis. ("logical hypothesis")
- `$f` -- Floating Hypothesis. ("variable type hypothesis") Must contain a constant followed by a variable.
- `$a` -- Axiomatic assertion. Constant followed by arbitrarily many math symbols.
- `$p` -- Provable assertion. Constant followed by arbitrarily many math symbols.

Notes while trying to understand the metamath proof in ch2:

 - `tze $a term 0 $.` This is an axiomatic hypothesis, as opposed to the floating hypotheses earlier. The floating hypotheses were not "axioms" because they refer to metavariables. But `0` is an actual term of the language (?) so we need an actual axiom.
- `tpl $a term ( t + r ) $.` Here parentheses are just constants, not actual metamath syntax. though the concept of parentheses aren't in the language, can I come up with an example where the addition of parentheses changes the way in which expression parsing occurs? 
- "`$a` is a constant followed by arbitrary seq of math symbols" -- The definition is simple, no tricks. I don't think there is any invalid axiom we can write by this definition. (Later when we introduce the `$d` symbol maybe? Unsure if this puts constraints on the axiom itself, or simply on what is allowed to be substited in for the mandatory hypotheses of an axiom.)
- In the statement `tpl $a term ( t + r ) $.` constants `( + )` don't need any hypotheses. `t` and `r` need hypotheses because they are metavariables. These are satisfied by the hypotheses `$f term t $.` and `$f term r $.`
- Metamath's `show` command can show you a statement's mandatory hypotheses, very useful for just
starting out when I've been unsure of what a statement's mhs are.

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

## Working through the proof without knowing Metamath

I found success in looking at the central proof example in chapter 2, and saying with conviction, "this is a ridiculously simple interaction of a stack and a substitution system."
There are only so many ways you can parse through a stack and substitute stuff
as you read through the proof (the list of `tt tt weq tt ...` statements),
and so eventually you'll stumble on the correct algorithm.

For example, two sequences that occur a few times in the proof are:

- `tt tze tpl` (occurs 4 times)
- `tt weq` (occurs 5 times)

Let's look at the first one. First, `tt` is our floating hypothesis (`$f`) which
declares `t` as a variable of typecode `term`, so `term t` is pushed to the stack. 
(Note: the word "typecode" is not used until chapter 4!! I thought of it as the "tag" for `t`, 
but typecode is the usual term)

Second, `term 0` is pushed to the stack.

Third, we want to push `tpl` to the stack. `tpl`'s definition is `tpl $a term ( t + r ) $.`, which has two placeholders aka variables `t` and `r`. The real way to phrase this is that we have two *mandatory hypotheses*. We pop from the stack to substitute our `term 0` in for the second placeholder (the most recent mandatory hypothesis). We pop from the stack to substitute our secondmost recent mandatory hypothesis. And we're left with `term ( t + 0 )`.

Turning our attention back to the whole proof, actually repeating this procedure works perfectly up until
the last two statements (`mp mp`).
We push terms when we hit an `$f` or the axiom with only constants in it `tze`, and we pop terms when we need 
to substitute variables. There are no surprises or nonsequiturs up until the modus ponens rules. 
Just before we parse the first `mp`, the stack looks like the following. And I'd like to reemphasize that
all the impenetrable work up until `mp mp` proceeds exactly like the `tt tze tpl` example with no surprises.

```
wff ( t + 0 ) = t
wff t = t
|- ( t + 0 ) = t 
wff ( t + 0 ) = t
wff ( ( t + 0 ) = t -> t = t ) 
|- ( t + 0 ) = t 
|- ( ( t + 0 ) = t -> ( ( t + 0 ) = t -> t = t ) ) 
```

When we parse `mp`, I initially thought we had two mandatory hypotheses meaning we pop two things from the stack 
(the most recent two turnstiles) and deduce what `P` and `Q` must be. But in fact, we don't get that fancy 
in Metamath! The substitutions for `P` and `Q` must be given explicitly, they are not figured out from
fancy algorithms. 
Therefore we need to pop four things from the stack in total. In order, the things we pop (the four mandatory 
hypotheses for `mp`) are `|- ( P -> Q )`, `|- P`, `Q`, `P`. The order is because this is the reverse order of 
how they appear in the database. This is established on page 130, section 4.2.5, of the Metamath book. Okay, 
so we pop four things from the stack, do our substitutions, and push turnstile `Q`. The proof stack now looks 
like this:

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

Especially useful stuff in the interactive CLI:
- `prove theorem1` -> `delete all` to practice.
- `assign 1 mp` -> Assign proof line 1 to the hypothesis `mp`.
- `improve all` -> used in ch2 for, when the "proof structure" is complete, there's still a lot of statements to fill, so `improve` can automatically construct those statements.


## Quiz Questions

### Question 1

In Metamath, what does a typecode refer to?

#### Answer

A typecode is a constant defined first inside `$c mytypecode $.` It is used to assign a type in a floating hypothesis,
`hypoth $f mytypecode x $.` This is a hypothesis which states that the variable `x` is of type `mytypecode`. Note that
there is no complicated "type system", so this is really just a constant that is associated with `x` whenever we apply
`hypoth`.

Note: For some reason, "typecode" isn't defined until chapter 4.1! But it's the correct term, so I'm using it from 
the beginning.

### Question 2

In Metamath, what does the statement `$c` mean and how is it used?

#### Answer

`c` stands for constant. These are user-defined, and the user needs to define things like typecodes `wff`, `term`, and
the other primitive symbols you want to define like `(`, `)`, `|-`, `->`. The `$c` statement must be closed with a `$.`
symbol. For example: `$c wff term ( ) |- -> $.`

### Question 3

In Metamath, what does the statement `$v` mean and how is it used?

#### Answer

`v` stands for variable. These are user-defined. Every variable that you want to use must be declared. The statement
`$v` must be closed with a `$.` symbol. For example, `$v t r s P Q $.`

Every variable used in an essential hypothesis or assertion must have an active floating hypothesis specifying its typecode.
When applying an assertion, the proof must supply expressions satisfying its mandatory hypotheses.

### Question 4

In Metamath, what does the statement `$e` mean and how is it used?

#### Answer

`e` stands for essential hypothesis. It is also called a logical hypothesis. It must have a label, followed by `$e`, a
typecode constant, and any number of math symbols, ending with `$.`, eg. `mytheorem $e |- ( P -> Q ) $.`

### Question 5

In Metamath, what does the statement `$f` mean and how is it used?

#### Answer

`f` stands for floating hypothesis. It is also called a variable-type hypothesis. It must have a label, followed by
`$f`, a typecode constant, and a variable, ending with `$.`. eg. `tt $f term t $.`

### Question 6

In Metamath, what does the statement `$a` mean and how is it used?

#### Answer

`a` stands for axiomatic assertion. It introduces an assertion without a proof. It must have a label, followed by `$a`,
a typecode constant, and zero or more math symbols, ending with `$.`. For example: `tze $a term 0 $.` This asserts that
`0` is a term. Axiomatic assertions can express syntax rules as well as logical axioms and inference rules.

### Question 7

In Metamath, what does the symbol `$p` mean, and how is it used?

#### Answer

`p` stands for provable assertion. It must have a label, followed by `$p`, a typecode constant, and zero or more math
symbols. These are followed by `$=`, a proof, and `$.`. The proof must establish the stated expression from the
available hypotheses and earlier assertions.

For example, given the mandatory-hypothesis-free axiom `tze $a term 0 $.`, the statement `th $p term 0 $= tze $.` proves `term 0`.

A proof can have a `?` in it, meaning the proof will not be checked and has unfinished steps.

### Question 8

What are the differences and similarities between the Metamath statements `$a` and `$p`? Can they have mandatory
hypotheses that must be satisfied before being used?

#### Answer

Similarities: `$a` and `$p` are both *assertions*. They are labeled statements followed by a typecode and any number of math
*symbols*.

The axiom statement `$a` must end with a `$.` after its math symbols. But the proof statement `$p` has its math symbols
followed by `$=` and then a sequence of labels, signifying the Metamath proof steps, followed by `$.` A Metamath proof
may also contain a `?` signifying the proof is incomplete.

Both kinds of assertion can have hypotheses that must be satisfied when the assertion is used.

### Question 9

What are the differences and similarities between the Metamath statements `$f` and `$e`? Can they have mandatory
hypotheses that must be satisfied before being used?

#### Answer

Similarities: `$f` and `$e` are both *hypotheses*. They are labeled statements with a typecode constant at the start of their
expressions. Both end with `$.` and have no proof attached.

A floating hypothesis `$f` has exactly one variable after its typecode, and is use to specify that 
variables type as its typecode. eg. `tt $f term t $.` not only makes a hypothesis `tt` which we can use 
in proofs, it also says the variable `t` has typecode `term`.

An essential hypothesis `$e` has any number of math symbols after its typecode and is meant to supply a 
logical premise, for example the "minor" hypothesis of modus ponens: `min $e |- P $.`

Neither statement has mandatory hypotheses of its own. When a hypothesis is used in a proof, its expression
is pushed onto the proof stack unchanged.

### Question 10

Recall the Metamath database of Megill ch2, which included statements such as...

```mm
$v t P $. $c term wff 0 $.
tt $f term t $.
wp $f wff P $.
tze $a term 0 $.
```

Why was the statement declaring `0` a term an axiomatic assertion, whereas the statement declaring `t` a term a floating
hypothesis?

#### Answer

A floating hypothesis may only have one math symbol after its typecode, and that symbol must be a variable. However `0`
is a constant. Instead, we are able to push `term 0` to the proof stack by using an axiom which has no essential
hypotheses, `tze`.

It is also important that `tze` is not a hypothesis. When the mandatory hypothesis of some axiom or theorem is a
floating hypothesis, this can end up giving us a replacement rule telling us what a given variable gets replaced by.
This process--unification--makes no sense to apply to the constant `0`.

### Question 11

In Metamath, consider the axiom `tpl $a term ( t + r ) $.`, how many mandatory hypotheses are required?
How would you apply it in a proof?

Note: Assume standard terminology as used in set.mm or demo0.mm. So `t` and `r` are variables with active
floating hypotheses defining their typecodes, appropriate symbols are constants, and so on. Assume there 
are no active essential hypotheses.

#### Answer

Two mandatory hypotheses are required, one for each variable that occurs in the axiom's symbol list. 
When applying `tpl` in a proof step, 
we pop two entries from the proof stack which must match with the typecodes of `t` and `r`, and which 
give us the rules about how to replace the variables `t` and `r` in the proof statement. 

Here is an example of a trivial proof demonstrating this symbol replacement.

```mm
$c term ( + ) $. $v t r u v $.
tt $f term t $.
tr $f term r $.
tu $f term u $.
tv $f term v $.
tpl $a term ( t + r ) $.
tpl.vacuous $p term ( u + v ) $= tu tv tpl $.
```

### Question 12 

In Metamath, in the middle of a proof, an axiom is `a2 $a |- ( t + 0 ) = t $.`. The mandatory hypothesis of `a2` is
`tt $f term t $.` and the term on the top of the proof stack is `term ( r + 0 )`. What is the resulting expression after
applying `a2`?

Assume conventions of `demo0.mm`, so things like `|-` and `term` and so on are constants.

#### Answer

The result is `|- ( ( r + 0 ) + 0 ) = ( r + 0 )`.

The statement on the proof stack `term ( r + 0 )` is unified with the mandatory hypothesis `term t` to find the
replacement rule, by which we replace every variable `t` in the axiom's list of math symbols with the list of math
symbols `( r + 0 )`.

### Question 13

In Metamath, start with an empty proof stack and the following database. Trace the proof fragment `tt tze tpl tt weq`.
What statement is left on the stack after applying the statements?

```metamath
$c term wff 0 + = ( ) $.
$v t r $.
tt $f term t $.
tr $f term r $.
tze $a term 0 $.
tpl $a term ( t + r ) $.
weq $a wff t = r $.
```

#### Answer

The proof fragment constructs `wff ( t + 0 ) = t` and pushes it to the proof stack.

1. `tt` pushes `term t`.
2. `tze` pushes `term 0`.
3. `tpl` consumes two entries from the stack, substituting `t` for its first variable and `0` for its second. It pushes
   `term ( t + 0 )`.
4. `tt` pushes `term t`.
5. `weq` consumes the two terms and pushes `wff ( t + 0 ) = t`.

### Question 14 

In the following Metamath database, how many mandatory hypotheses does `mp` have? How does this differ from the way we
normally think about modus ponens in mathematics?

```metamath
$c wff |- ( ) -> $.
$v P Q $.
wp $f wff P $.
wq $f wff Q $.
${
    min $e |- P $.
    maj $e |- ( P -> Q ) $.
    mp $a |- Q $.
$}
```

#### Answer

`mp` has four mandatory hypotheses: `wp`, `wq`, `min`, and `maj`. This means that before applying `mp` we expect the
proof stack to contain the following four entries, where the last statement is the top of the stack.

```text
wff ( a b c )
wff ( x y z )
|- ( a b c )
|- ( ( a b c ) -> ( x y z ) )
```

Normally in mathematics we think of modus ponens as having two premises. And indeed we could imagine that just given the
two entries off the top of the stack, we can infer what must replace the variables `P` and `Q`. But the Metamath
verifier doesn't figure this kind of thing out for us (in other words: it doesn't have a complex unification algorithm),
instead the floating hypotheses tell us exactly how things are parsed. First we unify `wff ( a b c )` with the mandatory
hypothesis `$f wff P $.` to figure out that `P` should be replaced with `( a b c )`. Next, we unify `wff ( x y z )` with
mandatory hypothesis `$f wff Q $.` to figure out that `Q` should be replaced with `( x y z )`. For the next two
mandatory hypotheses `min` and `maj`, we simply have to check that their expressions, after substitution, match the
corresponding proof-stack entries.

### Question 15

Consider the axiom schemas

$$
\begin{gather*}
(t=r \rightarrow(t=s \rightarrow r=s))  \tag{A1}\\
(t+0)=t \tag{A2}
\end{gather*}
$$

Using these axioms and modus ponens, prove $t=t$ with a standard mathematical proof.

Next, describe how you would write the proof in the Metamath proof assistant, assuming the database defines all the
terms (such as in `demo0.mm` of ch2). It might be worthwhile to open up the metamath proof assistant to go through the
steps yourself from memory.

#### Hint

The second part of the question is section 2.4. It might be useful to open up the proof assistant and recreate the
`demo0.mm` proof. In the metamath CLI, commands `prove th1`, `delete all`, and the command `show new_proof` with
arguments `/lemmon` or `/all` can be useful. From there, you'll want to use the command `assign n label` to assign line
`n` to proof step `label`. Finally, you can get it to a point where `improve all` can take over.

#### Answer

The following steps would be an acceptable proof. When applying axiom A1, we substitute $t+0$ for $t$, and $t$ for both
$r$ and $s$.

$$
\begin{align*}
&t+0=t \tag{by A2} \\
&(t+0=t) \to ((t+0=t) \to t=t) \tag{by A1} \\
&(t+0=t) \to t=t \tag{MP} \\
&t=t \tag{MP}
\end{align*}
$$

To construct this proof in the proof assistant, work backwards from $t=t:$ assign `mp` to the final goal, then another
`mp` to the implication needed as its major premise. For the second-to-last `mp`, we know its major premise comes from
an application of `a1`, so we also assign `a1` to that goal.

Where we need `term t`, we assign `tt`. Where we need $(t+0)=t$ we assign `a2` and use `tt` as applicable (otherwise
we'll just get `( $5 + 0 ) = $5` for example). Finally, if all logical steps are satisfied then we can write
`improve all` to finish the proof. 

This is a brief explanation so this answer may be insufficient. If you get stuck reproducing the proof in the proof
explorer, refer to [Megill ch2.4](book/index.html#2.4-your-first-proof) and follow the CLI usage.

### Question 16

In the Metamath CLI, remember the ch2 example:

```mm
$( demo0.mm excerpt $)
a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.
a2 $a |- ( t + 0 ) = t $.
${
    min $e |- P $.
    maj $e |- ( P -> Q ) $.
    mp $a |- Q $.
$}
th1 $p |- t = t $= ... $.
```

You load `demo0.mm`, type `prove th1`, and clear it with `delete all`. What does `assign 1 mp` do?

#### Answer

`1` refers to the proof line, at the start this only consists of the goal, `|- t = t`.

`assign 1 mp` says that this should arise as the conclusion of modus ponens, `|- Q`. It infers what `Q` must be
(`t = t`), but leaves `P` uninferred--rather than using the symbol `P`, this is a variable that has yet to be filled, so
we use a placeholder symbol `$n` to represent that it hasn't been populated. Modus ponens has four mandatory hypotheses,
so this creates four new proof statements that must be satisfied. The proof is then:

```
MM-PA> delete all
The entire proof was deleted.
1    th1=? $? |- t = t
MM-PA> assign 1 mp
3 -1   min=?  $? |- $2
4      maj=?  $? |- ( $2 -> t = t )
MM-PA> show new_proof/all/lemmon
1 ?              $? wff $2
2 ?              $? wff t = t
3 ?              $? |- $2
4 ?              $? |- ( $2 -> t = t )
5 1,2,3,4 mp     $a |- t = t
```
