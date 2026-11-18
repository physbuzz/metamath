---
title: "5. Variables, Binding, and Predicate Calculus"
---

<nav class="nav">
    <span class="activenav"><a href="04-propmm.html">← Previous</a></span>
    <span class="activenav"><a href="index.html">↑ Up</a></span>
    <span class="inactivenav" aria-disabled="true">Next →</span>
</nav>

<h1 id="05-predicate-calculus" style="border-bottom: none;">5. Variables, Binding, and Predicate Calculus</h1>

Links: [Chapter html](book/index.html#3.2.2-predicate-calculus), [pdf on metamath.org](https://us.metamath.org/downloads/metamath.pdf#page=82). All that work and we've only gone 5 pages forwards in the pdf!


@toc(hn)


## Introduction.

Before getting to predicate calculus, we should spend a bit of time
seeing how far we can get "without quantifiers." This question and related
ones such as "why do we need quantifiers?" takes us quite deep into metamathematics
and the debates of the early 1900's. I should emphasize to logicians reading
this section that we're coming at the issue from the perspective of Metamath tinkerers
with total disregard for mathematics, we just want to express fun concepts and we don't
care how we twist Metamath to get there. From this perspective, many concepts
of mathematical logic look quite strange and difficult to formulate.

We run into a problem immediately: what do we even mean, concretely, by "with quantifiers" or
"without quantifiers"?

The quantifier axioms in `set.mm` use
disjoint variable restrictions, so maybe the right framing is
whether or not `$d` is allowed? Nope, [MPE appendix 7](https://us.metamath.org/mpeuni/mmset.html#subsys) 
describes how to drop some of the axioms from `set.mm` such that we have predicate logic with no
disjoint variable restrictions (though the appendix does state that we have to build other 
machinery to take its place).

From what I can gather, at this point in a truly obstinate Metamath-first approach, 
we don't have the tools or terminology to motivate quantifiers for any other reason than
"we \[mathematicians\] often phrase proofs in them" or "the ZFC axioms have quantifiers in them."
If we're given a obfuscated Metamath database with the variables all renamed, we can't easily
determine whether it "uses quantifiers" or not, unless we do archaeological work or 
match the axioms directly to a publication. I really dislike this kind of
history-first, human-sociology-first statement, but I think it's the best we've got.

Reasons to include quantifiers, appeal to emotion:

- Axioms and statements containing variables are already a sort of "for all" statement. 
However, we find we can't include "not for all" statements.
- We also might want to have a $\forall$ statement in an assumption, which can't be done
with the tools we have so far. (Here I just mean that, in our databases, a statement like 
`mp.min $e |- P $.` doesn't mean "hypothesize that for all P, turnstile P," rather it can
be satisfied by any one `wff P` and `|- P`.)
- We might want nested $\forall$ statements.

Essentially, we have a notion of $\forall$ at the top level of a statement, 
but we can't do anything where we have to bring $\forall$ inside the statement. 
TODO: I'm still reading Frege's Begriffschrift, I believe this is the motivation given in there.

Finer points of quantifiers, appeal to Platonic ideals which we don't yet have the tools
to prove/discuss:

- [Hilbert and Bernays' first epsilon theorem](https://plato.stanford.edu/entries/epsilon-calculus/) 
states that in certain very general cases, theorems whose proofs involve quantifiers can be rewritten 
as proofs not involving quantifiers. However, it is not general enough for me to easily make a statement
like, "all theorems in any Metamath database of such-and-such form can be rewritten so as to not rely
on the quantifier axioms," because "any Metamath database" is too broad of a thing for me to constrain. 
The proof of the theorem *does* rely on an algorithm to transform proofs, so it's very constructive and 
concrete and could be a fun project. But it doesn't give us strong no-go theorems of the form "this new
system you're writing down contains no new theorems" because it's so easy to write axioms in Metamath
which land outside its purview.
- The ideas of [Primitive Recursive Arithmetic](https://en.wikipedia.org/wiki/Primitive_recursive_arithmetic) 
were developed by Skolem in 1923 with the explicit goal of being quantifier-free. (Skolem's work was later
made more precise and expanded upon, so we can't say that the full formal system is in that 1923 paper.)
- Quantifiers [can be viewed as](https://ncatlab.org/nlab/show/hyperdoctrine) left- and right- adjoints to 
substitution.
This is far outside the realm where I can comment, but it tells me that if we were in a different universe
where we chose a different foundation than Metamath, we might have quantifiers beautifully fall out of our 
theory right about now. So we're not saying quantifiers aren't special, merely that there is nothing 
special to motivate them in our notes right now. 

Okay, I tried to quarantine all of the things that I cannot concretely formalize into the above writing.
There's lots of tantalizing stuff, but let's try to illustrate things concretely with examples now.  

## 5.0 Arithmetic With and Without Quantifiers

This section contains no exercises. We're going to start with the theorems 
developed in the last chapter; so we have all of propositional logic at our
disposal, and all of the useful theorems and lemmas we want.

And I really mean we have all of propositional logic. In the file
[`code-04/prop.mm`](code-04/prop.mm), which 
is lines 1 through 12192 of `set.mm`, we have 1542 proofs of propositional logic. Basically, we can use 
$\rightarrow,$ $\leftrightarrow,$ $\land,$ $\lor,$ and $\neg$ to our heart's content.
Though I don't use them, it also contains and, xor, and probably other stuff, I wasn't picky.

### 5.0.1 Common arithmetic axioms

We next can imagine developing arithmetic. For starters, we define numbers of typecode `num`:

```mm
$c num = + * 0 S $.
$v t u v w $.
nt $f num t $.  nu $f num u $.  nv $f num v $.  nw $f num w $.
weq $a wff t = u $.
n0 $a num 0 $.
nS $a num S t $.
nadd $a num ( t + u ) $.
nmul $a num ( t * u ) $.
```

For axioms, there's no need to develop this all ourselves,
the best source for the axioms of arithmetic that I found was Peters 2022,
["Gödel’s Theorem Without Tears,"](https://www.ps.uni-saarland.de/~peters/bachelor/resources/thesis.edited.pdf#page=33) definition 4.16 p.23.
I think most of these axioms are simple enough that you could define them yourself
given only incidental exposure to the idea of starting with $0$ and applying a successor function $S.$ 
The only odd
axiom out is $\texttt{zos},$ which is indeed specific to Robinson's arithmetic[^1] and which
we do not go into detail on.

[^1]: $\texttt{zos}$ is axiom CD in Peters' notation, which I think refers to 
"case distinction." I renamed the axioms because I found I could never remember stuff like
$\texttt{ax-AZ}$ in proofs.

$$
\begin{array}{cl}
\texttt{eq-refl} & t = t \\
\texttt{eq-sym} & t = u \to u = t \\
\texttt{eq-tr} & t = u \to u = v \to t = v \\
\texttt{eq-s} & t = u \to S t = S u \\
\texttt{eq-add} & t = u \to v = w \to t + v = u + w \\
\texttt{eq-mul} & t = u \to v = w \to t \cdot v = u \cdot w \\
\texttt{add-0l} & 0 + t = t \\
\texttt{add-sl} & (S t) + u = S(t + u) \\
\texttt{mul-0l} & 0 \cdot t = 0 \\
\texttt{mul-sl} & (S t) \cdot u = u + t \cdot u \\
\texttt{zns} & 0 \ne S t \\
\texttt{zos} & t = 0 \lor (\exists u.\; t = S u) \\
\texttt{s-inj} & S t = S u \to t = u \\
\end{array}
$$

Define "System $B$" to be propositional logic, plus all of the above axioms except axiom 
$\texttt{zos}$ (which is read as "every integer is Zero Or a Successor", as opposed to $\texttt{zns}$ which 
is "Zero is Not a Successor"). 
Then my understanding is: 

- Robinson arithmetic is system $B$ plus predicate calculus plus $\texttt{zos}$.
- Peano arithmetic is system $B$ plus predicate calculus plus induction.
- Primitive Recursive Arithmetic (PRA) is system $B$ plus primitive recursive functions plus a 
predicate-free induction axiom.

(TODO cite Feferman, also Avigad, here)

Something I'd like to emphasize here is that we can "prove", or rather construct the term,
`wff 1 = 0` (ie. `wff S 0 = 0`). This isn't a problem. What is a problem is `|- 1 = 0`,
constructing that is a big problem.

### 5.0.2 Common arithmetic theorems

After this, we don't really need much ado. We can imagine having a whole host of helper theorems like in 
propositional logic. A decade ago we might have hemmed and hawed at how long this will take, but in 2026
we know we can knock it using any number of sledgehammers.

```mm
${
  eq-tri.1 $e |- t = u $.
  eq-tri.2 $e |- u = v $.
  eq-tri $p |- t = v $=
    nt nu weq nu nv weq nt nv weq eq-tri.1 eq-tri.2 nt nu nv eq-tr mp2 $.
$}
${
  eq-trd.1 $e |- ( ph -> t = u ) $.
  eq-trd.2 $e |- ( ph -> u = v ) $.
  eq-trd $p |- ( ph -> t = v ) $= 
    wph nu nv weq nt nv weq eq-trd.2 wph nt nu weq nu nv weq nt nv weq wi
    eq-trd.1 nt nu nv eq-tr syl mpd $.
$}
```

Well, and so on and so forth. But there's one glaring omission that we can't seem to prove...
commutativity of addition. Or more pointedly, given the axiom scheme `add-0l` which says
$0 + t = t,$ we'd expect to be able to prove the theorem scheme:

```mm
add-0r $p |- ( t + 0 ) = t $= ? $.
```

In fact, we can't prove this! To say "we can't prove it" requires some justification, though.
Number one, this is a metatheorem the likes of which I keep trying and failing to dodge. 
My concrete, novice perspective is the following: Suppose we introduce some constant `num e`, 
such that the axiom or theorem `|- -. ( e + 0 ) = e` is satisfied. Of course, `|- ( 0 + e ) = e` also
holds, because that's an axiom of system $B$. If we can prove or argue that this system is consistent, and that
the system $B$ is also consistent, then it can only be the case that `|- ( t + 0 ) = t` cannot be 
proved by system $B.$ Okay, but we can't really broach proofs like that without doing a lot more work
or a lot of a different kind of work, so we shelve that. The fact remains
that we don't seem to be able to prove `add-0r`.

But there is indeed an induction argument! 

If $(S^n 0+0)=S^n 0$, then $S(S^n+0)=S^{n+1}0$ by axiom `eq-s`. So $(S^{n+1}+0)=S^{n+1}0$ 
by `add-sl` (and probably `eq-sym` and `eq-tr`). Also, it is certainly true that $0+0=0$ by `add-0l`.
So mathematical induction could prove this handily! 

### 5.0.3 Induction without quantifiers

Here we're surely forced to use quantifiers, right? Nope!

Mathematical induction is usually phrased as the following rule[^2]:

[^2]: I omit the use of turnstiles
because I'm not talking about a Metamath essential hypothesis with typecode `|-`.

$$\frac{P(0)\quad P(t)\to P(t+1)}{P(u)}$$

(TODO: check and cite. I know I read good occurrences of induction as used in other books)

For us this is a bit awkward because we haven't built the machinery to define functions.
Really what we want to do is something like the following: 

Say our well-formed formula is $\varphi,$ which takes the value `r + 0 = r`, and which 
we want to "act like a function" in some way. One example is that we need to evaluate
this at $r=0.$ But... Metamath is just going to replace $\varphi$ with a fixed expression,
and it has to be that same expression at every occurrence in our formula! We can't say 
"at this point, unify $\varphi$ with `|- 0 + 0 = 0`, but then later on try to unify it
with `|- S t + 0 = S t`." 

How do we solve this? First off, we realize that $\varphi$ can only be unified with one
thing, so in the example case we've been using we say that phi is the wff `x + 0 = x`. 
How do we ensure that this doesn't get unified with `0 + 0 = 0` once, ruining our ability
to substitute other values of $x$? The answer is that `x` cannot be of typecode `num`.

We instead do a very clever trick. At least I think it's very clever. We make the following
definitions:

```mm
$c var $.
$v x $.
vx $f var x $.
nx $a num x $.
xzero $p |- ( x = 0 -> ( x + 0 ) = x ) $=
  vx nx n0 weq vx nx n0 nadd n0 vx nx vx nx n0 weq vx nx n0 nadd n0 n0 nadd n0
  vx nx n0 n0 eq-add-left n0 n0 nadd n0 weq vx nx n0 weq n0 add-0l a1i eq-trd
  vx nx n0 eq-sym eq-trd $.
```

We put $x=0$ in our antecedent, and then use the axioms of our arithmetic to 
"perform the substitution". The axioms of our arithmetic are usable because 
we're always allowed to convert `var x` to `num x` via `nx`. Yet we can never
unify, say, `S 0` in place of `x` because we would need `var S 0`, which 
we can never build.

I absolutely love this, because it's very instructive for us on two counts: 
It gives us a Metamath programming trick which we can use, which is
essentially the same notion as an object variable in logic. 
And it gives us a method to construct our axiom systems (our axiom systems
must be sufficiently powerful that we can apply the operations above which
should be interpreted as "substituting the variable for zero"). I think that's
a very general lesson about theory building.

(TODO: improve the above paragraph. Also cite the "object variable" thing.)

Introducing a `var` leads us to one other piece of machinery, whose construction
requires the use of disjoint variables.

Suppose we introduce vars and we manage to prove the
theorem `|- x + 0 = x`. We wouldn't actually be able to use this to prove `|- t + 0 = t`,
because t is a num. We can't allow `t` to be converted into a `var` either, as this would 
lead us straight back to the problem that we just fixed. 
No issue, we just apply our trick of "evaluating at a variable" again. We introduced 
the axiom `$a num x $.` to deal with `var`s, what's one more axiom?

Let $\varphi$ be our `wff` which we think of as a function of `x`. And $\psi$ is the value
of x as the `num t` that we want to plug in. Then we just create an axiom saying we can plug
in that value:

```mm
${ 
  vtonum.1 $e |- ( x = t -> ( ph <-> ps ) ) $.
  vtonum.2 $e |- ph $.
  vtonum $a |- ps $.
$}
```

It looks good, but in fact we can now prove `|- 1 = 0`. Why? Take `ph := x = x`, `t := 0`, `ps := x = 0`.
We conclude `|- x = 0`. A second application of `vtonum` with `ph := x = 0`, `t := 1`, and `ps := 1 = 0` 
concludes `|- 1 = 0`.

What went wrong? In our first application of `vtonum`, an $x$ was leftover in our formula even though
we were supposed to be substituting for $x$! The problem is that we allowed the variable $x$ to occur
anywhere in $\psi$. This is exactly what the disjoint variable restriction, `$d ... $.` prevents:

```mm
${ 
  $d x ps $. $d x t $.
  vtonum.1 $e |- ( x = t -> ( ph <-> ps ) ) $.
  vtonum.2 $e |- ph $.
  vtonum $a |- ps $.
$}
```

TODO: comment on the reason for the t variable restriction.

Compare this to a similar theorem inside set.mm, [`vtocl`](https://us.metamath.org/mpeuni/vtocl.html).

*Now*, we can begin to construct our induction axiom.
Well, we have a formula $\varphi$ which is our $P(x)$. We have a base case,
$P(0)$ which I will call $\psi$. The conclusion of our rule, $P(t)$ which can 
be evaluated at any `num t`, I'll call $\tau.$ The naming and ordering of the 
essential hypotheses is something we inherit from `set.mm` by the way, don't blame me 
for it![^3]

[^3]: An example of this is [nnind](https://us.metamath.org/mpeuni/nnind.html).

```mm
${
  $d x ps $. $d x ta $. $d x t $.
  ax-ind.at-zero $e |- ( x = 0 -> ( ph <-> ps ) ) $.
  ...
  ax-ind.at-num $e |- ( x = t ->  ( ph <-> ta ) ) $.
  ax-ind.base $e |- ps $.
  ...
  ax-ind $a |- ta $.
$}
```

Okay, and of course we also don't want our expression for $P(t)\to P(t+1)$ to unify
with some specific `num t`, so that has to be a var as well. 
So we evaluate at y (call the wff $\chi$), evaluate at y+1 (call the wff $\theta$), 
and have our inductive hypothesis $(\chi\to\theta)$.

```mm
${
  $d x ps $. $d x ta $. $d x t $. 
  $d x ch $. $d x th $. 
  $d x y $. $d y ph $.
  ax-ind.at-zero $e |- ( x = 0 -> ( ph <-> ps ) ) $.
  ax-ind.at-var $e |- ( x = y -> ( ph <-> ch ) ) $.
  ax-ind.at-succvar $e |- ( x = S y -> ( ph <-> th ) ) $.
  ax-ind.at-num $e |- ( x = t ->  ( ph <-> ta ) ) $.
  ax-ind.base $e |- ps $.
  ax-ind.step $e |- ( ch -> th ) $.
  ax-ind $a |- ta $.
$}
```

And there we have it, our axiom of induction!

#### 5.0.3a Applying the quantifier-free induction

TODO: proof that `|- ( t + 0 ) = t`

Maybe a more interesting proof?

### 5.0.4 Induction with quantifiers

Introducing quantifiers, we'll experiment with these more in 5.1

setvar discussion

Example of how to write vtonum

induction axiom

#### 5.0.4a Applying the quantifier-ful induction

TODO: proof that `|- ( t + 0 ) = t`

TODO probably a statement that there's nothing new if we repeated the "more interesting proof" down here.

### 5.0.5 Reading Skolem 1923

- Paper written in 1919 and published in 1923. I'm going to refer to it as Skolem 1923 though.

- I notice that I don't have a good definition of free or bound variable anywhere yet... that should probably be in 5.0.

- Paraphrased foreword comment: "in free-variable arithmetic, we can state and prove that there are infinitely many primes in the sense that $\forall x\exists\text{prime y}: x\lt y\leq x!+1.$ But that there exist infinitely many pairs of twin primes cannot (today) be stated by means of a free-variable formula." The book's preface to Skolem then says "the limitations of free-variable formulas are overcome, so far as possible [...]" which, in the version of PRA the author is talking about, does not 
mean that it can be stated.

- There are two different "Primitive Recursive Arithmetics" people talk about in modern terminology.
Number one is "System $B$ + primitive-recursive functions + quantifier-free induction." This can be 
denoted $\text{PRA}_{\text{qf}}.$ This is the system in which stating the twin prime conjecture 
cannot be easily done, and it's discussed in Feferman 1993[^4]. On the other hand, many authors (most authors?) use PRA to refer to a system
with predicate calculus, but with induction restricted to quantifier-free formulas. This is 
$\text{PRA}_{\text{fo}},$ "System $B$ + primitive-recursive functions + predicates + induction
restricted to quantifier-free formulas." Both these systems are defined and compared in Avigad 2002[^5].

[^4]: Solomon Feferman (1993), What Rests on What? The Proof-Theoretic Analysis of Mathematics, pp. 7-8
[^5]: Jeremy Avigad (2002), Ordinal Analysis Without Proofs, 

- In comparing to Metamath definitions, I wonder if Skolem would take issue with the metavariables
of our system being able to range over an infinite domain. I think not. I think there's something
buried in the writing here that an implicit leading "forall" outside the equation, which in our case
is a metavariable with given typecode, can also be seen as a variable name or placeholder and
not as "ranging over an infinite domain" at all.

Skolem's development:

`a + 1` is already defined for arbitrary `a`. Thus addition can be defined recursively:

**Definition 1:** `a + ( b + 1 ) = ( a + b ) + 1`

... I started reading this paper way too thoroughly, I'm going to read it while working on 
arith.mm




## 5.1 Building Predicate Calculus Ourselves

Okay, so we now have some arguments for why the machinery that we're going to introduce
is the way it is, and we have an idea of the types of issues we'd run into if we tried to
keep coding without copying and pasting `set.mm` and Norm Megill's implementation of 
Tarski's axioms.

In this section, we assume to have every propositional calculus tool we built in chapter 4. 
I will not, however, assume that we are working inside set.mm though you may prefer to 
work there.

In section 5.2, we'll switch to `set.mm` for good; I expect we'll stay there for the rest of these 
notes.

### 5.1.1 Our starting tools

> [!WARNING]
> This section is AI-generated and has not been reviewed.

Continue with the implication and negation exercises from 4.1.1–4.1.5.
Nothing from the supplied-connective section is needed. The standalone
`ai/predicate-calculus/small-exercises.mm` includes checked solutions to those
earlier exercises and leaves just the eight new targets below blank.
`small-reference.mm` contains their completed solutions. The original
`src/code-04/myset.mm` remains your working file.

We start with these additions to the language and axioms. `setvar` is a
syntactic type name; it introduces no set-theoretic axioms. `weq` constructs
variable-equality formulas. Until 5.1.4 there are no laws of equality, so
`x = y` is just a formula that happens to contain two variables.

```metamath
$c setvar A. = $.
$v x y z $.
vx $f setvar x $. vy $f setvar y $. vz $f setvar z $.
wal $a wff A. x ph $.
weq $a wff x = y $.
${ ax-gen.1 $e |- ph $. ax-gen $a |- A. x ph $. $}
ax-4 $a |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $.
${ $d x ph $. ax-5 $a |- ( ph -> A. x ph ) $. $}
```

`ax-gen` quantifies an established assertion. `ax-4` distributes a universal
quantifier over implication. `ax-5` introduces a quantifier on a formula
which does not contain its variable. Its distinctness condition is essential:
generalization alone does not give the unrestricted formula `ph -> A. x ph`.

### 5.1.2 Five constructions
> [!WARNING]
> This section is AI-generated and has not been reviewed.

Prove these in order. The last combines implication lifting with distribution;
there is no additional supplied predicate library.

```metamath
${
  $d x z $.
  $d y z $.
  ax5-example $p |- ( x = y -> A. z x = y ) $= ? $.
$}

${
  gen2.h1 $e |- ph $.
  gen2 $p |- A. x A. y ph $= ? $.
$}

${
  alimi.h1 $e |- ( ph -> ps ) $.
  alimi $p |- ( A. x ph -> A. x ps ) $= ? $.
$}

${
  $d ph x $.
  alrimiv.h1 $e |- ( ph -> ps ) $.
  alrimiv $p |- ( ph -> A. x ps ) $= ? $.
$}

${
  al2imi.h1 $e |- ( ph -> ( ps -> ch ) ) $.
  al2imi $p |- ( A. x ph -> ( A. x ps -> A. x ch ) ) $= ? $.
$}
```


#### Hints

- `ax5-example`: substitute `x = y` for `ph` and `z` for the bound variable in `ax-5`. Use `weq` for syntax. Its two inherited pairs are `x,z` and `y,z`; `x,y` is unnecessary.
- `gen2`: apply `ax-gen` over `y`, then over `x`. No distinctness condition is required.
- `alimi`: apply `ax-gen` to the given implication, then detach `ax-4` using `ax-mp`.
- `alrimiv`: use `syl` through `A. x ph`. `ax-5` supplies the first implication and `alimi` supplies the second. Only the first needs `$d x ph $.`.
- `al2imi`: lift the hypothesis using `alimi`, treating `( ps -> ch )` as one formula. Compose with `ax-4` using `syl`.

### 5.1.3 Checking substitutions
> [!WARNING]
> This section is AI-generated and has not been reviewed.

From the repository root:

```sh
metamath 'read "ai/predicate-calculus/small-exercises.mm"'
make -C ai/predicate-calculus check
```

In the proof assistant, start with `prove ax5-example`. To check distinctness,
the `invalid` target makes two independent copies of the reference file:

1. In the block for `ax5-example`, delete `$d x z $.` and leave the proof unchanged.
2. In that block, change the conclusion to `|- ( x = y -> A. x x = y )` and the proof to `vx vy weq vx ax-5`, retaining both original distinctness declarations.

```sh
make -C ai/predicate-calculus invalid
metamath 'read "ai/predicate-calculus/invalid/missing-pair.mm"' 'verify proof ax5-example' exit
metamath 'read "ai/predicate-calculus/invalid/shared-variable.mm"' 'verify proof ax5-example' exit
```

The first lacks an inherited pair. The second substitutes expressions with a
variable in common for arguments required to be disjoint. Both must report a
**disjoint variable (`$d`) violation**. Metamath can exit successfully despite
reporting proof errors, so inspect the diagnostic.

### 5.1.4 Equality: two more axioms, three more constructions
> [!WARNING]
> This section is AI-generated and has not been reviewed.

So far the quantifier only moves implications around. Tarski's system has two
more axioms for a language whose only predicate is equality:

```metamath
${
  $d x y $.
  ax6v $a |- -. A. x -. x = y $.
$}

ax-7 $a |- ( x = y -> ( x = z -> y = z ) ) $.
```


`ax6v` says that something equals `y`: it is not the case that every `x`
differs from it. `ax-7` says that two things equal to the same thing are equal
to each other. Together with `ax-gen`, `ax-4`, and `ax-5` these are all of
Tarski's predicate axioms for this language; `set.mm` adds `ax-8` and `ax-9`
for membership. Our `ax6v` is Axiom B7 of Tarski, which requires `x` and `y`
to be distinct. In `set.mm` the axiom `ax-6` has no such condition and `ax6v`
is a theorem that weakens it.

Prove these in order. They need nothing beyond chapter 04 and 5.1.2.

```metamath
${
  $d x y $.
  equid $p |- x = x $= ? $.
$}

equcomi $p |- ( x = y -> y = x ) $= ? $.

${
  $d ph x $.
  $d x y $.
  spvw $p |- ( A. x ph -> ph ) $= ? $.
$}
```


`equid` has a distinctness condition on a variable that does not occur in
its statement: `y` is a dummy variable used inside the proof. After proving
it, compare

```text
show statement equid /full
show statement spvw /full
```

Metamath lists `<x,y>` as an *optional* pair in both. A mandatory pair
constrains everyone who applies the theorem; an optional pair only constrains
the proof. `equcomi` applies `equid` and needs no `$d` at all.

`spvw` removes a quantifier that binds nothing. Even this needs `ax6v`: in an
empty domain `A. x ph` would hold for every `ph`. Its converse is `ax-5`, so
the two implications of `19.3v` are now both available. We have no `<->` here
to state them as one equivalence.

#### Hints

- `equid`: this one is longer than the others. Specialize `ax-7` to `( y = x -> ( y = x -> x = x ) )` and contract with `pm2.43i`. Contrapose with `con3i` and lift over `y` with `alimi`. `ax-5` on `-. x = x` gives the missing first link for `syl`; this is the step using `$d x y $.`. Contrapose with `con1i` and detach `ax6v`.
- `equcomi`: this one should be quick. Specialize `ax-7` with `z := x`, swap the antecedents with `com12`, and detach `equid`.
- `spvw`: aim for `( A. x ph -> ( -. ph -> A. x -. x = y ) )` using `pm2.21`, `al2imi`, `ax-5` on `-. ph`, `syl`, and `com12`. `ax6v` refutes the inner consequent, so `pm2.21i` and `imim2i` change it to `ph`. Finish with `pm2.18`.

For a third rejection experiment, delete `$d x y $.` from the completed
`equid`. `make -C ai/predicate-calculus invalid` writes that variant too:

```sh
metamath 'read "ai/predicate-calculus/invalid/missing-dummy-pair.mm"' 'verify proof equid' exit
```

This is where we stop building. Bound-variable change, the existential
quantifier, and anything stated with `<->`, `/\`, or `\/` need a lot more
groundwork, and `set.mm` has already done it. We continue there.


## 5.2 Working Inside `set.mm`

### 5.2.1 A brief guide to the connectives
> [!WARNING]
> This section is AI-generated and has not been reviewed.

Here we use the full local `src/code/set.mm`. We can inspect the supporting
proofs without reconstructing their entire dependency chain first. The
following survey is a map of useful interfaces, not another sequence of
elementary connective exercises.

The syntax rules construct equivalence, conjunction, disjunction, and
existential formulas. The `df-` assertions define their relationships to
older connectives. Definitions are `$a` assertions: Metamath checks their
consequences, not their soundness as definitions. See the Proof Explorer's
[discussion of definitions](https://us.metamath.org/mpeuni/mmset.html#definitions).

```metamath
wb $a wff ( ph <-> ps ) $.

wa $a wff ( ph /\ ps ) $.

wo $a wff ( ph \/ ps ) $.

df-bi $a |- -. ( ( ( ph <-> ps ) -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) -> -. ( -. ( ( ph -> ps
  ) -> -. ( ps -> ph ) ) -> ( ph <-> ps ) ) ) $.

df-an $a |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) $.

df-or $a |- ( ( ph \/ ps ) <-> ( -. ph -> ps ) ) $.

wex $a wff E. x ph $.

df-ex $a |- ( E. x ph <-> -. A. x -. ph ) $.

${
  biimpi.1 $e |- ( ph <-> ps ) $.
  biimpi $p |- ( ph -> ps ) $= ... $.
$}

${
  biimpri.1 $e |- ( ph <-> ps ) $.
  biimpri $p |- ( ps -> ph ) $= ... $.
$}
```


The long primitive definition of equivalence is normally accessed through
its introduction and elimination rules. Conjunction lets us package two
claims; disjunction supports introduction and reasoning by cases. Familiar
identities such as commutativity have proofs in the library; we will use
these interfaces without assigning those elementary proofs here.

### 5.2.2 Useful interfaces and the machinery we are passing over
> [!WARNING]
> This section is AI-generated and has not been reviewed.

In these supplied interfaces, `...` abbreviates the existing proof. Syntax
hypotheses use the declarations already present in `set.mm`; essential
hypotheses and distinctness conditions are written out.

```metamath
${
  impbii.1 $e |- ( ph -> ps ) $.
  impbii.2 $e |- ( ps -> ph ) $.
  impbii $p |- ( ph <-> ps ) $= ... $.
$}

simpl $p |- ( ( ph /\ ps ) -> ph ) $= ... $.

simpr $p |- ( ( ph /\ ps ) -> ps ) $= ... $.

${
  jca.1 $e |- ( ph -> ps ) $.
  jca.2 $e |- ( ph -> ch ) $.
  jca $p |- ( ph -> ( ps /\ ch ) ) $= ... $.
$}

orc $p |- ( ph -> ( ph \/ ps ) ) $= ... $.

olc $p |- ( ph -> ( ps \/ ph ) ) $= ... $.

${
  jaoi.1 $e |- ( ph -> ps ) $.
  jaoi.2 $e |- ( ch -> ps ) $.
  jaoi $p |- ( ( ph \/ ch ) -> ps ) $= ... $.
$}

${
  syl.1 $e |- ( ph -> ps ) $.
  syl.2 $e |- ( ps -> ch ) $.
  syl $p |- ( ph -> ch ) $= ... $.
$}

${
  con3i.a $e |- ( ph -> ps ) $.
  con3i $p |- ( -. ps -> -. ph ) $= ... $.
$}

sp $p |- ( A. x ph -> ph ) $= ... $.

${
  $d ph x $.
  alrimiv.1 $e |- ( ph -> ps ) $.
  alrimiv $p |- ( ph -> A. x ps ) $= ... $.
$}
```


`biimpi` and `biimpri` extract the two implications from an equivalence;
`impbii` joins them. `simpl` and `simpr` extract conjuncts; `jca` combines two
consequences of one antecedent. `orc` and `olc` introduce disjunction, while
`jaoi` combines its two cases. For example, applying `alimi` to `simpl`
transports conjunction elimination through a universal quantifier.

We are passing over many inference, deduction, and closed variants, along
with specialized rearrangements. A deduction rule retains a common antecedent
in its premises and conclusion; an inference rule consumes established
assertions. `syl` and `con3i` are familiar examples of reusable inference tools.

Specialization `sp` is a derived theorem. Its construction, and the equality
machinery supporting substitution, are available to inspect. Nonfreeness can
also be expressed by explicit hypotheses rather than the stronger syntactic
nonoccurrence condition `$d x ph $.`. The bound-variable rules below expose
both kinds of interface. No set-theoretic reasoning is needed for our targets.

### 5.2.3 Reconstructing existing proofs
> [!WARNING]
> This section is AI-generated and has not been reviewed.

Start at the repository root:

```text
read "src/code/set.mm"
show statement albii /full
show proof albii /lemmon
prove albii
delete all
show new_proof /lemmon
```

`prove` enters the proof assistant with the existing proof; `delete all`
clears that current proof so it can be reconstructed. Use `assign`, `match`,
and `improve` as in chapter 04. Earlier assertions in the database are
available. The intended routes below avoid detaching an earlier equivalent
version that would bypass the mechanism being practiced; they are not an
exhaustive whitelist of permitted tools.

For saving experiments, first copy the source to
`ai/predicate-calculus/.build/set-work.mm` (create `.build` if needed), read
that copy, and use `save new_proof` followed by `write source` to that same
copy. Do not overwrite the original database.

```metamath
${
  albii.1 $e |- ( ph <-> ps ) $.
  albii $p |- ( A. x ph <-> A. x ps ) $= ? $.
$}

${
  $d ph x $.
  19.3v $p |- ( A. x ph <-> ph ) $= ? $.
$}

${
  $d ph x $.
  19.9v $p |- ( E. x ph <-> ph ) $= ? $.
$}

${
  eximi.1 $e |- ( ph -> ps ) $.
  eximi $p |- ( E. x ph -> E. x ps ) $= ? $.
$}

19.26 $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ A. x ps ) ) $= ? $.

${
  $d ph x $.
  19.21v $p |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) $= ? $.
$}

${
  $d ph y $.
  $d ps x $.
  $d x y $.
  cbvalvw.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
  cbvalvw $p |- ( A. x ph <-> A. y ps ) $= ? $.
$}
```


#### Hints

- `albii`: extract both implications with `biimpi` and `biimpri`, use `alimi` twice, and assemble with `impbii`. Avoid the closed lifting theorem `albi` for this exercise.
- `19.3v`: combine restricted specialization `spvw` and `ax-5` with `impbii`. We proved `spvw` from the axioms in 5.1.4; the library's route goes through `spnfw`.
- `19.9v`: apply `19.3v` to `-. ph`, lift through negation with `notbii`, and compose with `df-ex` and double negation using `bitri`. Use `impbii` with `notnotr` and `notnot` to orient double negation as needed.
- `eximi`: contrapose the premise with `con3i`, apply `alimi`, and contrapose again. Extract the two appropriately directed implications from `df-ex` and compose with `syl`. Avoid the closed theorem `exim` as a shortcut.
- `19.26`: derive the forward direction by applying `alimi` to `simpl` and `simpr`, then `jca`. For the converse use `alanimi` with `id`. Finish with `impbii`.
- `19.21v`: `stdpc5v` gives the forward direction. For the reverse, use `imim1i` on `ax5e` to reach `( E. x ph -> A. x ps )`, then apply `19.38` and compose with `syl`. Assemble with `impbii`.
- `cbvalvw`: inspect `cbvalw` and its four explicit nonfreeness premises. Supply them using `ax-5` on `A. x ph` over `y`, `-. ps` over `x`, `A. y ps` over `x`, and `-. ph` over `y`. Keep the given equality-conditioned equivalence as the last premise.

The reference solutions in `library-solutions.json` are checked by replacing
these proofs at their original positions in a disposable full-database copy.
This ensures they use earlier assertions and cannot invoke the target itself.

### 5.2.4 A concrete bound-variable change
> [!WARNING]
> This section is AI-generated and has not been reviewed.

`rename-equality` is our own label, not an existing theorem to look up in
`set.mm`. The generated extension loads the whole library and adds this target:

```metamath
${ $d x y z $.
rename-equality $p |- ( A. x x = z <-> A. y y = z ) $= ? $. $}
```


```sh
cd ai/predicate-calculus
metamath 'read library-extension-exercises.mm'
```

Then use `prove rename-equality`. Its reference proof is in the matching
extension reference file. This is a particular checked equivalence; a theorem
about a general renaming algorithm would require a representation of syntax.

#### Hints

Use `cbvalvw` with `ph := x = z` and `ps := y = z`. The earlier equality
congruence theorem `equequ1` supplies its premise. The inherited conditions
are exactly the three pairs `x,y`, `x,z`, and `y,z`, protecting the unchanged
variable `z` from capture.