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

The names of these axioms correspond to the names in 
`arith-common.mm`, embedded below:

@src(code-05/arith-common.mm, noexecute, collapsed)

Define "System $A$" to be propositional logic plus all of our arithmetic axioms except axiom 
$\texttt{zos}$ (which is read as "every integer is Zero Or a Successor", as opposed to $\texttt{zns}$ which 
is "Zero is Not a Successor"). 
Then my understanding is: 

- Robinson arithmetic is system $A$ plus predicate calculus plus $\texttt{zos}$.
- Peano arithmetic is system $A$ plus predicate calculus plus induction.
- Primitive-Recursive Arithmetic (PRA)[^2] is system $A$ plus a predicate-free induction axiom, 
plus primitive-recursive functions[^3].

[^2]: There are two different "Primitive Recursive Arithmetics" people talk about in modern terminology.
Number one is "System $A$ + primitive-recursive functions + predicate-free induction." This can be 
denoted $\text{PRA}_{\text{qf}}$
and it's discussed in Feferman 1993 "What Rests on What? The Proof-Theoretic Analysis of Mathematics," pp. 7-8. 
Many authors (most authors?) use PRA to refer to a system
with predicate calculus (first order logic), but with induction restricted to quantifier-free formulas. This is 
$\text{PRA}_{\text{fo}},$ "System $A$ + primitive-recursive functions + predicates + induction
restricted to quantifier-free formulas." Both these systems are defined and compared in 
Avigad 2002, "Ordinal Analysis Without Proofs."

[^3]: There's not some big "set of primitive-recursive function axioms" to add to our database. 
We just are only allowed to define functions satisfying (TODO insert specification). This could 
be done with some machinery and a PRF-builder notation, or it could be enforced with a linter
like `set.mm`, but if we use any we'll just define functions ourselves and be extra careful
to follow the rules :)

PRA has a long and storied history with lots of tantalizing stuff;
Gödel and metamathematics and things. But our motivation is much more innocent: we have 
some axioms for arithmetic, now let's see what we can and can't prove.

Elementary note: In the last chapter, 
we could construct terms like `wff ph -> -. ph` without issue. It's an
issue if we construct the term `|- ph -> -. ph`. Similarly here, we'll construct terms like
`num 0` and then `wff 1 = 0`, or rather `wff S 0 = 0`, but this is no issue for the same reason,
whereas `|- 1 = 0` is a big, big issue! I only 
bring it up because "oh no, I'm not constructing a contradiction am I?" goes through my head
every time I type `$a`.

### 5.0.2 Common arithmetic theorems

We can imagine having a whole host of helper theorems like we built in  
propositional logic, and that's exactly what we have in `arith-common.mm`.

Let's walk through a few of the theorems. First, since we just introduced
equality, we can work with a bunch of theorems involving that. In `set.mm`
we care about equality of `class`es, but here we care about equality of `num`s.
Here's `eqcomi`, `eqtri`, and `eqtr4i`. The links go to the analogous
theorems in set.mm, of course, I'm just stealing the naming convention.


$$
\frac{\vdash t=u}{\vdash u=t}\quad\href{https://us.metamath.org/mpeuni/eqcomi.html}{\texttt{eqcomi}};\qquad
\frac{\vdash t=u\quad \vdash u=v}{\vdash t=v}\quad\href{https://us.metamath.org/mpeuni/eqtri.html}{\texttt{eqtri}}
$$
$$
\frac{\vdash t=u\quad\vdash v=u}{\vdash t=v}\quad\href{https://us.metamath.org/mpeuni/eqtr4i.html}{\texttt{eqtr4i}}
$$

Okay... let's walk through a proof of `|- ( 1 + 0 ) = 1`. This isn't given to us for free, we only have the axiom `|- ( 0 + t ) = t`.

```
MM-PA> show n/lemmon
24 df-1          $a |- 1 = S 0
25 24 addeq1i    $p |- ( 1 + 0 ) = ( S 0 + 0 )
28 add-sl        $a |- ( S 0 + 0 ) = S ( 0 + 0 )
34 add-0l        $a |- ( 0 + 0 ) = 0
35 34 suceqi     $p |- S ( 0 + 0 ) = S 0
36 25,28,35 3eqtri  $p |- ( 1 + 0 ) = S 0
37 df-1          $a |- 1 = S 0
38 36,37 eqtr4i  $p |- ( 1 + 0 ) = 1
```

This is a bit difficult to parse. Working from the goal backwards, clearly the first thing to do is get rid of `1`. This is 
accomplished at step 35. `( 0 + 0 ) = 0` is an axiom, and `3eqtri` chains three equalities, which are built at 
steps 25, 38, 35.

$$(1+0)=(S0+0)=S(0+0)=S0.$$

And the only reason we don't add `S0=1` at the end of that chain is that we haven't defined a `4eqtri`.
So the proof strategy for this is to first write out the chain of equalities you want to make, and then puzzle out
how to build each one from the axioms.

Ok, it's a bit weird how this doesn't follow immediately from the axiom though. What about $(2+0)=2$ and $(3+0)=3$? Well, we
can figure out there's a common method to all these proofs. We define:

$$
\frac{\vdash t=Su\quad \vdash (u+0)=u}{\vdash(t+0)=t} \quad \texttt{suc}
$$

```mm
${                                                                                
  successor-lemma.1 $e |- t = S u $.                                                     
  successor-lemma.2 $e |- ( u + 0 ) = u $.                                               
  successor-lemma $p |- ( t + 0 ) = t $=                                                          
    nt n0 nadd nu nS nt nt n0 nadd nu nS n0 nadd nu n0 nadd nS nu nS nt nu nS n0           
    successor-lemma.1 addeq1i nu n0 add-sl nu n0 nadd nu successor-lemma.2 suceqi 3eqtri                 
    successor-lemma.1 eqtr4i $.                                                          
$}                                                                                
1p0e1 $p |- ( 1 + 0 ) = 1 $=                                                      
  n1 n0 df-1 00id successor-lemma $.                                                              
2p0e2 $p |- ( 2 + 0 ) = 2 $=                                                      
  n2 n1 df-2 1p0e1 successor-lemma $.                                                             
3p0e3 $p |- ( 3 + 0 ) = 3 $=                                                      
  n3 n2 df-3 2p0e2 successor-lemma $. 
```

So now how do we write a theorem $(t+0)=t$? This is called [`addrid`](https://us.metamath.org/mpeuni/addrid.html) rather than `tp0et`.
We just need to apply our successor-lemma t times, but try as we might, we can't seem to do it.

```mm
addrid $p |- ( t + 0 ) = t $= ? $.
```

Soon we convince ourselves, we can't prove it at all! Saying "we can't prove it" is a metatheorem,
which we haven't built the skills for yet, but some comments from my novice perspective:

Suppose we introduce some constant `num e`, 
such that the axiom or theorem `|- -. ( e + 0 ) = e` is satisfied. Of course, `|- ( 0 + e ) = e` also
holds, because that's an axiom of system $A$. If we can prove or argue that this system is consistent, and that
the system $A$ is also consistent, then it can only be the case that `|- ( t + 0 ) = t` cannot be 
proved by system $A.$ 

My impression is that proofs like this are not really out of place in the first few weeks of a good introduction
to logic course at the advanced undergraduate level. We're shelving it because at present, it is a "human brain
as a proof checker" topic, which we want to avoid.
The fact remains that we cannot prove `addrid`, 
yet for any finite $t$ we can construct a proof that $(t+0)=t.$ 
What we're missing is induction.

### 5.0.3 Induction without quantifiers

Here we're surely forced to use quantifiers, right? Nope!

Mathematical induction is usually phrased as the rule[^6][^7]

[^4]: I omit the use of turnstiles
because I'm not yet talking about a Metamath essential hypothesis with typecode `|-`.

[^5]: Troelstra and van Dalen's 1988 *Constructivism in Mathematics: An Introduction*, p. 120, writes
$A(0),\quad A(x)\to A(Sx)\quad\Rightarrow\quad A(t),$
while Troelstra and Schwichtenberg's 2000 *Basic Proof Theory*, p. 128 writes
$$\frac{\Gamma\vdash A(0)\qquad \Gamma\vdash A(x)\to A(Sx)}{\Gamma\vdash A(t)},
\qquad x\notin\operatorname{FV}(\Gamma). $$
Both formulations assume that $A$ is quantifier-free.

$$\frac{\varphi(0)\quad \varphi(x)\to \varphi(Sx)}{\varphi(t)},$$

where somehow we have to treat $\varphi(x)$ as well-formed formula which is a function of $x.$ 
This issue of treating $\varphi$ as a `wff` depending on a variable is the first place
that I encountered the need for disjoint variables.

Say our well-formed formula is $\varphi,$ which takes the value `r + 0 = r`.
If we try to "replace $r$ with zero" in the usual Metamath sense, we'll just unify the
whole expression for phi as `phi := 0 + 0 = 0`. Its status as a formula is lost, 
and it will no longer be able to be unified with other expressions like our induction hypothesis,
`( x + 0 ) = x -> ( S x + 0 ) = S x`. 

How do we solve this? Let's start with a theorem that "substitutes in" zero for x and shows
the formula holds:

```mm
$c var $.
$v x $.
vx $f var x $.
nx $a num x $.
xzero $p |- ( x = 0 -> ( x + 0 ) = x ) $=
  vx nx n0 weq vx nx n0 nadd n0 vx nx vx nx n0 weq vx nx n0 nadd n0 n0 nadd n0
  vx nx n0 n0 addeq1 n0 n0 nadd n0 weq vx nx n0 weq n0 add-0l a1i eqtrd
  vx nx n0 eq-sym eqtrd $.
```

Two notes:

- It's not of much consequence yet, but the trick with defining `x` as a `var` makes it so that
we can't substitute numbers. I'm purposefully restricting `xzero` so that it doesn't prove `1 = 0 -> ( 1 + 0 ) = 1`.
- If we had developed our axioms from scratch, here is where
we might find we missed a few axioms! For this to work, our axioms had to be powerful enough to allow for 
interactions like this where we "substitute" the value just by applying axioms.

In general, if we want to "substitute in" the `num t` for the `var x`, we should do the following:

$$x=t\to (\varphi\leftrightarrow\psi)$$

We could implement it in Metamath as follows (compare to [`vtocl`](https://us.metamath.org/mpeuni/vtocl.html)):

```mm
${ $( don't use this code, it's intentionally broken :) $)
  vtonum.1 $e |- ( x = t -> ( ph <-> ps ) ) $.
  vtonum.2 $e |- ph $.
  vtonum $a |- ps $.
$}
```

This looks good, but we can now prove `|- 1 = 0`. Why? Take `ph := x = x`, `t := 0`, `ps := x = 0`.
We conclude `|- x = 0`. A second application of `vtonum` with `ph := x = 0`, `t := 1`, and `ps := 1 = 0` 
concludes `|- 1 = 0`. Oops. This is a failure caused by $\psi$ still containing the variable $x$ after 
we substituted for $x.$

We can prove $1=0$ a different way. Put `ph := 0 = 0`, `t := x + 1`, and `ps := 1 = 0`.
We conclude `|- 1 = 0`.
This is a failure caused by trying to assign `x` a value that depends on `x`.[^8]

[^8]: Technically this requires us to prove `-. x = x + 1`, which in our axioms and 
[even in Robinson arithmetic](https://math.stackexchange.com/a/1066378) can't be done. 
So this is unsound provided we want to work in an arithmetic where `-. x = x + 1`.

One way to view these failures is that we're thinking of `vtonum` wrong. Rather than "substituting into a function",
we really should think of it as *eliminating* a variable from a formula. All of our woes are solved by 
requiring that $\psi$ and $t$ contain no instances of $x.$
This is accomplished by using the `$d ... $.` statement.

```mm
${ 
  $d x ps $. $d x t $.
  vtonum.1 $e |- ( x = t -> ( ph <-> ps ) ) $.
  vtonum.2 $e |- ph $.
  vtonum $a |- ps $.
$}
```

*Now*, we can begin to construct our induction axiom.
We have a formula $\varphi$ which we think of as a function of `var x`. We have a base case,
$\varphi(0)$ which I will call $\psi$. The conclusion of our rule, $\varphi(t)$ which can 
be evaluated at any `num t`, I'll call $\tau.$ The naming and ordering of the 
essential hypotheses is something we inherit from `set.mm` by the way, don't blame me 
for it![^9]

[^9]: An example of this is [nnind](https://us.metamath.org/mpeuni/nnind.html).

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

Next our induction hypothesis. We don't want $\varphi(y)\to \varphi(y+1)$ to unify
with some specific `num y`, so `y` has to be a var as well. 
We evaluate at y (call the wff $\chi$), evaluate at y+1 (call the wff $\theta$), 
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
Number one is "System $A$ + primitive-recursive functions + quantifier-free induction." This can be 
denoted $\text{PRA}_{\text{qf}}.$ This is the system in which stating the twin prime conjecture 
cannot be easily done, and it's discussed in Feferman 1993[^6]. On the other hand, many authors (most authors?) use PRA to refer to a system
with predicate calculus, but with induction restricted to quantifier-free formulas. This is 
$\text{PRA}_{\text{fo}},$ "System $A$ + primitive-recursive functions + predicates + induction
restricted to quantifier-free formulas." Both these systems are defined and compared in Avigad 2002[^7].


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