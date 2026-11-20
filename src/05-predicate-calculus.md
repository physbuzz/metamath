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

(I should emphasize to logicians reading
this section that we're coming at the issue from the perspective of Metamath tinkerers
with total disregard for mathematics, we just want to express fun concepts and we don't
care how we twist Metamath to get there. So I hope that explains some of the weird perspective
from time to time. I do try to bend over backwards to cite stuff and follow conventions of
the literature though.)

Before getting to predicate calculus, we should spend a bit of time
seeing how far we can get "without quantifiers." This question and related
ones such as "why do we need quantifiers?" takes us quite deep into metamathematics
and the debates of the early 1900's. I wasn't even trying to get there, I was just
confused, and certain I'd turn the corner and be hit with "aha! So *that's* why we need
quantifiers."

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
If we're given an obfuscated Metamath database with the variables all renamed, we can't easily
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
TODO: I'm still reading Frege's Begriffsschrift, I believe this is the motivation given in there.

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
Though I don't use them, it also contains nand, xor, and probably other stuff, I wasn't picky.

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
$\texttt{zos}$ (which is read as "every number is Zero Or a Successor", as opposed to $\texttt{zns}$ which 
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

TODO: replace this, probably with a proof of the successor lemma.

```
MM-PA> show new_proof/lemmon
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
steps 25, 28, 35.

$$(1+0)=(S0+0)=S(0+0)=S0.$$

And the only reason we don't add `S0=1` at the end of that chain is that we haven't defined a `4eqtri`.
So the proof strategy for this is to first write out the chain of equalities you want to make, and then puzzle out
how to build each one from the axioms.

Ok, it's a bit weird how this doesn't follow immediately from the axiom though. What about $(2+0)=2$ and $(3+0)=3$? Well, we
can figure out there's a common method to all these proofs. We define:

$$
\frac{\vdash t=Su\quad \vdash (u+0)=u}{\vdash(t+0)=t} \quad \texttt{successor-lemma}
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
holds, because that's an axiom of system $A$. If we can prove or argue that this system is consistent, 
then it can only be the case that `|- ( t + 0 ) = t` cannot be proved by system $A.$ Of course, $e$
isn't a natural number in any definition that mathematicians actually use, we've created a weird system
consistent with our axioms.

My impression is that proofs like this are not really out of place in the first few weeks of a good introduction
to logic course at the advanced undergraduate level. We're shelving it because at present, it is a "human brain
as a proof checker" topic, which we want to avoid.
The fact remains that we cannot prove `addrid`, 
yet for any finite $t$ we can construct a proof that $(t+0)=t.$ 
What we're missing is induction.

### 5.0.3 Induction without quantifiers

Here we're surely forced to use quantifiers, right? Nope!

Mathematical induction is usually phrased as the rule[^4][^5]

[^4]: I omit the use of turnstiles
because I'm not yet talking about a Metamath essential hypothesis with typecode `|-`.

[^5]: Troelstra and van Dalen's 1988 *Constructivism in Mathematics: An Introduction*, p. 120, writes
$A(0),\quad A(x)\to A(Sx)\quad\Rightarrow\quad A(t),$
while Troelstra and Schwichtenberg's 2000 *Basic Proof Theory*, p. 128 writes
$$\frac{\Gamma\vdash A(0)\qquad \Gamma\vdash A(x)\to A(Sx)}{\Gamma\vdash A(t)},
\qquad x\notin\operatorname{FV}(\Gamma). $$
Both formulations assume that $A$ is quantifier-free.

$$\frac{\varphi(0)\quad \varphi(x)\to \varphi(Sx)}{\varphi(t)},$$

where somehow we have to treat $\varphi(x)$ as a well-formed formula which is a function of $x.$ 
This issue of treating $\varphi$ as a `wff` depending on a variable is the first place
that I encountered the need for disjoint variables.

Say our well-formed formula is $\varphi,$ which takes the value `t + 0 = t`.
If we try to "replace $t$ with zero" in the usual Metamath sense, we'll just unify the
whole expression for phi as `phi := 0 + 0 = 0`. Its status as a formula is lost, 
and it will no longer be able to be unified with other expressions like our induction hypothesis,
`( x + 0 ) = x -> ( S x + 0 ) = S x`. 

How do we solve this? Let's start with a theorem that "substitutes in" zero for x and shows
the formula holds:

```mm
$c var $.
$v x y $.
vx $f var x $. vy $f var y $.
nx $a num x $. ny $a num y $.
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

To prove `addrid` we take `ph := ( x + 0 ) = x`. Evaluating it at $0,$ $y,$ $Sy$ and $t$
gives the other four wffs:

```
ps := ( 0 + 0 ) = 0
ch := ( y + 0 ) = y
th := ( S y + 0 ) = S y
ta := ( t + 0 ) = t
```

The six hypotheses we need to fill are:

```
|- ( x = 0 -> ( ( x + 0 ) = x <-> ( 0 + 0 ) = 0 ) )
|- ( x = y -> ( ( x + 0 ) = x <-> ( y + 0 ) = y ) )
|- ( x = S y -> ( ( x + 0 ) = x <-> ( S y + 0 ) = S y ) )
|- ( x = t -> ( ( x + 0 ) = x <-> ( t + 0 ) = t ) )
|- ( 0 + 0 ) = 0
|- ( ( y + 0 ) = y -> ( S y + 0 ) = S y )
```

The first four are of the same form, so it suffices to show a lemma:

```mm
addrid-at $p |- ( t = u -> ( ( t + 0 ) = t <-> ( u + 0 ) = u ) ) $=
  nt nu weq nt n0 nadd nu n0 nadd nt nu nt nu n0 addeq1 nt nu weq id eqeq12d $.
```

The base case is `00id`, which we used in the proof of `( 1 + 0 ) = 0` so that's easy.

Finally, the inductive step is essentially the same as `successor-lemma` above.
Combining all the steps give us our additive right identity, `addrid`:

```mm
addrid-step $p |- ( ( y + 0 ) = y -> ( S y + 0 ) = S y ) $=
  vy ny n0 nadd vy ny weq vy ny nS n0 nadd vy ny n0 nadd nS vy ny nS
  vy ny nS n0 nadd vy ny n0 nadd nS weq vy ny n0 nadd vy ny weq vy ny n0 add-sl a1i
  vy ny n0 nadd vy ny weq vy ny n0 nadd vy ny vy ny n0 nadd vy ny weq id suceqd
  eqtrd $.

${
  $d x t $. $d x y $.
  addrid $p |- ( t + 0 ) = t $=
    vx nx n0 nadd vx nx weq n0 n0 nadd n0 weq vy ny n0 nadd vy ny weq
    vy ny nS n0 nadd vy ny nS weq nt n0 nadd nt weq nt vx vy
    vx nx n0 addrid-at vx nx vy ny addrid-at vx nx vy ny nS addrid-at
    vx nx nt addrid-at 00id vy addrid-step ax-ind $.
$}
```

```
MM> show proof addrid /lemmon /renumber
1 addrid-at      $p |- ( x = 0 -> ( ( x + 0 ) = x <-> ( 0 + 0 ) = 0 ) )
2 addrid-at      $p |- ( x = y -> ( ( x + 0 ) = x <-> ( y + 0 ) = y ) )
3 addrid-at      $p |- ( x = S y -> ( ( x + 0 ) = x <-> ( S y + 0 ) = S y ) )
4 addrid-at      $p |- ( x = t -> ( ( x + 0 ) = x <-> ( t + 0 ) = t ) )
5 00id           $p |- ( 0 + 0 ) = 0
6 addrid-step    $p |- ( ( y + 0 ) = y -> ( S y + 0 ) = S y )
7 1,2,3,4,5,6 ax-ind  $a |- ( t + 0 ) = t
```

This proof is in `arith-qf.mm`:

@src(code-05/arith-qf.mm, noexecute, collapsed)

Okay, a fun way to spend a weekend or two might be to go extend proofs like this to all of Skolem's 1923 paper. 
We have built most of the conceptual groundwork, and "primitive-recursive functions" I don't think require
heavy machinery, they just tell us what kinds of functions we're going to define (introducing heavy machinery
to lint or build PRFs is up to you, but strictly speaking there's no need).
But for us, we're done, we've seen how we can apply induction.

### 5.0.4 Induction with quantifiers

Okay, now how do we introduce quantifiers? There's a few different
ways to do this which I'll put in an appendix 5.0.4b.
One difficulty of the system we introduced in 5.0.3 is described in 
Jean van Heijenoort's preface to a translation of Skolem's 1923 paper, where
it's mentioned that our version of PRA cannot easily phrase things like the twin prime
conjecture, because the "existence" of a pair is difficult to phrase. It's 
technically possible to state in our language without proving, but would
require substantial partial results related to the conjecture.
But in first-order logic it's easy to state.

We're going to get all of our quantifier practice done in sections 
5.1 and 5.2. So this section is going to be a bit brief, I'm just going to
show you what works and assert that it works, without getting too in detail.


For our induction axiom, we're going to use a single formula:

$$\frac{}{\vdash (\varphi(0)\land\forall y\,(\varphi(y)\to\varphi(Sy)))\to\forall x\,\varphi(x)}$$

This is basically the [`induction`](https://github.com/metamath/set.mm/blob/develop/peano.mm#L798) axiom of [peano.mm](https://github.com/metamath/set.mm/blob/develop/peano.mm).
Our goal is to start from `arith-common.mm` and see what axioms we need to introduce.
We'll definitely keep the same `var x` machinery. We introduce 
A. for $\forall$ and E. for $\exists$. E. is defined in terms of A., so its 
properties will be mostly elaborated on in lemmas and theorems.

```mm
$c A. E. $.
wal $a wff A. x ph $.
wex $a wff E. x ph $.
df-ex $a |- ( E. x ph <-> -. A. x -. ph ) $.
```

The symbols, as discussed in Megill, are given meaning through Tarski's axioms:

$$\frac{\vdash\varphi}{\vdash\forall x\varphi}\quad\href{https://us.metamath.org/mpeuni/ax-gen.html}{\texttt{ax-gen}}\qquad
\frac{}{\vdash\forall x(\varphi\to\psi)\to(\forall x\varphi\to\forall x\psi)}\quad\href{https://us.metamath.org/mpeuni/ax-4.html}{\texttt{ax-4}}$$

$$
\frac{}{\vdash\varphi\to\forall x\varphi} \;(x\text{ not in }\varphi)\quad\href{https://us.metamath.org/mpeuni/ax-5.html}{\texttt{ax-5}}\qquad
\frac{}{\vdash\exists x\,(x=t)}\;(x\text{ not in }t)\quad\href{https://us.metamath.org/mpeuni/ax6ev.html}{\texttt{ax-6}}
$$

```mm
${
  ax-gen.1 $e |- ph $.
  ax-gen $a |- A. x ph $.
$}
ax-4 $a |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $.
${
  $d x ph $.
  ax-5 $a |- ( ph -> A. x ph ) $.
$}
${
  $d x t $.
  ax-6 $a |- E. x x = t $.
$}
```

And our induction axioms copy peano.mm's axioms, but with a syntax more like `set.mm`. There
are a whole bunch of ways we could write this btw.

```mm
${
  $d x y $. $d y ph $.
  ax-peano $a |- ( ( A. x ( x = 0 -> ph )
      /\ A. y ( A. x ( x = y -> ph ) -> A. x ( x = S y -> ph ) ) ) -> A. x ph ) $.
$}
```

And actually, that's enough!! We can define induction as before, but as a theorem now:

```mm

${
  $d x ps $. $d x ch $. $d x th $. 
  $d x ta $. $d x t $.
  $d x y $. $d y ph $.
  ind.at-zero $e |- ( x = 0 -> ( ph <-> ps ) ) $.
  ind.at-var $e |- ( x = y -> ( ph <-> ch ) ) $.
  ind.at-succvar $e |- ( x = S y -> ( ph <-> th ) ) $.
  ind.at-num $e |- ( x = t -> ( ph <-> ta ) ) $.
  ind.base $e |- ps $.
  ind.step $e |- ( ch -> th ) $.
  ind $p |- ta $= ? $.
$}
```

The proof is the longest we encountered yet.

```
MM> show proof ind /lemmon /renumber
 1 ind.base      $e |- ps
 2 ind.at-zero   $e |- ( x = 0 -> ( ph <-> ps ) )
 3 2 biimprd     $p |- ( x = 0 -> ( ps -> ph ) )
 4 1,3 mpi       $p |- ( x = 0 -> ph )
 5 4 ax-gen      $a |- A. x ( x = 0 -> ph )
 6 eq-refl       $a |- y = y
 7 eqeq1         $p |- ( x = y -> ( x = y <-> y = y ) )
 8 ind.at-var    $e |- ( x = y -> ( ph <-> ch ) )
 9 7,8 imbi12d   $p |- ( x = y -> ( ( x = y -> ph ) <-> ( y = y -> ch ) ) )
10 9 spcv        $p |- ( A. x ( x = y -> ph ) -> ( y = y -> ch ) )
11 6,10 mpi      $p |- ( A. x ( x = y -> ph ) -> ch )
12 ind.step      $e |- ( ch -> th )
13 11,12 syl     $p |- ( A. x ( x = y -> ph ) -> th )
14 ax-5          $a |- ( th -> A. x th )
15 ind.at-succvar  $e |- ( x = S y -> ( ph <-> th ) )
16 15 biimprd    $p |- ( x = S y -> ( th -> ph ) )
17 16 com12      $p |- ( th -> ( x = S y -> ph ) )
18 17 alimi      $p |- ( A. x th -> A. x ( x = S y -> ph ) )
19 14,18 syl     $p |- ( th -> A. x ( x = S y -> ph ) )
20 13,19 syl     $p |- ( A. x ( x = y -> ph ) -> A. x ( x = S y -> ph ) )
21 20 ax-gen     $a |- A. y ( A. x ( x = y -> ph ) -> A. x ( x = S y -> ph ) )
22 ax-peano      $a |- ( ( A. x ( x = 0 -> ph ) /\ A. y ( A. x ( x = y -> ph )
                                     -> A. x ( x = S y -> ph ) ) ) -> A. x ph )
23 5,21,22 mp2an  $p |- A. x ph
24 ind.at-num    $e |- ( x = t -> ( ph <-> ta ) )
25 24 spcv       $p |- ( A. x ph -> ta )
26 23,25 ax-mp   $a |- ta
```

The key command here is to use `mp2an`, which allows us to get `|- ch` from `|- ( ( ph /\ ps ) -> ch )`
when the antecedents hold. Compare it to `set.mm`'s proof of 
[`nn0ind`](https://us.metamath.org/mpeuni/nn0ind.html).

Okay, the whole source file is here:

@src(code-05/arith-fo.mm, noexecute, collapsed)

#### 5.0.4.1 Alternate considerations to writing the induction scheme

There were a few issues in figuring out what axioms to use for section 5.0.4. 
We really want something that leads us to a beautiful illustration of how
quantifiers fit together in a beautifully engineered system.

Option 1 was to try to follow `set.mm`. Right, this is the approach, 
"well we can do induction from inside MPE, let's just copy that!" 
But actually, induction here, [`peano5`](https://us.metamath.org/mpeuni/peano5.html) depends 
on the construction of the 
natural numbers in terms of sets, and the ZFC axioms Extensionality, Separation,
Empty Set, Pairing, Union.

Option 2 would be to have as an axiom something that demonstrates the ability for
quantifiers to be inside a formula, such as a deductive form of induction:

$$\frac{\vdash(\psi\to \phi(0))\quad\vdash(\psi\to\forall(\phi(y)\to\phi(S y)))}{\vdash(\psi\to\forall\phi(x))}$$


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

### 5.1.1 Lift an implication

> [!WARNING]
> This section is AI-generated and has not been reviewed.

Work in [pred-5-1.mm](code-05/pred-5-1.mm) with [prop.mm](code-05/prop.mm) beside it. Prove [`mpg`](https://us.metamath.org/mpeuni/mpg.html) and [`alimi`](https://us.metamath.org/mpeuni/alimi.html). The first combines generalization with modus ponens. The second lets you take an implication you already proved in chapter 4 and put `A. x` on both sides. Prove [`al2im`](https://us.metamath.org/mpeuni/al2im.html) and [`al2imi`](https://us.metamath.org/mpeuni/al2imi.html) for an implication with two antecedents. That version comes up in the very next proof.

```metamath
${
  mpg.1 $e |- ( A. x ph -> ps ) $.
  mpg.2 $e |- ph $.
  mpg $p |- ps $= ? $.
$}

${
  alimi.1 $e |- ( ph -> ps ) $.
  alimi $p |- ( A. x ph -> A. x ps ) $= ? $.
$}

al2im $p |- ( A. x ( ph -> ( ps -> ch ) ) -> ( A. x ph -> ( A. x ps -> A. x ch ) ) ) $= ? $.

${
  al2imi.1 $e |- ( ph -> ( ps -> ch ) ) $.
  al2imi $p |- ( A. x ph -> ( A. x ps -> A. x ch ) ) $= ? $.
$}
```

### 5.1.2 Collect the conjuncts

> [!WARNING]
> This section is AI-generated and has not been reviewed.

Prove [`alanimi`](https://us.metamath.org/mpeuni/alanimi.html) and [`19.26`](https://us.metamath.org/mpeuni/19.26.html). The first lets you reuse a chapter 4 theorem that takes a conjunction as its hypothesis. The second is theorem ∗10.22 of *Principia Mathematica*. Saying that everyone satisfies both conditions is equivalent to saying that everyone satisfies each condition separately. One direction uses `alimi` twice. The other is what `alanimi` is for.

```metamath
${
  alanimi.1 $e |- ( ( ph /\ ps ) -> ch ) $.
  alanimi $p |- ( ( A. x ph /\ A. x ps ) -> A. x ch ) $= ? $.
$}

19.26 $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ A. x ps ) ) $= ? $.
```

### 5.1.3 Split a quantified biconditional

> [!WARNING]
> This section is AI-generated and has not been reviewed.

Prove [`albi`](https://us.metamath.org/mpeuni/albi.html) and its inference form [`albii`](https://us.metamath.org/mpeuni/albii.html). The payoff is being able to rewrite inside `A. x` whenever you have proved the old and new formulas equivalent. Finish with [`albiim`](https://us.metamath.org/mpeuni/albiim.html), where the chapter 4 equivalence you want to use sits inside the quantifier and the distribution law you just proved does the rest.

```metamath
albi $p |- ( A. x ( ph <-> ps ) -> ( A. x ph <-> A. x ps ) ) $= ? $.

${
  albii.1 $e |- ( ph <-> ps ) $.
  albii $p |- ( A. x ph <-> A. x ps ) $= ? $.
$}

albiim $p |- ( A. x ( ph <-> ps ) <-> ( A. x ( ph -> ps ) /\ A. x ( ps -> ph ) ) ) $= ? $.
```

## 5.2 Working inside `set.mm`

> [!WARNING]
> This section is AI-generated and has not been reviewed.

Open the [working copy of set.mm](code-05/set.mm). For each exercise, find the label, clear its proof, and write your own using the theorems available at that point in the file.

### 5.2.1 Carry an existential witness

> [!WARNING]
> This section is AI-generated and has not been reviewed.

Prove [`eximi`](https://us.metamath.org/mpeuni/eximi.html), the existential counterpart of `alimi`, and try it on chapter 4’s `ax-1` to get [`exa1`](https://us.metamath.org/mpeuni/exa1.html). Then prove [`19.29`](https://us.metamath.org/mpeuni/19.29.html). The interesting choice here is whether two facts can be combined into a fact about the same person. Knowing that someone satisfies each condition separately would leave that open. Here one condition holds for everyone.

```metamath
${
  eximi.1 $e |- ( ph -> ps ) $.
  eximi $p |- ( E. x ph -> E. x ps ) $= ? $.
$}

exa1 $p |- ( E. x ph -> E. x ( ps -> ph ) ) $= ? $.

19.29 $p |- ( ( A. x ph /\ E. x ps ) -> E. x ( ph /\ ps ) ) $= ? $.
```

### 5.2.2 Move implication under the quantifier

> [!WARNING]
> This section is AI-generated and has not been reviewed.

Prove [`19.35`](https://us.metamath.org/mpeuni/19.35.html). This is the hard problem in 5.2. Compare it with `19.26`. Distributing a universal quantifier over a conjunction gave two universal quantifiers. Moving an existential quantifier across an implication gives a universal on the left and an existential on the right. Proving both directions explains why that switch works. Then turn the reverse direction into [`19.35ri`](https://us.metamath.org/mpeuni/19.35ri.html) for the last exercise.

```metamath
19.35 $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> E. x ps ) ) $= ? $.

${
  19.35ri.1 $e |- ( A. x ph -> E. x ps ) $.
  19.35ri $p |- E. x ( ph -> ps ) $= ? $.
$}
```

### 5.2.3 The drinker paradox

> [!WARNING]
> This section is AI-generated and has not been reviewed.

Prove [`qexmid`](https://us.metamath.org/mpeuni/qexmid.html), the drinker paradox. In any nonempty tavern there is someone such that, if that person drinks, everyone drinks. Try picking that person by hand first, both in a tavern where everyone drinks and in one where someone abstains. The formal proof is short once you recognize which instance of `19.35ri` says what you need.

```metamath
qexmid $p |- E. x ( ph -> A. x ph ) $= ? $.
```
