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

### 5.0.1 Common arithmetic axioms

We next can imagine developing arithmetic. Well, no need to develop this all ourselves,
the best source for the axioms of arithmetic that I found was Peters 2022,
["Gödel’s Theorem Without Tears,"](https://www.ps.uni-saarland.de/~peters/bachelor/resources/thesis.edited.pdf#page=33) definition 4.16 p.23.
We already know not to worry about the $\forall$ at the beginning of each formula:
a theorem scheme already holds for all variables we wish to substitute. The only odd
axiom out is $\texttt{zos},$ which is indeed specific to Robinson's arithmetic[^1].

[^1]: $\texttt{zos}$ is axiom CD in Peters' notation, I just found that I could never
remember to write $\texttt{ax-CD}$ in Metamath proofs.

\begin{center}
\begin{tabular}{cl}
\texttt{eq-refl} & $\forall x.\; x = x$ \\
\texttt{eq-sym} & $\forall xy.\; x = y \to y = x$ \\
\texttt{eq-tr} & $\forall xyz.\; x = y \to y = z \to x = z$ \\
\texttt{eq-s} & $\forall xy.\; x = y \to \sigma x = \sigma y$ \\
\texttt{eq-add} & $\forall xyzw.\; x = y \to z = w \to x + z = y + w$ \\
\texttt{eq-mul} & $\forall xyzw.\; x = y \to z = w \to x \cdot z = y \cdot w$ \\
\texttt{add-0l} & $\forall x.\; 0 + x = x$ \\
\texttt{add-sl} & $\forall xy.\; (\sigma x) + y = \sigma(x + y)$ \\
\texttt{mul-0l} & $\forall x.\; 0 \cdot x = 0$ \\
\texttt{mul-sl} & $\forall xy.\; (\sigma x) \cdot y = y + x \cdot y$ \\
\texttt{zns} & $\forall x.\; 0 \ne \sigma x$ \\
\texttt{zos} & $\forall x.\; x = 0 \lor (\exists y.\; x = \sigma y)$ \\
\texttt{s-inj} & $\forall xy.\; \sigma x = \sigma y \to x = y$ \\
\end{tabular}
\end{center}

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
  subnum.1 $e |- ( x = t -> ( ph <-> ps ) ) $.
  subnum.2 $e |- ph $.
  subnum $a |- ps $.
$}
```

It looks good, but in fact we can now prove `|- 1 = 0`. Why? Take `ph := x = x`, `t := 0`, `ps := x = 0`.
We conclude `|- x = 0`. A second application of `subnum` with `ph := x = 0`, `t := 1`, and `ps := 1 = 0` 
concludes `|- 1 = 0`.

What went wrong? In our first application of `subnum`, an $x$ was leftover in our formula even though
we were supposed to be substituting for $x$! The problem is that we allowed the variable $x$ to occur
anywhere in $\psi$. This is exactly what the disjoint variable restriction, `$d ... $.` prevents:

```mm
${ 
  $d x ps $. $d x t $.
  subnum.1 $e |- ( x = t -> ( ph <-> ps ) ) $.
  subnum.2 $e |- ph $.
  subnum $a |- ps $.
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



SCRATCHWORK BELOW HERE



We need to evaluate it at $r=0,$ $r=t,$ $r=t+1,$ and $r=s,$ because these are the 
four places we evaluate $P$ in our induction inference rule. Let's take the $r=0$ case and say 
that $\varphi$ assumes the value $\psi$ at $r=0.$ Well, the phrasing "if r=0 then phi equals psi"
is very suggestive, so we might want to say
$(r=0)\to(\psi\leftrightarrow\varphi).$ The intent of this is to say
that at zero, the wff $\phi$ takes on value $\psi.$ Well, there's one issue here right off the bat: $\psi$ could
also contain the metavariable $r$. No problem, we've been saving just the tool for that! 


Okay, converting to metamath-pseudocode:

```mm
${
  ax-ind.1 $e P ( 0 ) $.
  ax-ind.2 $e P ( t ) -> P ( S t ) $.
  ax-ind $a P ( u )
$}
```



While it could be natural to do so, I'm drawing the line somewhere!! This is not a full 
development of arithmetic from scratch. We simply want to see an axiom that is sufficient to 
prove our theorem using induction. 





Alright, let's try to put this into Metamath form. We're going to have essential hypotheses, so
we'll have something like:

```mm
${
  ax-ind.1 $e ... $.
  ax-ind $a TODO
$}
```


Our proposition, $\varphi,$ is $t+0=t.$ To evaluate this proposition at zero, we care about the 
statement $t=0\to \varphi$

[AI SECTION BEGIN]

More precisely, we need to distinguish a formula from a formula with an
argument singled out for substitution. If $P(x)$ is $x+0=x$, we want to
relate it to $P(0)$, which is $0+0=0$. Metamath has no built-in operation
`ph(0)` for doing this. An equality guard such as `x = 0` can help, but it
matters what we allow in the position occupied by `x`.

Here is a small example before we tackle induction. Suppose we have proved

$$x=0\to\psi,$$

where $x$ does not occur in $\psi$. Since this is a theorem for arbitrary
$x$, it holds when $x$ has value zero. Therefore $\psi$ holds. Changing the
value of $x$ does not change $\psi$, precisely because $x$ does not occur
there. This motivates the following theorem-to-theorem rule:

```mm
${
  $d x ps $.
  at-zero.1 $e |- ( x = 0 -> ps ) $.
  at-zero $a |- ps $.
$}
```

This is a proposed extra rule, not something we already get from
propositional logic. It illustrates one operation we might want when
working with equality guards: after proving `x = 0 -> P(0)`, we can remove
the guard, because the instance `P(0)` no longer contains `x`.

Now suppose we declared `nx $f num x $.`. This would let us substitute
`S 0` for `x`. Choose `ps` to be `S 0 = 0`. The premise becomes

```text
|- ( S 0 = 0 -> S 0 = 0 )
```

which is just an instance of `id`! The rule would then conclude

```text
|- S 0 = 0
```

The `$d` condition does not prevent this: both substituted expressions
contain only constants. The argument for the rule has broken because
`S 0` cannot take the value zero. A position intended for an independently
varying variable has accepted a fixed arithmetic expression.

To prevent this, give individual variables their own type, with a rule
allowing them to be used as arithmetic terms:

```mm
$c var $.
$v x y $.
vx $f var x $.
vy $f var y $.
nvar $a num x $.
```

There is no rule constructing `var 0` or `var S t`. Thus `at-zero` now
requires a variable in its `x` position, and the bad application above
fails: we can prove `num S 0`, but cannot prove `var S 0`.

The rule `nvar` is essential to using these variables in equations. Given
the existing syntax rule `weq $a wff t = u $.`, whose arguments have type
`num`, we can prove:

```mm
eq-vars $p wff x = y $= vx nvar vy nvar weq $.
```

The two uses of `nvar` supply `num x` and `num y`; `weq` then supplies
`wff x = y`. Likewise, `vx nvar n0 weq` proves `wff x = 0`. These syntax
proofs can appear directly inside other proofs; we need not give each one
a separate theorem label.

Declaring a variable to have type `num` is perfectly appropriate for the
arithmetic rules we already have. The trouble arises when we use that
type for a position whose intended job is to identify a variable we can
vary or substitute for. The combination of `var`, `nvar`, and `$d` gives
us a small amount of machinery for that job. We can then build the
induction rule using proofs that connect the zero, variable, successor,
and target instances of our property.

[AI SECTION END]

Since I'm a novice I should clarify the ", I'm relying on the observation that these theorems
use induction inside `set.mm`, and AI claims (TODO: strengthen citation?). I believe that the
statement, "it holds for every $S^n 0,$ but we cannot prove it" can be demonstrated by introducing some
constant `num e` such that in fact, `-. ( e + 0 ) = e` though of course the axiom `( 0 + e ) = e` must hold.
If the resulting system is consistent -- an argument which I don't know how to make -- then of course
we shouldn't be able to prove $t+0=t$ because it's not true in this weird new system!


Hmm... 

Granted, for any given numbers we can prove $n+m=m+n$ (or rather, $(S^n 0+S^m 0)=(S^m 0+S^n 0)$),
but we can't seem to prove the general theorem scheme. A more simple and pointed example is
that we're given $0 + x = x,$ but we can't seem to prove the 


which 
This gives us a concrete reason to introduce quantifiers!!!




# Scratchwork

```mm
$( Representative arithmetic helpers; the propositional library of set.mm
   is available, including mp2, mp2d, syl, syl5, syl6, com12, and com23. $)

$( Inference form: detach both premises with mp2. $)
${
  eq-tri.1 $e |- t = u $.
  eq-tri.2 $e |- u = v $.
eq-tri $p |- t = v $=
  nt nu weq nu nv weq nt nv weq eq-tri.1 eq-tri.2 nt nu nv eq-tr mp2 $.
$}

$( Equality transitivity: deduction form. $)
${
  eq-trans-d.1 $e |- ( ph -> t = u ) $.
  eq-trans-d.2 $e |- ( ph -> u = v ) $.
eq-trans-d $p |- ( ph -> t = v ) $=
  wph nu nv weq nt nv weq eq-trans-d.2 wph nt nu weq nu nv weq nt nv weq wi
  eq-trans-d.1 nt nu nv eq-tr syl mpd $.
$}

$( Equality transitivity: closed form with the premises exchanged by com12. $)
eq-tr-com $p |- ( u = v -> ( t = u -> t = v ) ) $=
  nt nu weq nu nv weq nt nv weq nt nu nv eq-tr com12 $.

$( Equality symmetry: inference form. $)
${
  eq-symi.1 $e |- t = u $.
eq-symi $p |- u = t $=
  nt nu weq nu nt weq eq-symi.1 nt nu eq-sym ax-mp $.
$}

$( Equality symmetry: deduction form. $)
${
  eq-sym-d.1 $e |- ( ph -> t = u ) $.
eq-sym-d $p |- ( ph -> u = t ) $=
  wph nt nu weq nu nt weq eq-sym-d.1 nt nu eq-sym syl $.
$}

$( Successor congruence: inference form. $)
${
  eq-si.1 $e |- t = u $.
eq-si $p |- S t = S u $=
  nt nu weq nt nS nu nS weq eq-si.1 nt nu eq-s ax-mp $.
$}

$( Successor congruence: deduction form. $)
${
  eq-succ-d.1 $e |- ( ph -> t = u ) $.
eq-succ-d $p |- ( ph -> S t = S u ) $=
  wph nt nu weq nt nS nu nS weq eq-succ-d.1 nt nu eq-s syl $.
$}

$( Congruence in the left argument: closed form. $)
eq-add-left $p |- ( t = u -> ( t + v ) = ( u + v ) ) $=
  nv nv weq nt nu weq nt nv nadd nu nv nadd weq wi nv eq-refl nt nu weq nv nv
  weq nt nv nadd nu nv nadd weq nt nu nv nv eq-add com12 ax-mp $.

$( Congruence in the right argument: closed form. $)
eq-add-right $p |- ( t = u -> ( v + t ) = ( v + u ) ) $=
  nv nv weq nt nu weq nv nt nadd nv nu nadd weq wi nv eq-refl nv nv nt nu
  eq-add ax-mp $.

$( Inference form: detach both premises with mp2. $)
${
  eq-add-i.1 $e |- t = u $.
  eq-add-i.2 $e |- v = w $.
eq-add-i $p |- ( t + v ) = ( u + w ) $=
  nt nu weq nv nw weq nt nv nadd nu nw nadd weq eq-add-i.1 eq-add-i.2 nt nu nv
  nw eq-add mp2 $.
$}

$( Joint congruence: deduction form. $)
${
  eq-add-d.1 $e |- ( ph -> t = u ) $.
  eq-add-d.2 $e |- ( ph -> v = w ) $.
eq-add-d $p |- ( ph -> ( t + v ) = ( u + w ) ) $=
  wph nv nw weq nt nv nadd nu nw nadd weq eq-add-d.2 wph nt nu weq nv nw weq
  nt nv nadd nu nw nadd weq wi eq-add-d.1 nt nu nv nw eq-add syl mpd $.
$}

$( Congruence in the left argument: closed form. $)
eq-mul-left $p |- ( t = u -> ( t * v ) = ( u * v ) ) $=
  nv nv weq nt nu weq nt nv nmul nu nv nmul weq wi nv eq-refl nt nu weq nv nv
  weq nt nv nmul nu nv nmul weq nt nu nv nv eq-mul com12 ax-mp $.

$( Congruence in the right argument: closed form. $)
eq-mul-right $p |- ( t = u -> ( v * t ) = ( v * u ) ) $=
  nv nv weq nt nu weq nv nt nmul nv nu nmul weq wi nv eq-refl nv nv nt nu
  eq-mul ax-mp $.

$( Inference form: detach both premises with mp2. $)
${
  eq-mul-i.1 $e |- t = u $.
  eq-mul-i.2 $e |- v = w $.
eq-mul-i $p |- ( t * v ) = ( u * w ) $=
  nt nu weq nv nw weq nt nv nmul nu nw nmul weq eq-mul-i.1 eq-mul-i.2 nt nu nv
  nw eq-mul mp2 $.
$}

$( Joint congruence: deduction form. $)
${
  eq-mul-d.1 $e |- ( ph -> t = u ) $.
  eq-mul-d.2 $e |- ( ph -> v = w ) $.
eq-mul-d $p |- ( ph -> ( t * v ) = ( u * w ) ) $=
  wph nv nw weq nt nv nmul nu nw nmul weq eq-mul-d.2 wph nt nu weq nv nw weq
  nt nv nmul nu nw nmul weq wi eq-mul-d.1 nt nu nv nw eq-mul syl mpd $.
$}

$( Two terms equal to the same term are equal. $)
${
  eq-common-i.1 $e |- t = v $.
  eq-common-i.2 $e |- u = v $.
eq-common-i $p |- t = u $=
  nt nv nu eq-common-i.1 nu nv eq-common-i.2 eq-symi eq-tri $.
$}

$( Addition congruence in one argument: inference form. $)
${
  eq-add-righti.1 $e |- t = u $.
eq-add-righti $p |- ( v + t ) = ( v + u ) $=
  nt nu weq nv nt nadd nv nu nadd weq eq-add-righti.1 nt nu nv eq-add-right
  ax-mp $.
$}

$( Compose congruence lemmas to replace a term inside a larger expression. $)
eq-add-mul $p |- ( t = u -> ( ( t + v ) * w ) = ( ( u + v ) * w ) ) $=
  nt nu weq nt nv nadd nu nv nadd weq nt nv nadd nw nmul nu nv nadd nw nmul
  weq nt nu nv eq-add-left nt nv nadd nu nv nadd nw eq-mul-left syl $.

$( Cancel matching successors, in both directions. $)
ss-eq $p |- ( S S t = S S u <-> t = u ) $=
  nt nS nS nu nS nS weq nt nu weq nt nS nS nu nS nS weq nt nS nu nS weq nt nu
  weq nt nS nu nS s-inj nt nu s-inj syl nt nu weq nt nS nu nS weq nt nS nS nu
  nS nS weq nt nu eq-s nt nS nu nS eq-s syl impbii $.

$( A successor is not zero. $)
snz $p |- -. S t = 0 $=
  nt nS n0 weq n0 nt nS weq nt zns nt nS n0 eq-sym mto $.

$( Calculation step: from t + u = v, obtain S t + u = S v. $)
${
  add-stepi.1 $e |- ( t + u ) = v $.
add-stepi $p |- ( S t + u ) = S v $=
  nt nS nu nadd nt nu nadd nS nv nS nt nu add-sl nt nu nadd nv add-stepi.1
  eq-si eq-tri $.
$}

$( Calculation step: from t * u = v and u + v = w, obtain S t * u = w. $)
${
  mul-stepi.1 $e |- ( t * u ) = v $.
  mul-stepi.2 $e |- ( u + v ) = w $.
mul-stepi $p |- ( S t * u ) = w $=
  nt nS nu nmul nu nv nadd nw nt nS nu nmul nu nt nu nmul nadd nu nv nadd nt
  nu mul-sl nt nu nmul nv nu mul-stepi.1 eq-add-righti eq-tri mul-stepi.2
  eq-tri $.
$}

$( One plus an arbitrary term. $)
add-1l $p |- ( S 0 + t ) = S t $=
  n0 nS nt nadd n0 nt nadd nS nt nS n0 nt add-sl n0 nt nadd nt nt add-0l eq-si
  eq-tri $.

$( Two plus an arbitrary term, using the preceding lemma. $)
add-2l $p |- ( S S 0 + t ) = S S t $=
  n0 nS nS nt nadd n0 nS nt nadd nS nt nS nS n0 nS nt add-sl n0 nS nt nadd nt
  nS nt add-1l eq-si eq-tri $.

$( A nested sum with an arbitrary term. $)
add-2-3-term $p |- ( S S 0 + ( S S S 0 + t ) ) = ( S S S S S 0 + t ) $= ? $.

$( 3 + 2 = 5: one application of the addition-step rule. $)
add-3-2-value $p |- ( S S S 0 + S S 0 ) = S S S S S 0 $=
  n0 nS nS n0 nS nS n0 nS nS nS nS add-2-2-value add-stepi $.

$( 2 + 3 = 5: one application of the addition-step rule. $)
add-2-3-value $p |- ( S S 0 + S S S 0 ) = S S S S S 0 $=
  n0 nS n0 nS nS nS n0 nS nS nS nS add-1-3-value add-stepi $.

$( Combine two evaluations with the common-value equality rule. $)
add-3-2 $p |- ( S S S 0 + S S 0 ) = ( S S 0 + S S S 0 ) $=
  n0 nS nS nS n0 nS nS nadd n0 nS nS n0 nS nS nS nadd n0 nS nS nS nS nS
  add-3-2-value add-2-3-value eq-common-i $.

$( 2 * 3 = 6: one application of the multiplication-step rule. $)
mul-2-3-value $p |- ( S S 0 * S S S 0 ) = S S S S S S 0 $=
  n0 nS n0 nS nS nS n0 nS nS nS n0 nS nS nS nS nS nS mul-1-3-value
  add-3-3-value mul-stepi $.

$( 3 * 2 = 6: one application of the multiplication-step rule. $)
mul-3-2-value $p |- ( S S S 0 * S S 0 ) = S S S S S S 0 $=
  n0 nS nS n0 nS nS n0 nS nS nS nS n0 nS nS nS nS nS nS mul-2-2-value
  add-2-4-value mul-stepi $.

$( Combine two evaluations with the common-value equality rule. $)
mul-2-3 $p |- ( S S 0 * S S S 0 ) = ( S S S 0 * S S 0 ) $=
  n0 nS nS n0 nS nS nS nmul n0 nS nS nS n0 nS nS nmul n0 nS nS nS nS nS nS
  mul-2-3-value mul-3-2-value eq-common-i $.

$( Transport a known inequality along a proved equation. $)
${
  neq-replace.1 $e |- t = u $.
  neq-replace.2 $e |- -. u = v $.
neq-replace $p |- -. t = v $=
  nt nv weq nu nv weq neq-replace.2 nu nt weq nt nv weq nu nv weq wi nt nu
  neq-replace.1 eq-symi nu nt nv eq-tr ax-mp mto $.
$}

$( Two is not one. $)
neq-2-1 $p |- -. S S 0 = S 0 $=
  n0 nS nS n0 nS weq n0 nS n0 weq n0 snz n0 nS n0 s-inj mto $.

$( 1 + 1 = 2: one application of the addition-step rule. $)
add-1-1-value $p |- ( S 0 + S 0 ) = S S 0 $=
  n0 n0 nS n0 nS add-0-1-value add-stepi $.

$( Combine the calculation and inequality lemmas: one plus one is not one. $)
neq-1p1-1 $p |- -. ( S 0 + S 0 ) = S 0 $=
  n0 nS n0 nS nadd n0 nS nS n0 nS add-1-1-value neq-2-1 neq-replace $.

$( Two is not three. $)
neq-2-3 $p |- -. S S 0 = S S S 0 $=
  n0 nS nS n0 nS nS nS weq n0 n0 nS weq n0 zns n0 nS nS n0 nS nS nS weq n0 nS
  n0 nS nS weq n0 n0 nS weq n0 nS n0 nS nS s-inj n0 n0 nS s-inj syl mto $.

$( One times t reduces to t + 0, before induction. $)
mul-1l-base $p |- ( S 0 * t ) = ( t + 0 ) $=
  n0 nS nt nmul nt n0 nt nmul nadd nt n0 nadd n0 nt mul-sl n0 nt nmul n0 weq
  nt n0 nt nmul nadd nt n0 nadd weq nt mul-0l n0 nt nmul n0 nt eq-add-right
  ax-mp eq-tri $.

$( Two times t reduces to t + ( t + 0 ), before induction. $)
mul-2l-base $p |- ( S S 0 * t ) = ( t + ( t + 0 ) ) $=
  n0 nS nS nt nmul nt n0 nS nt nmul nadd nt nt n0 nadd nadd n0 nS nt mul-sl n0
  nS nt nmul nt n0 nadd weq nt n0 nS nt nmul nadd nt nt n0 nadd nadd weq nt
  mul-1l-base n0 nS nt nmul nt n0 nadd nt eq-add-right ax-mp eq-tri $.
```


# Old article






From what I understand, 

So we take 

```mm
$( Terms and equations. $)
$c num = + * 0 S $.
$v t u v w $.
nt $f num t $.  nu $f num u $.  nv $f num v $.  nw $f num w $.
weq $a wff t = u $.
n0 $a num 0 $.
nS $a num S t $.
nadd $a num ( t + u ) $.
nmul $a num ( t * u ) $.

$( Peters, Definition 4.16, p. 23: equality in his printed order. $)
eq-ER $a |- t = t $.
eq-ES $a |- ( t = u -> u = t ) $.
eq-ET $a |- ( t = u -> ( u = v -> t = v ) ) $.
eq-CS $a |- ( t = u -> S t = S u ) $.
eq-CA $a |- ( t = u -> ( v = w -> ( t + v ) = ( u + w ) ) ) $.
eq-CM $a |- ( t = u -> ( v = w -> ( t * v ) = ( u * w ) ) ) $.
```


whose premises and conclusion don't involve quantifiers,
but whose proof involves quantifiers, there exists a proof of the theorem without quantifiers.

 Metamath is too broad of a system to easily make statements like

I think that from a truly obstinate Metamath-first approach, *at this point in our education*,
we can only say that "using quantifiers" and "not using quantifiers"
refer to the human estimation and opinion about a Metamath database. To formalize
"a formal system does or doesn't have quantifiers", we would first, for example, formalize what
a formal system is inside `set.mm`.



Does it simply mean with or without the disjoint variable restriction?


 not English language philosophizing and that we're really doing something concrete. 
I'm c

 insisting as using Metamath as a foundation in order to avoid the English language
struggles I see in class so often. 


If I use Metamath as my foundation, though,
I'm confronted with a bit of an issue... What does "without quantifiers" mean? 
The only syntax feature I haven't used yet is the disjoint variable restriction, 
so perhaps that's it? 

 So indeed the class of logics that Metamath allows us to 
talk about is quite large, which means that if we're creative enough we could certainly
make very expressive systems that don't follow the usual development of `set.mm`, or 
apply obfuscation tricks to the point where it's unclear if we are or are not "using quantifiers". 


So far we (or I) have been a bit myopic on propositional logic. So we have to remind
ourselves that we can introduce new symbols and new axioms. 

For example, the fundamentals of arithmetic:

```mm
$v t u v$.
nt $f num t $.  nu $f num u $.  nv $f num v $.
weq $a wff t = u $.
n0 $a num 0 $.
nS $a num S t $.
eq-refl $a |- t = t $.
eq-sym $a |- ( t = u -> u = t ) $.
eq-tr $a |- ( t = u -> ( u = v -> t = v ) ) $.
eq-S $a |- ( t = u -> S t = S u ) $.
```





- This is [Hilbert and Bernays' First Epsilon Theorem](TODO) In any first order logic, for theorems whose premises and conclusion don't involve quantifiers,
but whose proof involves quantifiers, there exists a proof of the theorem without quantifiers.
This is [Hilbert and Bernays' First Epsilon Theorem](TODO). This is quite broad, but I don't have
the expertise to cast it into a statement about "any Metamath database of a specific form."
- https://plato.stanford.edu/entries/peirce-logic/
- https://plato.stanford.edu/entries/logical-consequence/
- https://www.andrew.cmu.edu/user/avigad/Papers/understanding2.pdf
- https://concrete-semantics.org/
- https://plato.stanford.edu/entries/proof-theoretic-semantics/
- WHAT NUMBERS COULD NOT BE
- https://ncatlab.org/nlab/show/quantification

Okay, so there's a tremendous amount left to do to answer the question "why quantifiers?"
I feel that, in this presentation, we just haven't built up the tools to motivate it
as a platonic ideal of some kind. So we have to build it up by the more conventional route,
by recognizing the social phenomenon that mathematicians say a lot of things using quantifiers,
and we want to use quantifiers too. 

"But wait!" You object, "mathematicians use the concept of discharging a hypothesis, and we gave 
that up too. Why not quantifiers?" Well, like, I don't know man, but quantifiers are pretty nice 
aren't they?


## 5.0 

### 5.0.1 An example database without predicates.


Well, mathematicians say a lot of things with the concept of "discharging a hypothesis," and we
seemed to do fine without that, but okay, quantifiers is something we won't give up so easily.

To start with, a metatheorem is already essentially a universal quantifier, the statement
`$p |- P ( x ) $.` could easily be read as "$\forall x P(x)$". But what we're missing is quantifiers
inside assertions, especially $\neg \forall x P(x).$ Implication, nesting, etc. is also 
troublesome. In order to express these things. 

 as it's a "for all" statement.
But we struggle when we want to write "not ()


Thus, *we* have three reasons to introduce quantifiers:

1. Mathematicians 

1. Mathematicians (and us) want to express theorems and assumptions in terms of quantifiers.

2. perhaps we find that we cannot express the theorems that we want without quantifiers or;
3. perhaps we find that we cannot apply the proof strategies we want without quantifiers.


will refer to specific judgements of 

Okay, so 

I could mean "without disjoint variable restrictions," but then we 

If we keep asking fundamental questions about *why* we are developing the particular brand of logic
that we're developing, we quickly wind up back at the debates of the late 19th and early 20th century.
I don't have the expertise to cover things in such detail, so -- as always -- take what I say with a 
grain of salt! 

Before getting to predicate calculus, I found it necessary to spend a bit of time on
*why* we introduce quantifiers to logic. Three different possibilities come to mind:

1. Perhaps we find that we express a theorem in our new system, built on top of propositional calculus, 
which we cannot prove without quantifiers;

The answer appears to be points 2 and 3. For point 1, I'm told this is ruled out by Hilbert and Bernay's first
epsilon theorem, as well as Herbrand's theorem. These theorems basically say that if the assumptions and 
conclusions of a theorem don't contain quantifiers, we can always eliminate quantifiers from its proof. 
However I couch my words in "it appears to be" and "I'm told" because
we're very creative people, and I worry that Metamath makes it very easy to create nonstandard
systems of logic which lay outside the purview of these theorems. Since we can't formalize those issues right now,
we'll have to stow any subtleties about point 1 and just assume that points 2 and 3 are what we want.
Personally I did f







So, we have a few problems with introducing quantified logic. 

The problem with introducing quantified logic is explained well in the Metamath book,

but I'll write a bit to make it more concrete.

Consider Metamath's `ax-5`: 
```mm
$c 0 1 2 + num = $. 
$v x y z $.
nx $f num x $.
ny $f num y $.
nz $f num z $.
npl $a num ( x + y ) $.
weq $a wff x = y $.

foo-1 $a ( x + 0 ) = 0 $.
foo-2 $a 0 + 1 = 0 $.
${
  $d x ph $.
  ax-5 $a |- ( ph -> A. x ph ) $.
$}
```

If we ignore the `$d` symbol, and also say we've introduced equality `=` which 

Consider Metamath's 

The problem with introducing quantified logic is as follows.

Say we tried to define quantified logic ourselves. Okay, 


 Supposing we have 
$\forall x \varphi(x,y).$ 

Required reading:

- Tarski 1964, *[A Simplified Nomalization of Predicate Logic with Identity](http://eudml.org/doc/137772)*.
- Megill 1995, *[A Finitely Axiomatized Formalization of Predicate Calculus with Equality](doi.org/10.1305/ndjfl/1040149359)*.

### Notes on Tarski 1964

So, the 

### Notes on Megill 1995





> [!CAUTION]
> This document is completely AI-generated and has not been reviewed. 

## AI Slop

Okay, now for the disjoint variables. In chapter 4 I wanted to get a feel for
classical logic by actually proving things in Metamath. Here I want to do the
same thing with quantifiers, while finally dealing with the variable restrictions
that I could mostly ignore in the propositional exercises. There is some new
terminology to learn, but the plan is to keep bringing it back to particular
strings, particular substitutions, and particular proofs.

One question from chapter 4 is especially useful here: how do we change a
formula deep inside another formula? With quantifiers this becomes a very
concrete question. If I've proved an implication or an equivalence, what theorem
lets me put a universal quantifier around it? And if I want to change the name
of a bound variable, what actually authorizes that change? I want to get far
enough that these are proof steps I can carry out.

Section 5.1 continues our own implication-and-negation development with a small
quantifier toolkit. Section 5.2 introduces the richer interfaces in `set.mm`
and practices reconstructing proofs there, followed by a separate Peano excursion.

## 5.0 Important Notations, Terminology, and Citations

### 5.0.1 Variables in which language?

There is an easy way to get confused before we've even started: the word
"variable" is doing several jobs. In an ordinary first-order formula, a variable
can occur as an argument of a predicate or be bound by a quantifier. In a
textbook's discussion of those formulas, a metavariable can stand for a whole
formula. Metamath then has its own declared variables and type hypotheses. I
want to keep track of which of these we're discussing, instead of relying on
the typography to tell us.

**Source 1.** The [Metamath book](https://us.metamath.org/downloads/metamath.pdf),
especially §1.4.5, "Metamath and First-Order Logic," and §4.2.4, "The `$d`
Statement." The latter starts on printed page 120. The important point for our
purposes is that the verifier does not have a primitive free-variable or
bound-variable test. Its substitution mechanism and `$d` conditions are used
by an axiom system to control the substitutions that are permitted.

For example, `ph` has type `wff` in our familiar database, while `x` has type
`setvar` in the predicate-calculus portion of `set.mm`. Both are Metamath
variables. An instance of `ph` may be a large formula containing several
`setvar` variables; an instance of `x` must satisfy its own syntax hypothesis.
The declaration `vx $f setvar x $.` belongs to the syntax machinery. It is not
itself a quantified assertion about a mathematical set.

This also explains why a condition involving `x` and `ph` can make sense. We are
restricting which replacements for two Metamath variables can be used together.
The [Proof Explorer's discussion of axioms, schemes, and distinct
metavariables](https://us.metamath.org/mpeuni/mmset.html#distinct) is useful to
read alongside the book here.

### 5.0.2 Free occurrences, bound occurrences, and capture

**Source 2.** Harper's [Practical Foundations for Programming
Languages](https://www.cs.cmu.edu/~rwh/pfpl/), Chapter 1. His treatment of abstract
syntax and binding gives us terminology for talking about these problems
outside a particular Metamath database. The sustained reading of Harper is
going in the separate O5.5 notebook; here I just want enough vocabulary to
describe the examples in front of us.

Consider the familiar formula

$$x=y\ \to\ \forall x\,(x=y).$$

The occurrence of `x` on the left is free, while the occurrence of `x` inside
the quantified equality is bound. The quantifier does not reach back across
the implication. This is why it is useful to talk about *occurrences*: one
written variable name can have different roles in different parts of a formula.

A substitution can change these roles if we're careless. For example, consider
replacing the free `x` in

$$\forall y\,(x=y)$$

by `y`. Simply changing the printed letter gives

$$\forall y\,(y=y).$$

The newly inserted occurrence is now inside the scope of the `y` quantifier.
This is the sort of phenomenon called variable capture. A treatment of
capture-avoiding substitution must say how it handles this situation; in a
named-variable presentation, renaming a bound variable is one way to make the
required room.

Two expressions that differ only by a suitable change of bound-variable names
are called alpha-equivalent in the usual binding terminology. I'll use that
name when discussing the syntax. For the actual predicate-calculus exercises,
we will prove particular logical equivalences using named `set.mm` theorems.
Those are concrete things to check, and they give us something to compare with
the general discussion in Harper.

### 5.0.3 Tarski and the distinct-variable approach

**Source 3.** The Proof Explorer's [history of distinct
variables](https://us.metamath.org/mpeuni/mmset.html#distinct). It credits Tarski
with stating the approach in 1951, with proofs published in 1965. The historical
point I want to remember is the possibility of organizing predicate calculus
around comparatively elementary distinct-variable restrictions, while deriving
the more elaborate behavior within the system.

The comment on [`ax-5`](https://us.metamath.org/mpeuni/ax-5.html) gives a direct
connection to Tarski's system. It asserts

$$\vdash\bigl(\varphi\to\forall x\,\varphi\bigr),$$

with the condition that `x` does not occur in the substituted formula. In
Metamath source, that restriction is written `$d x ph $.`. This is a good
historical example to keep attached to an actual axiom we will use, instead of
remembering only that Tarski did something clever with variables.

There is a tradeoff to notice: making the verifier's primitive operation small
does not make every familiar logical manipulation a primitive operation.
Changing bound variables, specializing a quantified formula, or transporting
an equivalence still needs the relevant assertions and their proofs. That is
the machinery we will borrow and practice using in this chapter.

### 5.0.4 What `$d` asks the checker to do

The exact rule in §4.2.4 of the [book](https://us.metamath.org/downloads/metamath.pdf)
has two parts. When applying an assertion with a required disjoint pair, the
two replacement expressions must have no Metamath variables in common. Also,
every pair consisting of one variable from each replacement must be covered
by the active disjoint conditions in the proof. The second part is how the
restriction is inherited.

For a small example, suppose an assertion requires `$d ph ps $.`, and consider
the replacements `ph` by `x = y` and `ps` by `z = w`. The variables occurring
in the two replacements are disjoint as written. The proof still needs the
cross-pairs `x,z`, `x,w`, `y,z`, and `y,w`. It does not acquire a requirement
that `x` and `y` be distinct from each other from this particular `$d` pair.
We're checking pairs across the two replacements.

If instead both replacements contain `y`, there is an immediate conflict.
Declaring extra pairs cannot repair that overlap. On the other hand, identical
replacements containing only constants do not conflict with this particular
test, because they contain no variables. Their syntax hypotheses still have
to be satisfied, of course. These are checks on substitution data, so we can
practice them before making a large predicate-calculus proof.

The [discussion attached to `19.21v`](https://us.metamath.org/mpeuni/19.21v.html)
also gives a useful terminology distinction: "does not occur" is stronger
than "is not free in." For instance, `x` is not free in `A. x x = x`, but it
certainly occurs there. That formula therefore cannot be used as the
replacement for `ph` in a direct application of `ax-5` with `x` as the bound
variable. There are other theorems for less restrictive situations.

## 5.1 Building Predicate Calculus Ourselves

> [!WARNING]
> AI-generated, not human-reviewed. Reference solutions have been checked by Metamath.

### 5.1.1 Our starting tools

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

### 5.2.5 A Small Visit to `peano.mm`

#### 5.2.5.1 A separate language and its axioms

Use `ai/predicate-calculus/peano-exercises.mm` in a separate Metamath session.
It uses the actual syntax and selected axioms of [the local peano.mm](code/peano.mm),
with all supporting derived rules included. The completed file is
`ai/predicate-calculus/peano-reference.mm`. Its labels are independent of the
predicate file, even where a familiar propositional name is reused.

```sh
metamath 'read "ai/predicate-calculus/peano-exercises.mm"'
make -C ai/predicate-calculus verify
```

This language uses Polish notation: `= + 0 x x` means $0+x=x$,
`implies phi psi` is implication, and `forall x phi` is universal
quantification. A `var` can be made into a `term` with `tvar`; an arbitrary
term cannot be substituted for a `var`. In particular, `pa_ax3` and `pa_ax4`
have variable arguments. Getting a zero into their first argument requires
a proved substitution step.

These are all the declarations and primitive assertions used in this file.
`bi1`, `bi2`, and `bi3` really are axioms in `peano.mm`; their status is
different from the corresponding derived biconditional rules in 5.1.
The displayed `induction` is also the source database's actual axiom.

```metamath
$c + 0 = BINOP BINPRED LOGBINOP QUANT S and forall iff implies not term var wff |- $.
$v binop binpred ch chi logbinop ph phi ps psi quant s s0 s1 t t0 t1 ta th u v x y z $.
ts $f term s $.
tt $f term t $.
tu $f term u $.
ts0 $f term s0 $.
ts1 $f term s1 $.
tt0 $f term t0 $.
tt1 $f term t1 $.
varv $f var v $.
varx $f var x $.
vary $f var y $.
varz $f var z $.
binop_ $f BINOP binop $.
logbinop_ $f LOGBINOP logbinop $.
binpred_ $f BINPRED binpred $.
quant_ $f QUANT quant $.
wff_phi $f wff phi $.
wff_psi $f wff psi $.
wff-chi $f wff chi $.
wph $f wff ph $.
wps $f wff ps $.
wch $f wff ch $.
wth $f wff th $.
wta $f wff ta $.
```

```metamath
binop_plus $a BINOP + $.

tvar $a term v $.

tzero $a term 0 $.

tsucc $a term S s $.

tbinop $a term binop s t $.

logbinopand $a LOGBINOP and $.

logbinopimplies $a LOGBINOP implies $.

logbinopiff $a LOGBINOP iff $.

binpred_equals $a BINPRED = $.

quant_all $a QUANT forall $.

wff_atom $a wff binpred s t $.

wff_not $a wff not psi $.

wff_logbinop $a wff logbinop psi phi $.

wff_quant $a wff quant v phi $.

ax-1 $a |- implies phi implies psi phi $.

ax-2 $a |- implies implies phi implies psi chi implies implies phi psi implies phi chi $.

ax-3 $a |- implies implies not phi not psi implies psi phi $.

${
  ax-mp.h1 $e |- phi $.
  ax-mp.h2 $e |- implies phi psi $.
  ax-mp $a |- psi $.
$}

bi1 $a |- implies iff phi psi implies phi psi $.

bi2 $a |- implies iff phi psi implies psi phi $.

bi3 $a |- implies implies phi psi implies implies psi phi iff phi psi $.

df-an $a |- iff and phi psi not implies phi not psi $.

eq-refl $a |- = t t $.

eq-sym $a |- implies = s t = t s $.

eq-trans $a |- implies and = s t = t u = s u $.

eq-congr $a |- implies and = s0 s1 = t0 t1 iff binpred s0 t0 binpred s1 t1 $.

eq-suc $a |- implies = s t = S s S t $.

eq-binop $a |- implies and = s0 s1 = t0 t1 = binop s0 t0 binop s1 t1 $.

${
  $d phi x $.
  alpha_1.h1 $e |- implies phi iff psi chi $.
  alpha_1 $a |- implies phi iff quant x psi quant x chi $.
$}

${
  $d phi x $.
  alpha_2.h1 $e |- implies phi chi $.
  alpha_2 $a |- implies phi forall x chi $.
$}

${
  $d t x $.
  all_elim $a |- implies forall x phi forall x implies = x t phi $.
$}

${
  $d chi x $.
  $d t x $.
  all_elim3.h1 $e |- implies = x t iff phi chi $.
  all_elim3 $a |- implies forall x implies = x t phi chi $.
$}

pa_ax3 $a |- = x + x 0 $.

pa_ax4 $a |- = S + x y + x S y $.

${
  $d phi x $.
  $d x y $.
  induction $a |- implies and forall y implies = y 0 phi forall x implies forall y implies = y x phi
    forall y implies = y S x phi forall x forall y implies = y x phi $.
$}
```

#### 5.2.5.2 Supplied logical and equality tools

The next ledger supplies the implication machinery in this language.
The proofs of the rules involving only implication and negation are
translations of the local `set.mm` proofs. `wn` and `wi` are derived syntax
bridges to `wff_not` and `wff_logbinop`; they introduce no new axioms.
`jca` passes through `df-an` using `jc`, while `pair` applies the same
conjunction introduction to two established assertions.

<details>
<summary>Supplied tools and their exact interfaces</summary>

```metamath
wn $p wff not ph $= ... $.

wi $p wff implies ph ps $= ... $.

${
  a1i.h1 $e |- ph $.
  a1i $p |- implies ps ph $= ... $.
$}

${
  a2i.h1 $e |- implies ph implies ps ch $.
  a2i $p |- implies implies ph ps implies ph ch $= ... $.
$}

${
  mpd.h1 $e |- implies ph ps $.
  mpd.h2 $e |- implies ph implies ps ch $.
  mpd $p |- implies ph ch $= ... $.
$}

${
  syl.h1 $e |- implies ph ps $.
  syl.h2 $e |- implies ps ch $.
  syl $p |- implies ph ch $= ... $.
$}

id $p |- implies ph ph $= ... $.

idd $p |- implies ph implies ps ps $= ... $.

${
  a1d.h1 $e |- implies ph ps $.
  a1d $p |- implies ph implies ch ps $= ... $.
$}

${
  a2d.h1 $e |- implies ph implies ps implies ch th $.
  a2d $p |- implies ph implies implies ps ch implies ps th $= ... $.
$}

${
  sylcom.h1 $e |- implies ph implies ps ch $.
  sylcom.h2 $e |- implies ps implies ch th $.
  sylcom $p |- implies ph implies ps th $= ... $.
$}

${
  syl5com.h1 $e |- implies ph ps $.
  syl5com.h2 $e |- implies ch implies ps th $.
  syl5com $p |- implies ph implies ch th $= ... $.
$}

${
  com12.h1 $e |- implies ph implies ps ch $.
  com12 $p |- implies ps implies ph ch $= ... $.
$}

${
  syl5.h1 $e |- implies ph ps $.
  syl5.h2 $e |- implies ch implies ps th $.
  syl5 $p |- implies ch implies ph th $= ... $.
$}

${
  syl6.h1 $e |- implies ph implies ps ch $.
  syl6.h2 $e |- implies ch th $.
  syl6 $p |- implies ph implies ps th $= ... $.
$}

${
  syl2im.h1 $e |- implies ph ps $.
  syl2im.h2 $e |- implies ch th $.
  syl2im.h3 $e |- implies ps implies th ta $.
  syl2im $p |- implies ph implies ch ta $= ... $.
$}

pm2.27 $p |- implies ph implies implies ph ps ps $= ... $.

${
  mpdd.h1 $e |- implies ph implies ps ch $.
  mpdd.h2 $e |- implies ph implies ps implies ch th $.
  mpdd $p |- implies ph implies ps th $= ... $.
$}

${
  pm2.43i.h1 $e |- implies ph implies ph ps $.
  pm2.43i $p |- implies ph ps $= ... $.
$}

${
  imim2d.h1 $e |- implies ph implies ps ch $.
  imim2d $p |- implies ph implies implies th ps implies th ch $= ... $.
$}

imim2 $p |- implies implies ph ps implies implies ch ph implies ch ps $= ... $.

${
  sylc.h1 $e |- implies ph ps $.
  sylc.h2 $e |- implies ph ch $.
  sylc.h3 $e |- implies ps implies ch th $.
  sylc $p |- implies ph th $= ... $.
$}

${
  syl6c.h1 $e |- implies ph implies ps ch $.
  syl6c.h2 $e |- implies ph implies ps th $.
  syl6c.h3 $e |- implies ch implies th ta $.
  syl6c $p |- implies ph implies ps ta $= ... $.
$}

${
  syldd.h1 $e |- implies ph implies ps implies ch th $.
  syldd.h2 $e |- implies ph implies ps implies th ta $.
  syldd $p |- implies ph implies ps implies ch ta $= ... $.
$}

${
  syl5d.h1 $e |- implies ph implies ps ch $.
  syl5d.h2 $e |- implies ph implies th implies ch ta $.
  syl5d $p |- implies ph implies th implies ps ta $= ... $.
$}

${
  imim12d.h1 $e |- implies ph implies ps ch $.
  imim12d.h2 $e |- implies ph implies th ta $.
  imim12d $p |- implies ph implies implies ch th implies ps ta $= ... $.
$}

${
  imim1d.h1 $e |- implies ph implies ps ch $.
  imim1d $p |- implies ph implies implies ch th implies ps th $= ... $.
$}

con4 $p |- implies implies not ph not ps implies ps ph $= ... $.

${
  con4d.h1 $e |- implies ph implies not ps not ch $.
  con4d $p |- implies ph implies ch ps $= ... $.
$}

${
  mt4d.h1 $e |- implies ph ps $.
  mt4d.h2 $e |- implies ph implies not ch not ps $.
  mt4d $p |- implies ph ch $= ... $.
$}

${
  pm2.21d.h1 $e |- implies ph not ps $.
  pm2.21d $p |- implies ph implies ps ch $= ... $.
$}

pm2.21 $p |- implies not ph implies ph ps $= ... $.

${
  jarli.h1 $e |- implies implies ph ps ch $.
  jarli $p |- implies not ph ch $= ... $.
$}

${
  pm2.18d.h1 $e |- implies ph implies not ps ps $.
  pm2.18d $p |- implies ph ps $= ... $.
$}

pm2.18 $p |- implies implies not ph ph ph $= ... $.

notnotr $p |- implies not not ph ph $= ... $.

${
  con2d.h1 $e |- implies ph implies ps not ch $.
  con2d $p |- implies ph implies ch not ps $= ... $.
$}

pm3.2im $p |- implies ph implies ps not implies ph not ps $= ... $.

${
  jc.h1 $e |- implies ph ps $.
  jc.h2 $e |- implies ph ch $.
  jc $p |- implies ph not implies ps not ch $= ... $.
$}

${
  biimpd.h1 $e |- implies ph iff ps ch $.
  biimpd $p |- implies ph implies ps ch $= ... $.
$}

${
  biimprd.h1 $e |- implies ph iff ps ch $.
  biimprd $p |- implies ph implies ch ps $= ... $.
$}

${
  impbidd.h1 $e |- implies ph implies ps ch $.
  impbidd.h2 $e |- implies ph implies ch ps $.
  impbidd $p |- implies ph iff ps ch $= ... $.
$}

${
  imbi1d.h1 $e |- implies ph iff ps ch $.
  imbi1d $p |- implies ph iff implies ps th implies ch th $= ... $.
$}

${
  jca.h1 $e |- implies ph ps $.
  jca.h2 $e |- implies ph ch $.
  jca $p |- implies ph and ps ch $= ... $.
$}

${
  pair.h1 $e |- ph $.
  pair.h2 $e |- ps $.
  pair $p |- and ph ps $= ... $.
$}
```

</details>

The remaining general-purpose tools make the arithmetic steps short enough
to inspect. `eq-trd` joins two equalities under an antecedent using `jca`
and `eq-trans`. `gen` derives generalization from `alpha_2` with the closed
true antecedent `= 0 0`, which is removed by modus ponens. `specialize`
composes `all_elim` and `all_elim3`; `subst` first applies `gen`, then the
same elimination steps. Both require an explicit proof of the equality
transport formula and the displayed freshness conditions.

```metamath
${
  eq-symi.h1 $e |- = s t $.
  eq-symi $p |- = t s $= ... $.
$}

${
  eq-trd.h1 $e |- implies ph = s t $.
  eq-trd.h2 $e |- implies ph = t u $.
  eq-trd $p |- implies ph = s u $= ... $.
$}

${
  gen.h1 $e |- ph $.
  gen $p |- forall x ph $= ... $.
$}

${
  $d ch x $.
  $d t x $.
  specialize.h1 $e |- forall x ph $.
  specialize.h2 $e |- implies = x t iff ph ch $.
  specialize $p |- ch $= ... $.
$}

${
  $d ch x $.
  $d t x $.
  subst.h1 $e |- ph $.
  subst.h2 $e |- implies = x t iff ph ch $.
  subst $p |- ch $= ... $.
$}
```

#### 5.2.5.3 Two preparatory arithmetic proofs

Prove the right-zero and successor equations with their equalities oriented
in the usual computational direction:

```metamath
add-zero-right $p |- = + x 0 x $= ? $.
```

```metamath
add-successor-right $p |- = + x S y S + x y $= ? $.
```

##### Hints

- `add-zero-right`: Apply eq-symi to pa_ax3 with s := x and t := + x 0.
- `add-successor-right`: Apply eq-symi to pa_ax4 with s := S + x y and t := + x S y.

#### 5.2.5.4 The base case and ordinary successor step

For the rest of this section, the prose abbreviates `= + 0 t t` by `P(t)`.
This abbreviation adds no syntax to the database. All targets below are
written out in full.

The supplied `base-substitution` transports the formula `= x + x 0` across
`= x 0`. Its checked proof uses `eq-binop` to transport the sum and
`eq-congr` to transport the equality. Use it to instantiate `pa_ax3` at zero.

```metamath
base-substitution $p |- implies = x 0 iff = x + x 0 = 0 + 0 0 $= ... $.
```

```metamath
zero-base $p |- = + 0 0 0 $= ? $.
```

The analogous supplied transport for `pa_ax4` uses a fresh `y` in its first
argument. `rec-substitution` uses `eq-binop` twice, and `eq-suc` for the
successor on the left. This is repetitive equality bookkeeping, so its
proof is supplied. The subsequent specialization is an exercise.

```metamath
rec-substitution $p |- implies = y 0 iff = S + y x + y S x = S + 0 x + 0 S x $= ... $.
```

```metamath
${
  $d x y $.
  zero-recursion $p |- = S + 0 x + 0 S x $= ? $.
$}
```

The ordinary induction step now follows by reversing `zero-recursion`,
transporting the induction hypothesis with `eq-suc`, and composing equalities:

```metamath
${
  $d x y $.
  zero-step $p |- implies = + 0 x x = + 0 S x S x $= ? $.
$}
```

##### Hints

- `zero-base`: Use subst on pa_ax3 and base-substitution with t := 0 and ch := = 0 + 0 0. Reverse the resulting equality using eq-symi.
- `zero-recursion`: Use subst on pa_ax4 with its x := y, y := x, and on rec-substitution. In subst choose x := y, t := 0, ch := = S + 0 x + 0 S x; the freshness pair is x,y.
- `zero-step`: Reverse zero-recursion with eq-symi, then add antecedent = + 0 x x with a1i. eq-suc gives the second branch; combine with eq-trd through S + 0 x.

#### 5.2.5.5 The quantified premises and induction application

The axiom uses the guarded formula
`G(t) = forall y implies = y t = + 0 y y`.
Its base premise is `G(0)`; its step premise is
`forall x implies G(x) G(S x)`. It concludes `forall x G(x)`.
Use `phi := = + 0 y y` in `induction`: its requirement `$d phi x $.`
becomes `$d y x $.`, already required by the other condition. This explains
why the displayed axiom uses a fresh induction variable instead of treating
`P(S x)` as a primitive substitution notation.

`guard-substitution` proves equality transport for `P`. Derive elimination
of `G(t)` from it:

```metamath
guard-substitution $p |- implies = y t iff = + 0 y y = + 0 t t $= ... $.
```

```metamath
${
  $d t y $.
  guard-elim $p |- implies forall y implies = y t = + 0 y y = + 0 t t $= ? $.
$}
```

For the reverse implication, `guard-intro` extracts the reverse direction
of the equivalence with `biimprd`, commutes the antecedents with `com12`,
and quantifies `y` with `alpha_2`. The condition `$d y t $.` ensures the
retained antecedent `P(t)` contains no `y`.

```metamath
${
  $d t y $.
  guard-intro $p |- implies = + 0 t t forall y implies = y t = + 0 y y $= ... $.
$}
```

Now prepare exactly the two quantified premises, join them, and apply
induction. Each stage is its own proof obligation:

```metamath
induction-base $p |- forall y implies = y 0 = + 0 y y $= ? $.
```

```metamath
${
  $d x y $.
  induction-step $p |- implies forall y implies = y x = + 0 y y forall y implies = y S x = + 0 y y $=
    ? $.
$}
```

```metamath
${
  $d x y $.
  induction-step-all $p |- forall x implies forall y implies = y x = + 0 y y forall y implies = y S x
    = + 0 y y $= ? $.
$}
```

```metamath
${
  $d x y $.
  induction-result $p |- forall x forall y implies = y x = + 0 y y $= ? $.
$}
```

##### Hints

- `guard-elim`: Apply all_elim3 to guard-substitution with x := y, phi := = + 0 y y and chi := = + 0 t t. The restriction is $d y t $.
- `induction-base`: Detach guard-intro at t := 0 using zero-base and ax-mp.
- `induction-step`: Chain guard-elim at t := x, zero-step, and guard-intro at t := S x with syl.
- `induction-step-all`: Apply gen to induction-step with its quantified variable x unchanged.
- `induction-result`: Use pair to join induction-base and induction-step-all. Detach induction with phi := = + 0 y y, retaining its x and y.

#### 5.2.5.6 Specializing the result without capture

The induction result still has an outer quantifier. Use a fresh `z` for its
bound name and specialize it to `x`. To justify this, transport the equality
guard `= y z` to `= y x`, then lift that equivalence through implication
and `forall y`. The generic rules `imbi1d` and `alpha_1` were supplied in
5.2.5.1–5.2.5.2; the following concrete transport is an exercise.

```metamath
${
  $d x y $.
  $d y z $.
  outer-substitution $p |- implies = z x iff forall y implies = y z = + 0 y y forall y implies = y x =
    + 0 y y $= ? $.
$}
```

```metamath
${
  $d x y $.
  $d x z $.
  $d y z $.
  zero-left $p |- = + 0 x x $= ? $.
$}
```

The distinctness conditions on `y` and `z` are internal conditions on the
auxiliary variables in the last proof. Only `x` occurs in its conclusion,
so a later application of `zero-left` does not acquire two additional
mandatory variable arguments.

##### Hints

- `outer-substitution`: Under = z x, use jca with eq-refl at y (lifted by a1i) and id; eq-congr gives iff = y z = y x. Apply imbi1d with common consequent = + 0 y y, then alpha_1 over y. Both y,z and y,x are required.
- `zero-left`: Use specialize on induction-result with x := z, plus outer-substitution; set the specializing variable to z and term to x. The result is forall y implies = y x = + 0 y y. Finish with guard-elim at t := x and ax-mp.


## 5.3 Notes, Reflections, and TODO

The main question I want to come back to is the one about changing a formula
inside another formula. We now have examples where an implication or
equivalence can be transported through a quantifier. I'd like to recognize
when this is the right approach, instead of trying to manipulate a substring
as though the verifier had a general rewrite command built into its logic.

There is a related distinction between carrying out a proof step and proving
something about a general proof transformation. In this chapter I can write a
particular bound-variable change and have the checker accept it. In the later
metamathematics chapter I want formulas, substitutions, and derivability to be
mathematical objects we can quantify over. That will let us formulate a much
wider claim precisely. For now, I can keep an explicit list of the claims I
would eventually like to state.

TODO: add personal notes after the exercises. Which `$d` failures were
surprising? Which helper made an apparently complicated proof easy? Did it
help to write the intended intermediate formula before asking the proof
assistant to fill in the details? These should be observations from actually
working the problems; there is no need to manufacture conclusions in advance.

The separate O5.5 reading notebook can hold the longer work through Harper's
first three chapters and Gaifman's notes. It should be useful to compare
Harper's language with the operations we've just performed, while keeping a
record of the parts that still need formalization.

## 5.4 Quiz Questions

These questions are meant to test the terminology and the mechanics that the
proof exercises use. The answers below are short sketches to revise after
working through the chapter.

### Question 1

In `( x = y -> A. x x = y )`, which occurrences of `x` and `y` are free, and which
are bound? Why is it more precise to ask about occurrences than simply to
classify each variable name as free or bound?

#### Answer sketch

The `x` in the left equality is free, and the `x` in the right equality is
bound by `A. x`; the `x` written immediately after `A.` names the binder.
Both equality occurrences of `y` are free. A single name can
occur in different scopes; the binding depends on the occurrence's location.

### Question 2

An assertion requires `$d ph ps $.`. We replace `ph` by `x = y` and `ps` by
`z = w`. Which inherited pairs are needed? Why isn't the fact that these are
four differently written letters enough?

#### Answer sketch

The cross-pairs are `x,z`, `x,w`, `y,z`, and `y,w`. The checker needs the
corresponding active restrictions. The distinct spellings by themselves do
not record which later substitutions the assertion permits.

### Question 3

Explain why `$d x y $.` is different from `|- -. x = y`. Also explain why
`$d x ph $.` is stronger than saying that `x` is not free in the formula.

#### Answer sketch

The first is a restriction on substitutions for Metamath variables; the second
is a mathematical assertion of inequality. For the formula case, nonoccurrence
excludes bound occurrences too. `A. x x = x` is a concrete example in which
`x` occurs but is not free.

### Question 4

What is variable capture? Describe what goes wrong with the naive replacement
of free `x` by `y` in `A. y x = y`, and explain the role that changing the bound
name can play in avoiding it.

#### Answer sketch

The inserted `y` falls within the scope of the existing `A. y` binder and
becomes bound. A suitable change to a fresh bound name can preserve the role
of the inserted occurrence. The admissibility of the change must be handled
by the chosen syntax rules or, in our exercises, by an appropriate theorem.

### Question 5

What is the historical connection between Tarski's work and Metamath's
distinct-variable approach? Name the source used for the dates.

#### Answer sketch

The Proof Explorer's history credits Tarski with stating the approach in
1951 and publishing proofs in 1965. The relevant idea is organizing an
axiomatization using distinct-variable conditions rather than requiring the
usual free-variable and proper-substitution machinery as primitive notions.

### Question 6

Compare `ax-gen` with `ax-5`. Why can't we simply turn the former into an
unrestricted theorem `|- ( ph -> A. x ph )`?

#### Answer sketch

`ax-gen` takes an established assertion as a premise and universally quantifies
it. The closed implication has a different logical claim. `ax-5` supplies that
implication under a disjoint-variable restriction, and the `ax-gen` commentary
explicitly warns that its unrestricted closed form need not hold.

### Question 7

Which tool would you look for if you had proved `ph <-> ps` and wanted
`A. x ph <-> A. x ps`? What changes if you instead have `ph -> ps` and want
`ph -> A. x ps`?

#### Answer sketch

The first is the pattern of `albii`. The second is the pattern of `alrimiv`,
whose disjointness condition constrains `ph` and `x`. In the first case both
sides are quantified; in the second the antecedent remains outside.

### Question 8

In the `rename-equality` exercise, why do we need to protect `z` as well as
distinguish `x` and `y`? What would a general theorem about alpha-renaming say
beyond this particular checked equivalence?

#### Answer sketch

Substituting the two equality formulas into `cbvalvw` produces the additional
pairs `x,z` and `y,z`. A general theorem about a specified renaming procedure
would quantify over represented expressions and the procedure's inputs or
outputs. This exercise supplies one checked instance using an existing rule.
