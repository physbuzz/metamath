
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






## Skolem 1923
[AI SPARKNOTES]

#### What to take away

Read this as a demonstration of how much arithmetic can be done with recursive
functions, recursive predicates, and induction. Skolem starts with addition and
gets as far as gcd, lcm, prime factorization, infinitely many primes, and finite
counting. He is developing arithmetic under a restriction on the kinds of
statements he uses. He is not proving that quantifiers can be removed from any
arithmetic theory we might write down.

The restriction is on unbounded *bound* variables. Free variables are welcome:
$a+b=b+a$ is one of his “functional assertions.” So our use of arbitrary terms
in theorem schemes is close to what he has in mind. He does not require us to
replace every theorem by a separate theorem about each numeral. Also,
“quantifier-free” does not mean “predicate-free”: much of the paper consists of
introducing predicates and proving things about them.

The editorial introduction explicitly says that this is not a fully specified
formal system. Skolem takes arithmetic reasoning and substitution of equals for
equals for granted. In `arith.mm`, those steps need actual rules and proofs.
That is part of our project, rather than something this paper has already
specified for us.

#### A short route through the paper

Links below open the [32-page extract](book/dontshare/skolem-1923-foundations-of-elementary-arithmetic.pdf#page=1).
The page numbers are for that extract; add 312 for the original van Heijenoort PDF.

1. Read the introduction and Skolem's opening, pp. 1–4. Separate the editor's
   explanation of later primitive recursive arithmetic from Skolem's own claims.
   The main question is how to replace a search over all numbers by a bounded
   computation. You can skim the discussion of “the author of Waverley.”

2. Read [§1, pp. 4–5](book/dontshare/skolem-1923-foundations-of-elementary-arithmetic.pdf#page=4)
   carefully. His first theorem is associativity of addition, followed by the
   lemma $a+1=1+a$, then commutativity. Each proof shows the same useful pattern:
   unfold a recursive definition, use the induction hypothesis inside a larger
   expression, and fold the definition back up. Notice which variable is being
   inducted on and which other variables remain arbitrary.

3. Read Definition 2 at the start of
   [§2, p. 5](book/dontshare/skolem-1923-foundations-of-elementary-arithmetic.pdf#page=5),
   then skim the order proofs. Read Theorems 10–13 in
   [§3, pp. 8–9](book/dontshare/skolem-1923-foundations-of-elementary-arithmetic.pdf#page=8)
   if you want multiplication examples: distributivity, associativity, the other
   distributive law, then commutativity. You don't need to formalize all the order
   lemmas before trying these algebraic proofs with our axioms.

4. Read the opening of
   [§4, pp. 9–11](book/dontshare/skolem-1923-foundations-of-elementary-arithmetic.pdf#page=9):
   Definitions 5–6 and the discussion after Theorem 20. This is the most useful
   part for our question about quantifiers. It explains both how to define
   divisibility by recursion and why proving a theorem about that predicate
   requires more than manipulating equations with supplied witnesses.

5. Jump to [§8, pp. 25–26](book/dontshare/skolem-1923-foundations-of-elementary-arithmetic.pdf#page=25).
   Skolem now allows finite logical sums and products as convenient notation,
   and the prime-number arguments become much shorter. Read Theorem 68 and its
   proof: a prime divisor of $n!+1$ must exceed $n$, so the search for the next
   prime has the explicit bound $n!+1$. The Markdown transcription loses the
   factorial in the theorem's displayed upper bound; the PDF has $n!+1$.

For later: §5 deals with partially defined subtraction and division; §6 defines
and proves properties of gcd and lcm, and explains stronger-looking forms of
recursion and induction; §7 develops primality and prime factorization in the
longer notation. The rest of §8 covers unique factorization, bounded least-number
search, and finite cardinality. Read the statements if curious; leave the proofs
for another project. Skolem's concluding remark on pp. 31–32 even says he finds
his own formal presentation too cumbersome.

A notation shortcut: for propositions, $AB$ means $A\land B$, $A+B$ means
$A\lor B$, and $\bar A+B$ means $A\to B$. An equality between propositions
expresses equivalence. Finite logical $\Sigma$ and $\Pi$ mean finite OR and AND.
Also, $D(a,b)$ means that $b$ divides $a$, not the other way around.

#### What to prove in `arith.mm`

Skolem starts at 1, with successor already written $a+1$, and defines addition
recursively in its second argument. We start at 0 and our `add-sl` recurses in
the first argument. Keep our conventions. A manageable sequence is:

1. $a+0=a$ (`add-0r`). Induct on $a$. This is the first check that the induction
   machinery from §5.0.3 can actually be used.
2. $a+S b=S(a+b)$. Again induct on $a$. This lets successor move through the
   other argument of addition, and will supply the commutativity step.
3. $(a+b)+c=a+(b+c)$. Induct on $a$, keeping $b,c$ arbitrary. This is Skolem's
   Theorem 1 with the induction variable changed to suit our recursion equations.
4. $a+b=b+a$. Induct on $a$. The base case uses `add-0r`; the step uses the
   successor lemma and the induction hypothesis:
   $$S a+b=S(a+b)=S(b+a)=b+S a.$$

Those four are enough for the first pass. They exercise induction, parameters,
equality substitution, and the reuse of lemmas. There is no need to formalize
Skolem's entire development to get those lessons. His intermediate lemma
$a+1=1+a$ is worth understanding, but need not become an extra milestone in our
zero-based version.

If you want one multiplication theorem, try $(a+b)c=ac+bc$, his Theorem 12.
With our `mul-sl`, induction on $a$ fits the definition; addition associativity
does the rearranging in the step. Leave multiplication commutativity until you
actually want it.

If you want one example about avoiding quantifiers, try his recursive definition
of $<$, rather than all of §§2–4. In our zero-based notation it becomes
$$a<0\;\leftrightarrow\;\bot,\qquad
  a<S b\;\leftrightarrow\;(a<b\lor a=b).$$
Then prove $a<S a$ and the transitivity of $<$ (his Theorem 3). This gives us
an actual predicate defined without an existential quantifier, followed by a
proof using its definition. Stop there unless divisibility itself has become
the next thing you want to study.

#### Why the divisibility section matters even if we don't formalize it

For positive integers, Skolem defines
$$\begin{aligned}
\Delta(a,b,1)&\leftrightarrow a=b,\\
\Delta(a,b,c+1)&\leftrightarrow\Delta(a,b,c)\lor a=b(c+1),\\
D(a,b)&\leftrightarrow\Delta(a,b,a).
\end{aligned}$$
Here $\Delta(a,b,c)$ checks whether one of the numbers $1,\ldots,c$ is a
multiplier taking $b$ to $a$. The bound $a$ suffices for divisibility because a
positive multiplier of $b$ giving $a$ cannot exceed $a$. This replaces an
existential statement by a recursively defined predicate. The finite search
can be very slow; efficiency is not the point.

After Theorem 20, he distinguishes two proofs we might otherwise conflate.
Given $a=bd$ and $b=ce$, showing $a=c(de)$ is a calculation with witnesses
already supplied. Proving $D(a,b)\land D(b,c)\to D(a,c)$ starts with predicates
that do not supply those witnesses as terms. His intermediate lemmas do the
work needed to bridge that gap. This is particularly relevant to our experiments
with introducing new predicates in Metamath.

The editor's twin-prime comment is about the same issue. Bounding the search
for a prime by $n!+1$ lets us express that particular existence claim by
recursion. It does not give a bound for finding a twin-prime pair beyond $n$.
“So far as possible” does not announce a solution to that problem, nor does the
introduction prove a general impossibility theorem about every conceivable
reformulation of the twin-prime conjecture. We can leave that question open and
still get what we need from this paper: a few induction proofs and a concrete
example of replacing bounded quantification by recursion.

[/AI SPARKNOTES]

### 5.0.4 draft

> [!WARNING]
> The rest of this is fully llm written and has not yet been reviewed and edited.

"Every $x$ that equals $t$ satisfies $\varphi$." It's the hypothesis of `vtonum`, pulled
inside the formula. For this to really mean "$\varphi$ at $t$," we need to get in and get out:

- Getting in: if we proved `|- ( x = t -> ph )` about an arbitrary `x`, we should get the `A. x` version.
- Getting out: from `A. x ( x = t -> ps )` with no `x` in `ps`, we should get `ps`.

Four axioms do it. They're the first four of `set.mm`'s predicate calculus,
and we'll build with the first three ourselves in 5.1.

$$
\frac{\vdash\varphi}{\vdash\forall x\,\varphi}
\quad\href{https://us.metamath.org/mpeuni/ax-gen.html}{\texttt{ax-gen}}
$$

Generalization. This one I find very satisfying: in the introduction I complained that
a statement with variables is already a sort of "for all" statement. `ax-gen` just lets
us write that down.

$$
\vdash\forall x\,(\varphi\to\psi)\to(\forall x\,\varphi\to\forall x\,\psi)
\quad\href{https://us.metamath.org/mpeuni/ax-4.html}{\texttt{ax-4}}
$$

Modus ponens under a quantifier. With `ax-gen` it gives `alimi`: from
`|- ( ph -> ps )` get `|- ( A. x ph -> A. x ps )`.

$$
\vdash\varphi\to\forall x\,\varphi\quad(x\text{ not in }\varphi)
\quad\href{https://us.metamath.org/mpeuni/ax-5.html}{\texttt{ax-5}}
$$

Quantifying over a variable that isn't there does nothing. In Metamath this is `$d x ph`,
the same disjointness condition that saved `vtonum` in 5.0.3.

$$
\vdash\exists x\,(x=t)\quad(x\text{ not in }t)
\quad\href{https://us.metamath.org/mpeuni/ax6ev.html}{\texttt{ax-6}}
$$

Every term equals something. Without this, `A. x ( x = t -> ps )` could be true just because
nothing equals `t`, and we'd never get `ps` out. (`set.mm` states `ax-6` for two variables, and
for class terms the same job is done by a hypothesis `A e. V`.)

With these, getting out is the lemma `spcvlem`. Suppose `-. ps`. By `ax-5` that's
`A. x -. ps`, and with `A. x ( x = t -> ps )` and `ax-4` we get `A. x -. x = t`. That
contradicts `ax-6`. So `ps`. Wrapping it up with the hypothesis from 5.0.3 gives
specialization at a term, which is set.mm's [`spcv`](https://us.metamath.org/mpeuni/spcv.html)
minus the `A e. V`:

```
MM> show proof spcv /lemmon /renumber
1 spcv.1         $e |- ( x = t -> ( ph <-> ps ) )
2 1 biimpd       $p |- ( x = t -> ( ph -> ps ) )
3 2 com12        $p |- ( ph -> ( x = t -> ps ) )
4 3 alimi        $p |- ( A. x ph -> A. x ( x = t -> ps ) )
5 spcvlem        $p |- ( A. x ( x = t -> ps ) -> ps )
6 4,5 syl        $p |- ( A. x ph -> ps )
```

And now `vtonum` is no longer an axiom: given `|- ph`, `ax-gen` gives `|- A. x ph`, and
`spcv` gives `|- ps`. The `$d x ps $. $d x t $.` that we had to discover by breaking things in 5.0.3
are exactly the conditions `ax-5` and `ax-6` need in the proof. That's quite nice! We didn't put
them in by hand this time; they fell out.

Now we can write down induction. Every $\varphi(\cdot)$ in the textbook formula becomes
`A. x ( x = _ -> ph )`:

```mm
${
  $d x y $. $d y ph $.
  ax-peano $a |- ( ( A. x ( x = 0 -> ph )
      /\ A. y ( A. x ( x = y -> ph ) -> A. x ( x = S y -> ph ) ) ) -> A. x ph ) $.
$}
```

Compare to `ax-ind` from 5.0.3: it had five wff metavariables and six hypotheses, while `ax-peano`
has one metavariable and no hypotheses. It's one statement, and it's the statement from the book.

How does `set.mm` do it? ZFC has no induction axiom. Instead the natural numbers are built as
a set, $\omega,$ and [`peano5`](https://us.metamath.org/mpeuni/peano5.html) proves that
a set containing $\emptyset$ and closed under successor contains all of $\omega.$
It has the same shape as `ax-peano`, but it's a theorem, because set theory can talk about
"the smallest set closed under successor." Our arithmetic has no sets, so that shape is
something we have to assume. That's Peano's choice: induction is the one axiom we add.

#### 5.0.4a Applying the quantifier-ful induction

> [!WARNING]
> This section is AI-generated and has not been reviewed.

We could prove `addrid` straight from `ax-peano`, but there's a better way. We prove the rule from
5.0.3, same hypotheses, same names, as the theorem `ind`:

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

Each hypothesis of the old rule has a job now:

- Steps 1–5: `at-zero` and `base` give $\varphi(0)$, i.e. `A. x ( x = 0 -> ph )`. This is getting in.
- Steps 6–11: `at-var` turns $\varphi(y)$ back into `ch`. This is getting out, with `spcv` at `t := y`.
- Steps 12–21: `step` takes `ch` to `th`, `at-succvar` turns `th` into $\varphi(Sy)$ (getting in again),
and `ax-gen` quantifies over `y`.
- Steps 22–23: `ax-peano` gives `A. x ph`.
- Steps 24–26: `at-num` gets out at `t`.

The `$d` conditions of `ind` are the ones we listed by hand for `ax-ind` in 5.0.3, and
Metamath checks every one of them against the axioms used. So the rule we wrote down in 5.0.3,
which we could only defend by pointing at counterexamples to weaker versions, is now a theorem.

`set.mm` does the same thing. [`nn0ind`](https://us.metamath.org/mpeuni/nn0ind.html)
has our six hypotheses (with `y e. NN0 ->` on the step, since there not everything is a number),
and it is proved from a `peano5`-like fact, not assumed.

The proof of `addrid` is then the proof from 5.0.3a with `ind` in place of `ax-ind`. We copy
`addrid-at` and `addrid-step` into `arith-fo.mm`, since it doesn't include `arith-qf.mm`.

```
MM> show proof addrid /lemmon /renumber
1 addrid-at      $p |- ( x = 0 -> ( ( x + 0 ) = x <-> ( 0 + 0 ) = 0 ) )
2 addrid-at      $p |- ( x = y -> ( ( x + 0 ) = x <-> ( y + 0 ) = y ) )
3 addrid-at      $p |- ( x = S y -> ( ( x + 0 ) = x <-> ( S y + 0 ) = S y ) )
4 addrid-at      $p |- ( x = t -> ( ( x + 0 ) = x <-> ( t + 0 ) = t ) )
5 00id           $p |- ( 0 + 0 ) = 0
6 addrid-step    $p |- ( ( y + 0 ) = y -> ( S y + 0 ) = S y )
7 1,2,3,4,5,6 ind  $p |- ( t + 0 ) = t
```

The only change is that step 7 is `$p`, not `$a`.

@src(code-05/arith-fo.mm, noexecute, collapsed)

## Extra problem sets for 5.1 and 5.2

> [!WARNING]
> This section is AI-generated and has not been reviewed. Citations marked "(check)" have not
> been verified against a source.

These problem sets ask how much of predicate logic the axioms in 5.1 actually give us,
and what changes when we add more axioms. E1–E3 stay with a single quantifier variable;
E4–E9 return to the full `set.mm` library, with equality and multiple variables.

The accompanying proof files and countermodel searches are in `ai/tmp/ch05-deferred/`:

- `pred-k.mm`: E1–E2
- `pred-s5.mm`: E3
- `set-x.mm`: the new statements in E6 and E8
- `kripke.py` and `fol.py`: the countermodel searches

As in the chapter, hints read the proof backwards. "`ja` splits the goal into two cases" means:
assign `ja` to the goal, and its hypotheses are the new goals.

### E1 The existential quantifier in K

> [!WARNING]
> This section is AI-generated and has not been reviewed.

Start with the assertions available in `pred-5-1.mm`. Besides the imported
propositional library, we have `wal`, which constructs `wff A. x ph`, and two
assertions whose conclusions start with `|-`: `ax-gen` and `ax-4`. `ax-gen`
has an essential hypothesis `|- ph` and conclusion `|- A. x ph`. `ax-4` has
no essential hypotheses and gives
`|- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) )`.

What can we build from those assertions by substitution and proof composition?
Quite a lot, as 5.1 showed. But `|- ( A. x ph -> ph )` is out of reach.
E2 will establish that by finding a property every proof from this file
preserves, then showing that the proposed conclusion fails it.

The system generated by these assertions has a conventional name: **K**, the
weakest *normal modal logic*. To compare notation, keep `x` fixed and write
`[]ph` for `A. x ph`. Modal logic usually reads `[]` as “necessarily.” Its
*distribution* assertion is our `ax-4`; its *necessitation* rule is our
`ax-gen`. “Normal” specifies that these are available, together with classical
propositional reasoning and uniform substitution. K includes no additional
modal assertions. The name honors Kripke; see Schwarz's [discussion of K and
its extensions](https://www.umsu.de/logic2/03-accessibility.html).

Next we add the `$a` statements `wex` and `df-ex` below. The first constructs
expressions beginning with `E. x`; the second relates them to the expressions
we already have: `E. x ph <-> -. A. x -. ph`. Thus the new operator is
specified in terms of `A.` and negation. In modal notation it is written
`<>ph` and read “possibly ph.” The familiar quantifier reading is “some x
satisfies ph”: not every x fails ph.

The exercises ask what these additions let us prove. Problems 5.2.1–5.2.2
reappear here with only the E1 assertions available.

Append to a copy of `pred-5-1.mm`:

```metamath
$c E. $.
wex $a wff E. x ph $.
df-ex $a |- ( E. x ph <-> -. A. x -. ph ) $.

alnex $p |- ( A. x -. ph <-> -. E. x ph ) $= ? $.
alex $p |- ( A. x ph <-> -. E. x -. ph ) $= ? $.
exnal $p |- ( E. x -. ph <-> -. A. x ph ) $= ? $.

${
  aleximi.1 $e |- ( ph -> ( ps -> ch ) ) $.
  aleximi $p |- ( A. x ph -> ( E. x ps -> E. x ch ) ) $= ? $.
$}
exim $p |- ( A. x ( ph -> ps ) -> ( E. x ph -> E. x ps ) ) $= ? $.
${
  eximi.1 $e |- ( ph -> ps ) $.
  eximi $p |- ( E. x ph -> E. x ps ) $= ? $.
$}
exa1 $p |- ( E. x ph -> E. x ( ps -> ph ) ) $= ? $.
19.29 $p |- ( ( A. x ph /\ E. x ps ) -> E. x ( ph /\ ps ) ) $= ? $.
19.35 $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> E. x ps ) ) $= ? $.
${
  19.35ri.1 $e |- ( A. x ph -> E. x ps ) $.
  19.35ri $p |- E. x ( ph -> ps ) $= ? $.
$}
exintr $p |- ( A. x ( ph -> ps ) -> ( E. x ph -> E. x ( ph /\ ps ) ) ) $= ? $.
```

#### Hints

- `alnex`: `con2bii` moves the negation across `df-ex`.
- `alex`: `bitri` goes through `A. x -. -. ph`. Assign `alnex` to the second hypothesis first,
  since that fixes the middle. The first hypothesis is `albii` of double negation (`notnotb`).
- `exnal`: `con2bii` of `alex`.
- `aleximi` is the key lemma. Everything after it is short. The goal mixes `A.` and `E.`, and
  `E.` is `-. A. -.`, so contrapose. `con4d` reduces the goal to
  `( A. x ph -> ( -. E. x ch -> -. E. x ps ) )`. `3imtr3g` rewrites both `-. E.` into `A. -.`
  with `alnex`, which leaves `( A. x ph -> ( A. x -. ch -> A. x -. ps ) )`. That is `al2imi` of
  the contraposed hypothesis (`con3d`).
- `exim`: `aleximi` leaves `( ( ph -> ps ) -> ( ph -> ps ) )`.
- `eximi`, `exa1`, `19.29`, `19.35`, `19.35ri`: the hints in chapter 5.2.1–5.2.2 apply unchanged.
- `exintr`: `aleximi` leaves a chapter 4 theorem. Find it with
  `search * "( ( ph -> ps ) -> ( ph -> ( ph /\ ps ) ) )"`.

#### Answers

```
MM> show proof aleximi /lemmon /renumber
1 aleximi.1      $e |- ( ph -> ( ps -> ch ) )
2 1 con3d        $p |- ( ph -> ( -. ch -> -. ps ) )
3 2 al2imi       $p |- ( A. x ph -> ( A. x -. ch -> A. x -. ps ) )
4 alnex          $p |- ( A. x -. ch <-> -. E. x ch )
5 alnex          $p |- ( A. x -. ps <-> -. E. x ps )
6 3,4,5 3imtr3g  $p |- ( A. x ph -> ( -. E. x ch -> -. E. x ps ) )
7 6 con4d        $p |- ( A. x ph -> ( E. x ps -> E. x ch ) )
MM> show proof 19.35 /lemmon /renumber
 1 pm2.27        $p |- ( ph -> ( ( ph -> ps ) -> ps ) )
 2 1 aleximi     $p |- ( A. x ph -> ( E. x ( ph -> ps ) -> E. x ps ) )
 3 2 com12       $p |- ( E. x ( ph -> ps ) -> ( A. x ph -> E. x ps ) )
 4 exnal         $p |- ( E. x -. ph <-> -. A. x ph )
 5 pm2.21        $p |- ( -. ph -> ( ph -> ps ) )
 6 5 eximi       $p |- ( E. x -. ph -> E. x ( ph -> ps ) )
 7 4,6 sylbir    $p |- ( -. A. x ph -> E. x ( ph -> ps ) )
 8 exa1          $p |- ( E. x ps -> E. x ( ph -> ps ) )
 9 7,8 ja        $p |- ( ( A. x ph -> E. x ps ) -> E. x ( ph -> ps ) )
10 3,9 impbii    $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> E. x ps ) )
```

The rest, from the last step backwards:

- `alnex`: `df-ex con2bii`.
- `alex`: `notnotb albii`, `alnex`, then `bitri`.
- `exnal`: `alex con2bii`.
- `exim`: `id aleximi`.
- `eximi`: `exim`, `eximi.1`, then `mpg`.
- `exa1`: `ax-1 eximi`.
- `19.29`: `pm3.2 aleximi imp`.
- `19.35ri`: `19.35ri.1`, `19.35`, then `mpbir`.
- `exintr`: `ancl aleximi`.

### E2 Syllogisms with existential import

> [!WARNING]
> This section is AI-generated and has not been reviewed.

Continue the E1 file. These syllogisms combine “all,” “none,” and “some.”
The traditional letters A, E, I, O mean, respectively, “all S are P,” “no S
are P,” “some S are P,” and “some S are not P.” A *mood* specifies the forms
of the two premises and the conclusion; a *figure* specifies where the middle
term appears. The names below identify particular patterns, not new axioms.

`darii` and `ferio` already have an existential premise. `barbari` and `darapti`
need an additional one. For `darapti`, “all M are P” and “all M are S” imply
“some S is P” only if some M exists. Both universal premises can hold when M
is empty. The requirement that the relevant class contain something is called
**existential import**. Keep track of which class must be nonempty: a nonempty
universe alone does not guarantee that M has a member.

#### How to prove that no proof exists

Suppose someone supplies a proof of `|- ( A. x ph -> ph )` using the E1
file. Every `$p` it cites can be expanded into its own proof. Eventually we
are left with uses of the file's `$a` assertions and the active hypotheses,
with Metamath's substitutions applied. To rule out **every** possible proof,
we need a property that survives all those steps.

Use the truth-table calculations from propositional logic. Give each wff
variable a value T or F, and evaluate the connectives by their usual truth
tables. Extend that calculation with two deliberately simple instructions:

- An expression beginning with `A. x` gets T, whatever follows it.
- An expression beginning with `E. x` gets F, whatever follows it.

This is a calculation on the expressions in a proposed proof. The claim to
check is: **whenever its essential hypotheses evaluate to T, every assertion
application with a `|-` conclusion also evaluates to T.** The `wff` and
`setvar` steps supply expressions of the required types; they do not assert
that those expressions evaluate to T. We need no domain of objects or values
for `x`: the instruction for `A. x` simply ignores that token and its body.

Check each source of a `|-` conclusion:

- `ax-1`–`ax-3` evaluate to T by their truth tables. This remains so when
  whole wffs replace their variables: each replacement still evaluates to
  either T or F. The propositional definitions also evaluate to T when their
  defined connectives are given the corresponding truth tables.
- `ax-mp` preserves T: if `ph` and `( ph -> ps )` both evaluate to T, then
  `ps` evaluates to T.
- Every substitution instance of `ax-4` evaluates as `T -> ( T -> T )`,
  hence T.
- `ax-gen` concludes `A. x ph`, which always evaluates to T. In particular,
  it does so whenever its essential hypothesis evaluates to T.
- `df-ex` evaluates as `F <-> -. T`, hence T.

That covers the available assertions. Following the expanded proof step by
step, every `|-` line must therefore evaluate to T, provided the active
essential hypotheses do. Already-proved lemmas cannot escape this restriction:
their proofs consist of the same steps. This preserved property is called
an **invariant** of the proof construction.

A proof of `sp` would also allow the substitution `F.` for `ph`, giving
`|- ( A. x F. -> F. )`. That expression evaluates to `T -> F`, which is F.
So it cannot be the last line of such a proof. We have
proved that no E1 proof of `sp` exists, by examining what the file allows a
proof to do. The same calculation will settle the other two unprovability
exercises below.

This is the basic **countermodel** argument. The evaluation passes every
available assertion but fails the target. Showing that the assertion
applications preserve the test is the *soundness* part of the argument.
The unprovability conclusion concerns this fixed file; a new `$a` assertion
would have to pass the test too before we could reuse the argument.

```metamath
${
  darii.maj $e |- A. x ( ph -> ps ) $.
  darii.min $e |- E. x ( ch /\ ph ) $.
  darii $p |- E. x ( ch /\ ps ) $= ? $.
$}
${
  ferio.maj $e |- A. x ( ph -> -. ps ) $.
  ferio.min $e |- E. x ( ch /\ ph ) $.
  ferio $p |- E. x ( ch /\ -. ps ) $= ? $.
$}
${
  barbari.maj $e |- A. x ( ph -> ps ) $.
  barbari.min $e |- A. x ( ch -> ph ) $.
  barbari.e $e |- E. x ch $.
  barbari $p |- E. x ( ch /\ ps ) $= ? $.
$}
${
  darapti.maj $e |- A. x ( ph -> ps ) $.
  darapti.min $e |- A. x ( ph -> ch ) $.
  darapti.e $e |- E. x ph $.
  darapti $p |- E. x ( ch /\ ps ) $= ? $.
$}
```

Then a non-proof problem: show that none of the following can be proved from the E1 axioms.

- `sp` `|- ( A. x ph -> ph )`
- `19.2` `|- ( A. x ph -> E. x ph )`
- `darapti` without the hypothesis `darapti.e`

#### Hints

- `darii`: as with `barbara`, `mp2` takes the goal to the two premises plus a closed statement.
  Here the closed statement is `( A. x ( ph -> ps ) -> ( E. x ( ch /\ ph ) -> E. x ( ch /\ ps ) ) )`.
  The middle formulas are ambiguous, so fix them with `let variable` (or assign the premises
  first). `aleximi` then leaves a chapter 4 fact that `id` and `anim2d` give.
- `ferio`: one step, like `celarent`.
- `barbari`: `mp2` with `exintr` as the closed statement. The universal premise it needs is
  `barbara`.
- `darapti`: `mp2` with `exim` takes the goal to `darapti.e` and `A. x ( ph -> ( ch /\ ps ) )`.
  For that, `mp2` with `al2imi` takes it to the two premises and a chapter 4 theorem
  (`pm3.43i`).
- Unprovability: apply the evaluation above. For each target, check that the
  essential hypotheses evaluate to T and the conclusion evaluates to F.

#### Answers

```
MM> show proof darapti /lemmon /renumber
1 darapti.min    $e |- A. x ( ph -> ch )
2 darapti.maj    $e |- A. x ( ph -> ps )
3 pm3.43i        $p |- ( ( ph -> ch ) -> ( ( ph -> ps ) -> ( ph -> ( ch /\ ps ) ) ) )
4 3 al2imi       $p |- ( A. x ( ph -> ch ) -> ( A. x ( ph -> ps ) -> A. x ( ph -> ( ch /\ ps ) ) ) )
5 1,2,4 mp2      $p |- A. x ( ph -> ( ch /\ ps ) )
6 darapti.e      $e |- E. x ph
7 exim           $p |- ( A. x ( ph -> ( ch /\ ps ) ) -> ( E. x ph -> E. x ( ch /\ ps ) ) )
8 5,6,7 mp2      $p |- E. x ( ch /\ ps )
```

The rest:

- `darii`: `id anim2d aleximi`, then `mp2` with the two premises.
- `ferio`: `darii` with `-. ps` for `ps`.
- `barbari`: `barbara`, then `barbari.e`, `exintr`, and `mp2`.

For unprovability, apply the invariant established before the exercises:

- `sp` evaluates to `T -> F` when `ph` is assigned F.
- `19.2` evaluates to `T -> F` for every assignment to `ph`.
- Without `darapti.e`, both essential hypotheses of `darapti` evaluate to T,
  because they begin with `A. x`. Its conclusion begins with `E. x`, so it
  evaluates to F. Thus the inference cannot be proved either.

With `darapti.e` present, the last argument no longer works: that hypothesis
also begins with `E. x`, so it evaluates to F. Our invariant only constrains
proofs whose essential hypotheses all evaluate to T. This pinpoints how the
extra hypothesis makes the proof above possible.

The statement `19.2`, written `[]p -> <>p`, has the modal name **D**. Adding
it as a `$a` assertion to E1 gives the system **KD**. It fails our evaluation,
so this particular invariant no longer applies to the enlarged file. To
show that `sp` is still unprovable there, we will need a different evaluation;
E3 constructs one.

In the stored `set.mm` proof, `19.2` follows using `ax-6`, an equality axiom
asserting `E. x x = y`. E3 obtains it differently, from `sp`. These are two
sufficient ways to prove the same statement, not claims that either axiom is
indispensable. Run `show trace_back 19.2 /axioms` to inspect the library proof.

### E3 Capstone: from K to S5

> [!WARNING]
> This section is AI-generated and has not been reviewed.

We now enlarge the file with two `$a` assertions. The first is precisely
`sp`, which E2 showed we could not prove from E1. Its modal name is **T**,
and its modal notation is `[]p -> p`. The second is `ax-10`, with conclusion
`|- ( -. A. x ph -> A. x -. A. x ph )`. Its modal name is **5**, written
`-. []p -> []-. []p`. The exercises show how these additions let us derive
statements that were previously unavailable.

K together with T and 5 is the modal logic **S5**. This name comes from Lewis
and Langford's *Symbolic Logic* (1932), not Tarski's 1965 paper. Tarski's **S2**
in Megill's book is a different naming scheme for predicate logic with equality.
There is also a modal system called S2 in Lewis's series, but we do not need
it here. Schwarz gives the [modern axiomatization and its connection to Lewis
and Langford](https://www.umsu.de/logic2/01-operators.html).

Here “the file gives S5” identifies which statements become provable after
these additions, with `x` fixed and `A. x` read as the one modal operator.
It does not identify the whole of predicate logic with S5: equality and
interactions between different quantifier variables need further assertions.

Add the following to the E1–E2 file. In full `set.mm`, `sp` is instead a
`$p` assertion with a proof using `ax-12`.

```metamath
sp $a |- ( A. x ph -> ph ) $.
ax-10 $a |- ( -. A. x ph -> A. x -. A. x ph ) $.

19.8a $p |- ( ph -> E. x ph ) $= ? $.
19.2 $p |- ( A. x ph -> E. x ph ) $= ? $.
qexmid $p |- E. x ( ph -> A. x ph ) $= ? $.
hbe1 $p |- ( E. x ph -> A. x E. x ph ) $= ? $.
hbe1a $p |- ( E. x A. x ph -> A. x ph ) $= ? $.
bj-modalbe $p |- ( ph -> A. x E. x ph ) $= ? $.
modal-b $p |- ( ph -> A. x -. A. x -. ph ) $= ? $.
hba1 $p |- ( A. x ph -> A. x A. x ph ) $= ? $.
```

The first exercises recover familiar quantifier properties. `19.8a` says that
`ph` itself supplies an existential witness; combined with `sp`, it gives
`19.2`. `qexmid` is the drinker formula: some `x` has the property that, if
`ph` holds for that `x`, it holds for every `x`. It follows already from T
and the E1 results, without using 5.

The remaining exercises explain what 5 adds. `hbe1` is its possibility form,
`<>p -> []<>p`; `hbe1a` is the equivalent form `<>[]p -> []p`. The statements
`bj-modalbe` and `modal-b` express **B**, `p -> []<>p`: from `ph` we can
infer `A. x E. x ph`. They differ only in whether `E.` is written out using
`A.` and negation. Finally, `hba1` expresses **4**, `[]p -> [][]p`: an
`A. x` prefix can be repeated. The numbers 4 and 5
are conventional modal axiom names; they are not the numbers in Metamath's
labels `ax-4` and `ax-5`.

#### Hints

- `19.8a`: `sylibr` with `df-ex` turns the goal into `( ph -> -. A. x -. ph )`. `con2i` turns
  that into an instance of `sp`.
- `19.2`: `syl` through `ph`.
- `qexmid`: as in chapter 5.2.3. With `19.8a` available, it needs only `sp`, not `ax-10`.
- `hbe1`: `ax-10` with `-. ph` in place of `ph` is `hbe1` with `E.` unfolded. `3imtr4i` folds
  both sides back. Fix its middle formulas with `let variable` first, since the unification is
  ambiguous. The right side needs `albii` of `df-ex`.
- `hbe1a`: `sylbi` with `df-ex` unfolds the antecedent. Then `con1i` turns the goal into
  `ax-10`.
- `bj-modalbe`: `syl` through `E. x ph`.
- `modal-b`: `sylib` with `albii` of `df-ex` reduces it to `bj-modalbe`.
- `hba1` is the hard one. Apply B to `A. x ph`, then strip the inner `E. x A. x` with `hbe1a`
  under the quantifier. In backward terms: `syl` through `A. x E. x A. x ph`, fixed with `let`.
  The first goal is `bj-modalbe`. The second is `alimi` of `hbe1a`.

#### Answers

```
MM> show proof hbe1 /lemmon /renumber
1 ax-10          $a |- ( -. A. x -. ph -> A. x -. A. x -. ph )
2 df-ex          $a |- ( E. x ph <-> -. A. x -. ph )
3 df-ex          $a |- ( E. x ph <-> -. A. x -. ph )
4 3 albii        $p |- ( A. x E. x ph <-> A. x -. A. x -. ph )
5 1,2,4 3imtr4i  $p |- ( E. x ph -> A. x E. x ph )
MM> show proof hba1 /lemmon /renumber
1 bj-modalbe     $p |- ( A. x ph -> A. x E. x A. x ph )
2 hbe1a          $p |- ( E. x A. x ph -> A. x ph )
3 2 alimi        $p |- ( A. x E. x A. x ph -> A. x A. x ph )
4 1,3 syl        $p |- ( A. x ph -> A. x A. x ph )
```

The rest:

- `19.8a`: `sp con2i`, `df-ex`, then `sylibr`.
- `19.2`: `sp`, `19.8a`, then `syl`.
- `qexmid`: `19.8a 19.35ri`.
- `hbe1a`: `df-ex`, `ax-10 con1i`, then `sylbi`.
- `bj-modalbe`: `19.8a`, `hbe1`, then `syl`.
- `modal-b`: `bj-modalbe`, `df-ex albii`, then `sylib`.

#### Countermodels: which additions actually matter?

E2 used a single T/F value per expression. For stronger files, we can use
several values per expression, indexed by numbered positions. Evaluate the
propositional connectives separately at each position. Draw arrows between
the positions, then evaluate `A. x ph` at position `w` as T exactly when
`ph` evaluates to T at every position with an arrow from `w`. Evaluate
`E. x ph` as T when at least one of those positions gives `ph` value T.
With no outgoing arrows, these instructions give T and F respectively,
recovering E2's calculation. Use single arrows, not paths of several arrows.

The invariant is now: **every `|-` conclusion evaluates to T at every
position, whenever its essential hypotheses do.** Check it against the same
assertions. `ax-4` passes because at each arrow's destination, `ph -> ps`
and `ph` give `ps`. `ax-gen` passes because an expression that is T at every
position is T at every destination. `ax-mp` and the propositional assertions
pass position by position, and `df-ex` passes by the two evaluation rules.
These checks work for arbitrary substituted wffs. A proposed theorem that
evaluates to F at even one position therefore cannot have an E1 proof.

To extend the argument to a larger file, check its additional `$a` assertions
too. For example, `sp` passes all assignments if every position has an arrow
to itself: `A. x ph` then tests `ph` at that position as well. To use the
invariant for proofs with `$e` hypotheses, those hypotheses must evaluate
to T at every position. T at just the position where the target fails does
not suffice for the `ax-gen` check.

This construction is called a **Kripke model**. Its positions are usually
called *worlds*, the arrows form an *accessibility relation*, and the positions
and arrows together form a *frame*. Assigning the initial T/F values to wff
variables is a *valuation*. “World” here names a position in the evaluation;
the proof argument only uses the calculation just given. See the
[soundness connection between models and proofs](https://www.umsu.de/logic2/04-proofs.html).

The system names specify which additional assertions must pass:

- **K** is the E1 system, valid on arbitrary frames.
- **KD** adds D and uses *serial* frames: every world sees at least one world.
- **KT**, also called T, adds T and uses *reflexive* frames: every world sees itself.
- **S4** adds T and 4 to K. Its frames are reflexive and *transitive*: if `w`
  sees `v` and `v` sees `u`, then `w` sees `u`.
- **S5** adds T and 5 to K. Its frames are *equivalence relations*: reflexive,
  symmetric, and transitive. They split into groups within which every world
  sees every world, with no arrows between groups. From any starting world,
  the calculation therefore tests every position in that group.

These are the usual [frame conditions for the modal systems](https://www.umsu.de/logic2/03-accessibility.html).
More axioms restrict the permitted frames. To disprove derivability in S4,
for example, we must use a reflexive, transitive frame; an arbitrary K
countermodel would not suffice.

**Problem.** For each of `sp`, `19.2`, `qexmid`, `hba1`, and `ax-10`, search
for a countermodel in K, KD, KT, and S4, starting with one world and stopping
at three. Use `ai/tmp/ch05-deferred/kripke.py` or Z3. Record the arrows,
valuation, and world where the formula fails. Finding a countermodel proves
unprovability. Finding none up to three worlds establishes only that bounded
search result; a proof or a general semantic argument is still needed.

**Worked countermodels.** In each example, the listed arrows are all the arrows.

1. **K does not prove `sp`, `19.2`, or `qexmid`.** Use a single world with no
   arrows, reproducing E2's evaluation, with `p` false there. `[]p` is true, while `p` and every
   formula beginning with `<>` are false.
2. **D does not suffice for `sp` or `qexmid`.** Take two worlds, with arrows
   `0 -> 1` and `1 -> 0`, and `p` true only at 1. This frame is serial. At 0,
   `[]p` is true but `p` is false, refuting `sp`. For `qexmid`, the only
   candidate witness is 1. There `p` is true and `[]p` is false, so
   `p -> []p` is false. Hence `<>(p -> []p)` is false at 0 as well.
3. **T does not suffice for 4 (`hba1`).** Use `0 -> 0`, `1 -> 1`, `1 -> 2`,
   `2 -> 0`, and `2 -> 2`, with `p` true at 1 and 2 only. Every world sees
   itself. At 1, `[]p` holds. But 1 sees 2, where `[]p` fails because 2 sees
   0. Thus `[][]p` fails at 1. This is also a K and KD countermodel. For
   those weaker systems, two worlds suffice: use the two-world cycle in
   example 2 and evaluate 4 at 0.
4. **Even S4 does not suffice for 5 (`ax-10`).** Use `0 -> 0`, `1 -> 0`, and
   `1 -> 1`, with `p` true only at 0. The frame is reflexive and transitive.
   At 1, `-. []p` is true because 1 sees itself, where `p` is false. But 1
   also sees 0, where `[]p` is true. Hence `[]-. []p` is false at 1. The
   same frame refutes 5 in K, KD, and KT.

The searches give minimum sizes of one world for example 1, two for examples
2 and 4, and three for the reflexive countermodel in example 3. The positive
results have proofs: D is an axiom of KD; T gives D and `qexmid` by the
exercises above; and 4 is an axiom of S4. In S5 all five targets are provable.

So “`hba1` needs 5” would be too strong. What we have proved is that K + T
alone does not give 4, while adding 5 is one way to obtain it. Adding 4
directly is another. Likewise, refuting 5 in S4 proves that 5 is an
additional assumption, not a hidden consequence of T and 4.

### E4 Which axioms each theorem uses (set.mm)

> [!WARNING]
> This section is AI-generated and has not been reviewed.

A dependency trace reports which axioms the **stored proof** uses. If an axiom
is absent, this proof establishes that the theorem can be obtained without it.
If it is present, another proof might still avoid it. To establish that an
axiom is necessary, we need a separate argument such as E2's countermodel.

Predict the dependencies among `ax-gen`, `ax-4` … `ax-13`, and `ax-ext`, then
check with `show trace_back LABEL /axioms`:

`exim`, `19.8a`, `sp`, `19.2`, `qexmid`, `hba1`, `hbe1`, `alcom`, `excom`, `19.12`,
`sbequ12`, `sb6`, `alrimiv`, `exlimiv`, `19.21v`, `ax6ev`, `equid`, `stdpc4`, `ru0`, `axextb`.

#### Answer

The predicate and set-theoretic dependencies are listed below; propositional
axioms, syntax declarations, and definitions are omitted. Use the trace for
the complete dependency list.

- `exim`: `ax-gen ax-4`.
- `19.2`: `ax-gen ax-4 ax-6`.
- `hbe1`: `ax-gen ax-4 ax-10`.
- `alcom`: `ax-11`.
- `excom`: `ax-gen ax-4 ax-11`.
- `ax6ev`: `ax-6`.
- `alrimiv`, `exlimiv`, `19.21v`: `ax-gen ax-4 ax-5`.
- `sb6`, `equid`, `stdpc4`: `ax-gen ax-4 ax-5 ax-6 ax-7`.
- `19.8a`, `sp`, `qexmid`, `sbequ12`: `ax-gen ax-4 ax-5 ax-6 ax-7 ax-12`.
- `hba1`: `ax-gen ax-4 ax-5 ax-6 ax-7 ax-10 ax-12`.
- `19.12`: `ax-gen ax-4 ax-5 ax-6 ax-7 ax-10 ax-11 ax-12`.
- `ru0`: `ax-gen ax-4 ax-5 ax-6 ax-7 ax-8 ax-9`.
- `axextb`: `ax-gen ax-4 ax-5 ax-6 ax-7 ax-9 ax-ext`.

Things to notice:

- `19.2` comes from `ax-6`, the existence of `x = y`, not from `sp`. In `set.mm`, nonempty
  domains come from equality.
- `sp` is not an axiom. It is derived with `ax-12`. Its comment (line 19130) says it seems not to
  follow directly as a Metamath scheme from Tarski's schemes alone; compare `spw`.
  This is not an established unprovability result about `sp`: the library
  comment says “appears.” Nor does it contradict completeness of ordinary
  first-order logic; see the distinction in E7.
- `alcom` needs nothing but `ax-11`, not even `ax-gen`.
- `sb6` avoids `ax-12`, but `sbequ12` does not.
- Library skill: prove `qexmid` from `19.35` the long way, then run `minimize_with *` and compare
  with the `set.mm` proof.

### E5 The Hilbert–Ackermann toolkit (set.mm)

> [!WARNING]
> This section is AI-generated and has not been reviewed.

Hilbert and Ackermann, *Grundzüge der theoretischen Logik* (1928), gave two quantifier axioms and
two rules, and asked whether they are complete. Gödel's 1929 dissertation proved they are. Their
rules correspond to `alrimiv` and `exlimiv`. From `ph -> ps`, the first gives
`ph -> A. x ps` when `ph` does not depend on `x`; the second gives
`E. x ph -> ps` when `ps` does not depend on `x`. These restrictions prevent
an assumption about a particular `x`, or a conclusion about that `x`, from
being treated as independent of its value.

`set.mm` has two versions of each rule. The `v` version uses a `$d` condition:
`$d ph x` requires the substituted expression for `ph` not to contain the
variable substituted for `x`. The other version takes a hypothesis `F/ x ph`,
asserting that `x` is not free in `ph`. This permits occurrences bound by a
quantifier, such as `A. x ps`, whose truth does not depend on the current `x`.
In a working copy of `set.mm`, find each label, clear its proof, and reprove it:

```metamath
${ $d ph x $.  ax5e $p |- ( E. x ph -> ph ) $= ? $. $}
${ $d ph x $.  alrimiv.1 $e |- ( ph -> ps ) $.
   alrimiv $p |- ( ph -> A. x ps ) $= ? $. $}
${ $d ps x $.  exlimiv.1 $e |- ( ph -> ps ) $.
   exlimiv $p |- ( E. x ph -> ps ) $= ? $. $}
${ $d ph x $.  19.21v $p |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) $= ? $. $}
${ $d ps x $.  19.23v $p |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) $= ? $. $}
${ $d ch x $.  $d ph x $.  exlimdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
   exlimdv $p |- ( ph -> ( E. x ps -> ch ) ) $= ? $. $}
${ alrimi.1 $e |- F/ x ph $.  alrimi.2 $e |- ( ph -> ps ) $.
   alrimi $p |- ( ph -> A. x ps ) $= ? $. $}
${ exlimi.1 $e |- F/ x ps $.  exlimi.2 $e |- ( ph -> ps ) $.
   exlimi $p |- ( E. x ph -> ps ) $= ? $. $}
```

#### Hints

- `ax5e`: `mpbir` with `eximal` (`( ( E. x ph -> ps ) <-> ( -. ps -> A. x -. ph ) )`) rewrites
  the goal into an instance of `ax-5`.
- `alrimiv`: `alrimih` takes the goal to `( ph -> A. x ph )` and the hypothesis. The `$d` makes
  the first an instance of `ax-5`.
- `exlimiv`: `syl` through `E. x ps`. The first goal is `eximi`, the second `ax5e`.
- `19.21v`: `impbii`. The forward direction is a closed theorem; search for it. The reverse goes
  by `syl` through `( E. x ph -> A. x ps )`: `19.38` is the second goal, and `imim1i` of `ax5e`
  is the first.
- `19.23v`: `impbii`. Forward: `syl6` with `exim` and `ax5e`. Reverse: `syl` through
  `( E. x ph -> A. x ps )`. `19.38` again, plus `imim2i` of `ax-5`.
- `exlimdv`: `syl6` with the deduction form `eximdv` and `ax5e`.
- `alrimi`: as `alrimiv`, but `( ph -> A. x ph )` now comes from the `F/` hypothesis via `nf5ri`.
- `exlimi`: `mpgbi` takes the goal to `( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) )` and the
  hypothesis `( ph -> ps )`. The biconditional is `19.23` with the `F/` hypothesis.

Answers: `show proof LABEL /lemmon /renumber` in an unmodified `set.mm`. All eight proofs are
2–8 steps.

History: Skolem's "Einige Bemerkungen zur axiomatischen Begründung der Mengenlehre" (1922 talk,
published 1923, usually cited as 1923a) is the Löwenheim–Skolem paper. It is not the primitive
recursive arithmetic paper of 5.0.5. In a 1967 letter to Hao Wang, Gödel wrote that completeness
is an almost trivial consequence of Skolem 1923a, but that nobody, Skolem included, drew that
conclusion. He called this a "blindness (or prejudice, or whatever you may call it) of
logicians" (check quote; printed in Wang, *From Mathematics to Philosophy*, 1974).

### E6 Quantifier shift (set.mm)

> [!WARNING]
> This section is AI-generated and has not been reviewed.

Here the order of different quantifiers matters. `E. x A. y ph` chooses one
`x` that works for every `y`. In `A. y E. x ph`, the choice of `x` may depend
on `y`. Thus “someone is everyone's mother” implies “everyone has a mother,”
while the reverse implication would demand a single mother for everyone.
Two universal quantifiers can commute, as can two existential quantifiers;
the mixed case is different. Reprove these in `set.mm`:

```metamath
19.12 $p |- ( E. x A. y ph -> A. y E. x ph ) $= ? $.
alcom $p |- ( A. x A. y ph <-> A. y A. x ph ) $= ? $.
excom $p |- ( E. x E. y ph <-> E. y E. x ph ) $= ? $.
excomim $p |- ( E. x E. y ph -> E. y E. x ph ) $= ? $.
```

For a concrete counterexample to the converse, use `ph := y = x` on a
two-element domain. Every `y` equals some `x` (choose `x = y`), but no single
`x` equals both elements. This proves that the converse is not a theorem of
pure first-order logic. It does not make its negation a logical theorem:
on a one-element domain the converse is true.

In `set.mm` we can go further, using set theory to establish that there are
at least two objects. The next exercise proves the negation of this particular
instance of the converse:

```metamath
${ $d x y $.
  qsfail $p |- -. ( A. y E. x y = x -> E. x A. y y = x ) $= ? $.
$}
```

Finally, check by brute force (`ai/tmp/ch05-deferred/fol.py`) that `19.12` holds for every binary
relation on a domain of 1–3 elements, and find a 2-element countermodel for the converse.

#### Hints

- `19.12`: `alrimi` generalizes over `y`, provided `y` is not free in `E. x A. y ph`. That
  leaves a nonfreeness goal and `( E. x A. y ph -> E. x ph )`. The second is `eximi` of `sp`.
  For the first, `nfex` passes `F/ y` through `E. x`, and `nfa1` finishes.
- `alcom`: `impbii`, with `ax-11` both ways.
- `excom`: `3bitr4i` unfolds both sides with `2exnaln`
  (`( E. x E. y ph <-> -. A. x A. y -. ph )`). What remains is `notbii` of `alcom`.
- `excomim`: `biimpi`.
- `qsfail`: `-. ( A -> B )` follows from `A` and `-. B`. Find the chapter 4 theorem with
  `search * "( ph -> ( -. ps -> -. ( ph -> ps ) ) )"`, then use it with `mp2`. `A` is `ax-gen`
  of `ax6evr`. `-. B` is `nex` of `dtru` ("not everything equals `x`"). The unification for
  `nex` is ambiguous; accept the first. Run `show trace_back qsfail /axioms`. It needs `ax-nul`
  and `ax-pr` in this proof, supplying distinct sets. The singleton countermodel
  shows why some assumption beyond pure first-order logic is required; it does
  not show that those two particular set-theoretic axioms are indispensable.

#### Answers

```
MM> show proof 19.12 /lemmon /renumber
1 nfa1           $p |- F/ y A. y ph
2 1 nfex         $p |- F/ y E. x A. y ph
3 sp             $p |- ( A. y ph -> ph )
4 3 eximi        $p |- ( E. x A. y ph -> E. x ph )
5 2,4 alrimi     $p |- ( E. x A. y ph -> A. y E. x ph )
MM> show proof qsfail /lemmon /renumber
1 ax6evr         $p |- E. x y = x
2 1 ax-gen       $a |- A. y E. x y = x
3 dtru           $p |- -. A. y y = x
4 3 nex          $p |- -. E. x A. y y = x
5 jcn            $p |- ( A. y E. x y = x -> ( -. E. x A. y y = x -> -. ( A. y E. x y = x -> E. x A. y y = x ) ) )
6 2,4,5 mp2      $p |- -. ( A. y E. x y = x -> E. x A. y y = x )
```

The brute-force search finds `ph(x, y) := x != y` on `{0, 1}` as a countermodel. `x = y` works
too.

History:

- Cauchy's sum theorem (*Cours d'analyse*, 1821) says a convergent series of continuous functions
  is continuous. Abel gave a counterexample in 1826. The repair, uniform convergence, moves
  `E. N` in front of `A. x`. Lakatos discusses it in *Proofs and Refutations* (appendix 1). As an
  exercise, write continuity and uniform continuity of `f` on an interval as quantifier strings,
  and identify the shift. No proof is needed.
- Aristotle, *Nicomachean Ethics* I.1–2: "every action aims at some good" slides to "some good is
  aimed at by every action." The name "quantifier shift fallacy" is often credited to Geach
  (check).
- There is also a connection to *quantified modal logic*, which has both
  object quantifiers and a necessity operator. Read `A. y` as `[]` while
  retaining `A. x` as an object quantifier. Then `ax-11` has the shape
  `A. x []ph -> []A. x ph`, called the Barcan formula. This is a new
  interpretation, beyond the one-operator comparison in E1–E3. Its validity
  depends on how the domains of objects relate across accessible worlds.

### E7 Substitution as a schema (set.mm)

> [!WARNING]
> This section is AI-generated and has not been reviewed.

There is a second kind of “unprovability” to distinguish from E2. A textbook
may prove by induction on formulas that every concrete instance of a pattern
is derivable. For example, it treats atomic formulas, then shows how to extend
the result through negations, implications, and quantifiers. This is a
*metatheorem*: a recipe for constructing proofs, potentially with a different
proof for each formula.

A Metamath theorem with `ph` in it asks for one finite proof that works directly
for an arbitrary wff substituted for `ph`. Metamath's substitution mechanism
does not itself inspect the structure of `ph` or perform that induction.
Consequently, “every concrete instance has a proof” and “this scheme has a
single Metamath proof from these schemes” are different claims.

That distinction explains the auxiliary predicate-calculus axioms. The local
`set.mm` discussion “Logical redundancy of ax-10, ax-11, ax-12, ax-13” says that
Tarski's system proves their concrete object-language instances with the
required distinct-variable conditions, while the
additional schemes support direct proofs at the level of Metamath variables.
It reports a necessity result for `ax-12` at this scheme level and open
questions for the other three. This is compatible with ordinary first-order
completeness. In particular, the cautious comment on `sp` in E4 should not be
upgraded into a proved independence theorem about `sp` itself. See also the
[Metamath commentary on specialization](https://us.metamath.org/mpeuni/sp.html).

`[ t / x ] ph` is "`ph` with `t` substituted for `x`." `sb6` shows it is the pattern from 5.0.4:
`A. x ( x = 0 -> ph )` in `ax-peano` already meant `[ 0 / x ] ph`. Reprove these in `set.mm`:

```metamath
${ $d x t $.  sb6 $p |- ( [ t / x ] ph <-> A. x ( x = t -> ph ) ) $= ? $. $}
sbequ12 $p |- ( x = y -> ( ph <-> [ y / x ] ph ) ) $= ? $.
${ equsal.1 $e |- F/ x ps $.  equsal.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
   equsal $p |- ( A. x ( x = y -> ph ) <-> ps ) $= ? $.
   equsex $p |- ( E. x ( x = y /\ ph ) <-> ps ) $= ? $. $}
```

#### Hints

- `sb6`: `bitri` through `dfsb`, which is
  `( [ t / x ] ph <-> A. y ( y = t -> A. x ( x = y -> ph ) ) )`. The remaining goal collapses
  the outer `A. y ( y = t -> ... )`. `equsalvw` does that, given the implicit substitution
  `( y = t -> ( A. x ( x = y -> ph ) <-> A. x ( x = t -> ph ) ) )`. Build it with `albidv`,
  `imbi1d`, and `equequ2`.
- `sbequ12`: `impbid` with `sbequ1` and `sbequ2`.
- `equsal`: `3bitr4i` with three facts. `19.23` (from `equsal.1`) gives
  `( A. x ( x = y -> ps ) <-> ( E. x x = y -> ps ) )`. `albii` of `pm5.74i` of `equsal.2` swaps
  `ph` for `ps` under `x = y ->`. `a1bi` with `ax6e` removes `E. x x = y ->`.
- `equsex`: `impbii`. Forward: `exlimi` reduces it to `( ( x = y /\ ph ) -> ps )`, which is
  `biimpa` of `equsal.2`. Reverse: `sylbir` with `equsal` reduces it to `equs4`.

References:

- Tarski, "A simplified formalization of predicate logic with identity" (1965).
- Kalish and Montague, "On Tarski's formalization of predicate logic with identity" (1965).
- Megill, "A finitely axiomatized formalization of predicate calculus with equality," *Notre
  Dame J. Formal Logic* 36 (1995).
- The `set.mm` section "Logical redundancy of ax-10, ax-11, ax-12, ax-13" (around line 18440).

### E8 Capstone: cylindric algebra axioms (set.mm)

> [!WARNING]
> This section is AI-generated and has not been reviewed.

Cylindric algebras express quantifier laws as algebraic identities. Think of a
formula as the set of assignments that make it true. Conjunction becomes
intersection, negation becomes complement, and implication corresponds to
inclusion. Existential quantification `c_x` enlarges a set of assignments:
an assignment belongs to `c_x a` if changing just its `x` value can make it
belong to `a`. The name “cylindric” comes from letting that coordinate vary
freely, as when extending a region into a cylinder.

Write `0` for false, `1` for true, `a · b` for conjunction, `-a` for negation,
and `a <= b` for implication. Algebraic equality here means logical
equivalence. The element `d_xy` represents the formula `x = y`.

The seven laws below are exercises labeled C1–C7 locally; the labels should
not be assumed to match a particular textbook's axiom numbering. For the
algebraic theory, the reference is Henkin, Monk, and Tarski, *Cylindric
Algebras* (1971).

- **C1:** `c_x 0 = 0`. Quantifying an impossible condition cannot produce a
  witness. Prove `-. E. x F.`.
- **C2:** `a <= c_x a`. The current value of `x` supplies a witness whenever
  `a` holds. Find `( ph -> E. x ph )`.
- **C3:** `c_x (a · c_x b) = c_x a · c_x b`. The statement “some x satisfies
  b” no longer depends on the current `x`, so it can be taken outside another
  existential quantifier over `x`. Prove
  `( E. x ( ph /\ E. x ps ) <-> ( E. x ph /\ E. x ps ) )`.
- **C4:** `c_x c_y a = c_y c_x a`. Two existential quantifiers commute.
  Find `( E. x E. y ph <-> E. y E. x ph )`.
- **C5:** `c_x d_xy = 1`. There is an `x` equal to `y`. Find `E. x x = y`.
- **C6:** `d_xy = c_z (d_xz · d_zy)`, with `z` distinct from `x` and `y`.
  Two objects are equal exactly when some object equals both. Prove
  `( x = y <-> E. z ( x = z /\ z = y ) )`.
- **C7:** `c_x (d_xy · a) · c_x (d_xy · -a) = 0`, with distinct variable
  names `x` and `y`. Fixing `x` equal to `y` cannot make `a` both true and
  false. Prove `-. ( E. x ( x = y /\ ph ) /\ E. x ( x = y /\ -. ph ) )`.
  Distinct variable names do not require distinct values.

The “find” exercises are `19.8a`, `excom`, and `ax6ev`. Search with
`search * "..."`. Add the new statements to a copy of `set.mm`, after the
lemmas they use:

```metamath
cylc1 $p |- -. E. x F. $= ? $.
cylc3 $p |- ( E. x ( ph /\ E. x ps ) <-> ( E. x ph /\ E. x ps ) ) $= ? $.
${ $d x z $.  $d y z $.
  cylc6 $p |- ( x = y <-> E. z ( x = z /\ z = y ) ) $= ? $. $}
${ $d x y $.
  cylc7 $p |- -. ( E. x ( x = y /\ ph ) /\ E. x ( x = y /\ -. ph ) ) $= ? $. $}
```

#### Hints

- `cylc1`: `nex` leaves `-. F.`.
- `cylc3`: one application of `19.41` (`E. x ( ph /\ ps ) <-> ( E. x ph /\ ps )`, given
  `F/ x ps`). The remaining goal is nonfreeness of `x` in `E. x ps`.
- `cylc6`: search for the shape `( x = y <-> E. z ( ... ) )`. The library version has
  `z = x`, not `x = z`. So `bitri` through it, and fix the gap with `exbii`, `anbi1i`, and
  `equcom`.
- `cylc7`: C7 says substitution is a function: `y` cannot both satisfy and fail `ph`. `mtbir`
  reduces the goal to a contradiction `-. ( [ y / x ] ph /\ -. [ y / x ] ph )` (`pm3.24`) plus a
  biconditional; fix the contradiction with `let`. `anbi12i` splits the biconditional. Each half
  is `sb5` (`( [ y / x ] ph <-> E. x ( x = y /\ ph ) )`). The second half also needs `sbn` to
  move the negation out of `[ y / x ]`.

#### Answers

```
MM> show proof cylc7 /lemmon /renumber
1 pm3.24         $p |- -. ( [ y / x ] ph /\ -. [ y / x ] ph )
2 sb5            $p |- ( [ y / x ] ph <-> E. x ( x = y /\ ph ) )
3 2 bicomi       $p |- ( E. x ( x = y /\ ph ) <-> [ y / x ] ph )
4 sb5            $p |- ( [ y / x ] -. ph <-> E. x ( x = y /\ -. ph ) )
5 sbn            $p |- ( [ y / x ] -. ph <-> -. [ y / x ] ph )
6 4,5 bitr3i     $p |- ( E. x ( x = y /\ -. ph ) <-> -. [ y / x ] ph )
7 3,6 anbi12i    $p |- ( ( E. x ( x = y /\ ph ) /\ E. x ( x = y /\ -. ph ) ) <-> ( [ y / x ] ph /\ -. [ y / x ] ph ) )
8 1,7 mtbir      $p |- -. ( E. x ( x = y /\ ph ) /\ E. x ( x = y /\ -. ph ) )
MM> show proof cylc6 /lemmon /renumber
1 equvinv        $p |- ( x = y <-> E. z ( z = x /\ z = y ) )
2 equcom         $p |- ( z = x <-> x = z )
3 2 anbi1i       $p |- ( ( z = x /\ z = y ) <-> ( x = z /\ z = y ) )
4 3 exbii        $p |- ( E. z ( z = x /\ z = y ) <-> E. z ( x = z /\ z = y ) )
5 1,4 bitri      $p |- ( x = y <-> E. z ( x = z /\ z = y ) )
```

The rest:

- `cylc1`: `fal nex`.
- `cylc3`: `nfe1 19.41`.

History: Tarski's program to algebraize logic, continuing Boole, Peirce, and Schröder. Halmos's
polyadic algebras (1950s) were a rival algebraization.

### E9 Russell's paradox, barber form

> [!WARNING]
> This section is AI-generated and has not been reviewed.

This states that no set `y` contains exactly those sets that do not contain
themselves. If such a `y` existed, asking whether `y` contains itself would
give `y e. y <-> -. y e. y`. The contradiction rules out that proposed set;
it does not make set theory inconsistent. After chapter 5.2.4, add to a copy
of `set.mm`:

```metamath
${ $d x y $.
  rubarber $p |- -. E. y A. x ( x e. y <-> -. x e. x ) $= ? $.
$}
```

Hint: `nex` leaves `ru0`. Answer:
`vx cv vy cv wcel vx cv vx cv wcel wn wb vx wal vy vx vy ru0 nex`. It uses the same axioms as
`ru0`.

Related: `exnelv` (line 50372, revised April 2026) extracts the separation step from `nalset`.
`bj-ru1` and `bj-ru` (BJ's mathbox, around line 615740) are versions with minimized axiom use.
