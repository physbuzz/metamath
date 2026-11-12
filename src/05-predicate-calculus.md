---
title: "05 Variables, Binding, and Predicate Calculus"
---

<h1 id="05-predicate-calculus" style="border-bottom: none;">05 Variables, Binding, and Predicate Calculus</h1>

<nav class="nav">
    <span class="activenav"><a href="04-propmm.html">← Previous</a></span>
    <span class="activenav"><a href="index.html">↑ Up</a></span>
    <span class="activenav"><a href="06-setmm.html">Next →</a></span>
</nav>

---

> [!WARNING]
> AI-generated material has not been human-reviewed. Reference proofs are
> mechanically checked; exercise files intentionally contain blanks.


@toc

# 5 Variables, Binding, and Predicate Calculus

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
earlier exercises and leaves just the five new targets below blank.
`small-reference.mm` contains their completed solutions. The original
`src/code-04/myset.mm` remains your working file.

These are the entire additions to the language and axioms. `setvar` is a
syntactic type name; it introduces no set-theoretic axioms. `weq` constructs
variable-equality formulas, but we do not assume any laws of equality here.

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

This gives us a small toolkit for moving implications through quantifiers.
Specialization, existential operations, and bound-variable change need further
machinery. We will explore those in the full library next.

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
- `19.3v`: combine restricted specialization `spvw` and `ax-5` with `impbii`.
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
