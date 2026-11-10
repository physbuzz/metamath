
# 05 Metatheorems, notation, and history

*Working notes and problems to revisit. This chapter is intentionally unfinished;
sections need not yet form a continuous exposition.*

Chapter 04 was mostly code, with the program Metamath as the foundation. It's
difficult to talk about the history of logic without talking about things that are
surprisingly distant from this bootstrapping, and that take much, much more effort to
get to.

For these notes, our grounding is the 02 verifier and concrete proof files it
accepts. We can also discuss ordinary mathematical arguments, proposed
algorithms, and historical claims; none of those discussions is being
presented as a verified Metamath proof. I mark such claims **(to formalize)**.
The eventual task is to represent syntax, derivations, and verification as
data in a suitable Metamath database, and prove facts about them there.
That is much later work, perhaps around Chapter 14. Mario Carneiro's
formalizations and Metamath Zero are useful future references.

Three distinct achievements should not be conflated: (1) checking one
particular proof; (2) writing a program that takes proofs as input and emits
proofs as output; (3) proving inside a formal system that the program works
for all valid inputs. We can pursue them in that order.

## Object language and metalanguage

Logicians separate two levels. The *object language* is the formulas being studied;
in Metamath, these are the strings inside statements. The *metalanguage* is the
language used to talk *about* those formulas: English plus a few symbols. Statements
such as "this `$p` verifies" or "no proof of `|- M U` exists" belong to the
metalanguage. A large part of reading logic texts is noticing which level a symbol
belongs to. We can eventually make the metalanguage itself a formal
object language, by encoding formulas and proofs as data.

## Notation

**`⊢ φ`** conventionally means "φ is a theorem." This is a statement
about derivability, not a connective inside φ. Metamath's `|-` is just
a constant at the front of an expression. A Metamath statement
`|- ph` is distinct from a metalanguage claim
about the existence of a proof of some formula; it is the object we ask the
verifier to derive. We can later define an explicit `Provable(code)`
predicate in another formal language.

**`Γ ⊢ φ`** means "φ is deducible from Γ," where Γ is a set of
formulas. A `$p` with `$e` hypotheses gives an immediately useful
analogue, though the correspondence depends on the chosen encoding of
substitutions and hypotheses. Enderton uses `Γ; α` for adjoining an
assumption to Γ.

**Rule notation.** A rule of inference is often drawn with its premises above a line
and its conclusion below. Modus ponens:

```
  φ      φ → ψ
 ───────────────  MP
        ψ
```

This is the `ax-mp` block. A proof stacks rules like these into a tree. Metamath's
RPN proof is that tree written out in postorder, which is what the stack in the 02
verifier evaluates.

**Arrows.** The connective `→` is set.mm's `->`. Older books write it `⊃`, and
Mendelson writes it `⇒`. Elsewhere `⇒` means something else entirely: the sequent
arrow (see the sequent calculus section below), or just English "implies" in prose.

**`⊨`.** Conventional `Γ ⊨ φ` means that every valuation satisfying all
of Γ also satisfies φ; `⊨ φ` means that φ is valid under all valuations.
To investigate this concretely, define valuations, evaluation of syntax,
and then the satisfaction relation. Metamath can host those definitions;
we have not yet constructed them. `hol.mm` uses the characters `|=`
for something else: they are part of its actual assertions `|- R |= S`.

**Book differences.** Enderton's deductive calculus is in his first-order chapter, and
its propositional part takes every tautology (and its generalizations) as an axiom.
For a three-axiom Hilbert-style system like set.mm's, Mendelson's chapter 1 is the
closer match.

## More vocabulary

**Schema vs. atom.** In a textbook, a sentence symbol such as A₁ or p is one
particular propositional variable of the object language, while α ranges over all
formulas. set.mm has only the second kind. So every set.mm theorem is what a textbook
calls a *theorem schema*. Some authors call these "metatheorems," a weaker sense of
the word than the one below.

**"Deduction."** set.mm uses "inference" for a rule with bare hypotheses and
"deduction form" (suffix `d`) for the shared-antecedent version. A logician's
"deduction" is Enderton's: a finite sequence of formulas, each either in Γ, a logical
axiom, or obtained by modus ponens from earlier ones. A Metamath proof with `$e`
hypotheses gives a closely related schematic rule, but the exact
correspondence depends on how the system, substitutions, and hypotheses
are encoded. That correspondence is itself a useful question.

**Derivable vs. admissible.** A rule is called *derivable* when its
conclusion can be derived from its premises in the chosen calculus; a
`$p` with `$e` hypotheses is one convenient representation. It is
*admissible* if every substitution of theorem premises also has a
theorem conclusion. Derivability gives admissibility. Proving
admissibility can require a claim about all derivations, which we
have not formalized here.

**Metatheorem**: a mathematical result *about a formal system*, often
quantifying over formulas or derivations. The deduction theorem, MIU
nonderivability arguments, and cut elimination are examples. This is
vocabulary to recognize, not a claim that such results are forever
outside Metamath.

## The MIU system

The MIU system is described in chapter 1 of Hofstadter's *Gödel, Escher, Bach* (GEB).
`miu.mm` has good exposition. (Appendix D of the Metamath book, "The MIU system," is
just a copy of it, so open `miu.mm` instead.) There's also
[a Lean project](https://leanprover-community.github.io/mathlib4_docs/Archive/MiuLanguage/Basic.html)
that states "The principal aim of this project is to give a Lean proof that the
derivability of a string is a decidable predicate."

MIU's small rewriting rules make it useful for asking what *all possible*
derivations look like. This is a parking place for questions and ideas,
not a demand to prove nonderivability now.

```metamath
$c M I U |- wff $.
$v x y $.
wx $f wff x $.
wy $f wff y $.
we  $a wff $.
wM  $a wff x M $.
wI  $a wff x I $.
wU  $a wff x U $.
wxy $a wff x y $.
ax  $a |- M I $.
${ Ia   $e |- x I $.       I_  $a |- x I U $. $}
${ IIa  $e |- M x $.       II  $a |- M x x $. $}
${ IIIa $e |- x I I I y $. III $a |- x U y $. $}
${ IVa  $e |- x U U y $.   IV  $a |- x y $. $}
```

**Question 1.** Prove a theorem (the label is `miu.mm`'s):

```metamath
theorem1 $p |- M U I I U $= ? $.
```

**Question 2.** Prove a derived rule:

```metamath
${
  II2.1 $e |- M x $.
  II2 $p |- M x x x x $= ? $.
$}
```

*Hint:* use `II` twice. The second use substitutes `x x` for `x`, which needs `wxy`.

**Question 3 (later).** For any specific k, construct a proof of
`M I^(2^k)` (for example k = 3). A more ambitious claim ranges over
all k: write a program that produces the corresponding proof, and
later represent and justify that program's operation formally.

**Question 4 (later).** Formalize the claim that `|- M U` has no derivation.
**(to formalize)**

*Informal lead:* count `I`s modulo 3 and examine how each rule transforms
that count. GEB gives the conventional argument (p. 260); the future goal
is an explicit formal theorem about encoded derivations.

**Question 5 (later).** Formalize the proposed complete characterization:
a string is MIU-derivable exactly when it begins with a single `M`, has
only `I`s and `U`s thereafter, and its `I` count is nonzero modulo 3.
**(to formalize)** The necessity and sufficiency directions require
different constructions. The earlier guided worksheet suggested
starting with `MI^n` for every positive n not divisible by 3 and then
introducing the target `U`s by replacing triple `I`s.

**Question 6 (later).** Consider the proposed rule "from `|- M U`,
infer `|- U`." Investigate its admissibility given Q4 and whether
the following rule can be derived:

```metamath
${
  bad.1 $e |- M U $.
  bad $p |- U $= ? $.
$}
```

**(to formalize)**. *Informal lead:* every string derivable from the
axiom together with a hypothesis `M U` begins with `M`. The precise
nonderivability and admissibility statements remain to be encoded.

## The deduction theorem

In Enderton's notation:

> If Γ; α ⊢ β, then Γ ⊢ (α → β).

The usual informal argument is by induction on the deduction of β. Rewrite every line χ as
`α -> χ`. There are three cases, and chapter 04 proved a tool for each:

- the line is α itself: use `id`.
- the line is an axiom, another hypothesis, or an earlier theorem: use `a1i`.
- the line follows by modus ponens from earlier lines: use `mpd`.

For proofs using derived rules, one can expand them back to primitive
rules, or arrange suitable deduction-form replacements. This motivates
the many `i`/`d` variants in `set.mm`. Chapter 04 Question 14 used a
particular replacement. The general correctness of the transformation
is **(to formalize)**.

The proposed proof methods have a useful common shape: reason over an
arbitrary derivation. MIU's Q4 suggests an invariant preserved by the rules;
the deduction theorem suggests a procedure transforming proof objects.
Neither claim is itself one of the ordinary MIU or propositional `$p`
statements written so far. Once derivations are represented as data in a
richer database, both become candidates for explicit formalization. MIU
has no implication connective in the language shown, so the usual
implication-form version of the deduction theorem is not a statement in
that particular language.

Predicate logic adds a complication. set.mm has the rule `ax-gen`: from `|- ph`, infer
`|- A. x ph`. Applying the naive deduction theorem to it would give
`|- ( ph -> A. x ph )`, which is false when `ph` is `x = y`. So with generalization,
the theorem needs a side condition: you can't generalize on a variable that is free in
the hypothesis being discharged. Propositional logic has no generalization rule, so
this never came up in chapter 04.

## Sequent calculus

A Hilbert-style system manipulates formulas, and assumptions live outside them, in
the metalanguage. A *sequent calculus* (Gentzen, 1934) manipulates *sequents*,
`Γ ⇒ Δ`, read as "if everything in Γ holds, then something in Δ holds." Some books
write `Γ ⊢ Δ` instead. The assumptions are now part of the object language, so
moving an assumption into an antecedent becomes an ordinary rule. Each connective
has a *left* rule (how to use it) and a *right* rule (how to prove it). The right
rule for `→` is

```
   Γ, φ ⇒ ψ, Δ
 ───────────────  →R
   Γ ⇒ φ → ψ, Δ
```

Propositional sequent calculus fits in Metamath with no `$d`:

```metamath
$c ( ) -> -. wff ctx |- => $.
$v ph ps ch th $.
$v G H D E $.
wph $f wff ph $.
wps $f wff ps $.
wch $f wff ch $.
wth $f wff th $.
vG $f ctx G $.
vH $f ctx H $.
vD $f ctx D $.
vE $f ctx E $.
wn $a wff -. ph $.
wi $a wff ( ph -> ps ) $.
c0 $a ctx $.
cadd $a ctx G ph $.
ax-id $a |- G ph H => D ph E $.
${
  ax-negl.1 $e |- G H => D ph E $.
  ax-negl $a |- G -. ph H => D E $.
$}
${
  ax-negr.1 $e |- G ph H => D E $.
  ax-negr $a |- G H => D -. ph E $.
$}
${
  ax-impl.1 $e |- G H => D ph E $.
  ax-impl.2 $e |- G ps H => D E $.
  ax-impl $a |- G ( ph -> ps ) H => D E $.
$}
${
  ax-impr.1 $e |- G ph H => D ps E $.
  ax-impr $a |- G H => D ( ph -> ps ) E $.
$}
```

A `ctx` is a list of wffs: `c0` is the empty list, and `cadd` appends one wff. Every
wff is a variable, starts with `-.`, or is wrapped in parentheses, so a list of wffs
can be split up only one way and needs no commas. `G ph H` means "a context with `ph`
somewhere in it." Every rule acts at any position, so no reordering rule is needed.

`ax-id` is the axiom `φ ⇒ φ` with extra context. The other four rules are ¬L, ¬R, →L
and →R. There are no *structural rules* (weakening, contraction, exchange); logicians
call a system like this *G3-style*.

Here is `ph ⇒ ph` turned into `⇒ ( ph -> ph )`. All four contexts are empty (`c0`),
and the first `wph wph` gives the substitutions for `ph` and `ps` in `ax-impr`:

```metamath
seqid $p |- => ( ph -> ph ) $=
  wph wph c0 c0 c0 c0 wph c0 c0 c0 c0 ax-id ax-impr $.
```

A context with two formulas, `ph ps`, has the syntax proof `wps wph c0 cadd cadd`.
Matching a rule like `G ph H => ...` against a sequent can succeed in several ways
(where does `G` end?), so a proof assistant may ask you to choose, as with `miu.mm`.
By default mmj2 expects every `|-` statement to parse as a `wff`, so use
`metamath.exe` or the 02 checker.

**Question 7.** Prove `ax-1`, `ax-2` and `ax-3` as sequents, then Peirce's law and
double negation elimination.

```metamath
seqax1 $p |- => ( ph -> ( ps -> ph ) ) $= ? $.

seqax2 $p |- => ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $= ? $.

seqax3 $p |- => ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $= ? $.

seqpeirce $p |- => ( ( ( ph -> ps ) -> ph ) -> ph ) $= ? $.

seqnotnotr $p |- => ( -. -. ph -> ph ) $= ? $.
```

*Hint:* work from the bottom up (logicians say *backward* or *root-first* proof
search). The last step is always `ax-impr`. After that, pick any compound formula and
apply its rule backwards; each step makes the sequent smaller. Stop when the same
formula appears on both sides, and use `ax-id`. For `seqpeirce`, the `ax-impl` step
puts `( ph -> ps )` on the right, next to `ph`. Compare its five steps with chapter
04's Question 25.

**Question 8 (later).** Investigate whether weakening can be expressed as a derivable rule in this calculus:

```metamath
${
  wk.1 $e |- G => D $.
  wk $p |- G ph => D $= ? $.
$}
```

Look at the shape of each rule's conclusion. Then show that weakening is admissible
**(to formalize)**.

**Question 9 (later).** Investigate the attempted modus-ponens sequent rule. Which
rule could have `=> ps` as its conclusion?

```metamath
${
  seqmp.1 $e |- => ph $.
  seqmp.2 $e |- => ( ph -> ps ) $.
  seqmp $p |- => ps $= ? $.
$}
```

A candidate additional rule is *cut*, which lets us use a lemma:

```metamath
${
  ax-cut.1 $e |- G => D ph $.
  ax-cut.2 $e |- H ph => E $.
  ax-cut $a |- G H => D E $.
$}
```

**Question 10.** With `ax-cut` added, prove `seqmp`.

*Hint:* first prove `|- ph ( ph -> ps ) => ps` with one `ax-impl` and two `ax-id`s.
Cut that against `seqmp.2` to get `|- ph => ps`, then cut against `seqmp.1`.

**Cut elimination** (Gentzen's *Hauptsatz*) says that every sequent derivable with
`ax-cut` is derivable without it **(to formalize)**. Like the deduction theorem, it transforms
derivations. Three consequences, all **(to formalize)**:

- *The subformula property.* Every formula in a cut-free derivation is a piece of the
  final sequent. That's how `seqmp` can be admissible without being derivable. Taking
  modus ponens out of chapter 04's system, by contrast, would leave only axiom
  instances.
- *Consistency.* No rule concludes the empty sequent `|- =>`, so it has no cut-free
  derivation. The sequent proofs of `ax-1`–`ax-3`, together with `seqmp`, translate
  chapter 04's theorems into sequents. If chapter 04's system proved both φ and `-. φ`,
  two cuts would give `|- =>`. This argument never mentions truth tables.
- *A decision procedure.* Backward search always terminates, because every rule's
  premises have fewer connectives than its conclusion. A G3 prover in the SICP query
  language from 03, printing proofs that the 02 checker verifies, would be a good
  project.

For quantifiers, the ∀-right rule normally needs the proviso that `x` doesn't occur in the
context. In Metamath that's a `$d`:

```metamath
${
  $d x G $.  $d x H $.  $d x D $.  $d x E $.
  ax-allr.1 $e |- G H => D ph E $.
  ax-allr $a |- G H => D A. x ph E $.
$}
```

Without the `$d`, this rule would prove `ph ⇒ ∀x ph`, which is the `ax-gen` mistake
from the deduction theorem section, in sequent form.

## A note on hol.mm

hol.mm writes assumptions into its statements, as in `|- R |= S`, much like a sequent.
There, modus ponens for `==>` is a theorem (labeled `mpd`) proved from the definition
of implication. The primitive rule is `ax-eqmp`, modus ponens for equality.

## Threads to research

- Gentzen's sequent calculus and cut elimination (1934).
- Church's λ-calculus, Gödel–Herbrand recursive functions and Turing machines:
  different precise models of computability, related by formal translations.
  Study which equivalences were established as theorems, and which broader
  assertions are summarized by the Church–Turing thesis.
- Curry–Howard: study explicit correspondences between selected proof
  calculi and typed program calculi, not a blanket identity of every
  notion of proof and program.
- De Bruijn's Automath (from 1967), and the *de Bruijn criterion*: a
  small, independently understandable proof-checking component.
- Mizar (1973), LCF (Milner, 1970s), and the Boyer–Moore prover. Shankar
  mechanically checked Gödel's incompleteness theorem in the Boyer–Moore prover in
  1986.
- Mario Carneiro: `set.mm`'s developments about Metamath systems, and
  Metamath Zero. Find concrete statements, proof encodings, and verified
  translations to work through.
- Why logic texts state metatheory in English. Mechanization had real
  historical costs; the traditional mathematical treatment is also an
  intentional and useful research convention. This project chooses a
  more operational starting point.
- A useful primary-source example: the introduction to Solovay's
  [Peano arithmetic `peano.mm`](https://raw.githubusercontent.com/pbrosnan/ntg/15332ee0dfe50ada14b6e31e947272232e4dc671/peano.mm)
  explicitly separates formal Metamath statements from informal
  metamathematical arguments and observes that those arguments could
  be formalized in primitive recursive arithmetic. The source even
  identifies semantic justification of some axioms as work left to the
  reader. This is an unusually direct historical example of the
  distinction these notes are tracking.

## Claims left for later formalization

- `⊨`, truth tables, and any statement relating them to `⊢`.
- MIU nonderivability, admissibility, and the complete characterization (Questions 4–6).
- The deduction theorem, for all proofs, and its side condition for generalization.
- Weakening is admissible in the sequent calculus above.
- Cut elimination, the subformula property, the consistency argument, and
  decidability.
- Peirce's law can't be proved from `ax-1` and `ax-2` alone (chapter 04, Question 25).
  The usual proof uses a many-valued truth table.

## Additional exercises for later (requires quantifiers and `$d`)

The [Number Theory Game for Metamath](https://github.com/pbrosnan/ntg)
by Patrick Brosnan is a `.mm` development inspired by the Natural Number
Game, using Robert Solovay's Peano arithmetic. The more detailed practice
route used the repository at
[commit `15332ee...`](https://github.com/pbrosnan/ntg/blob/15332ee0dfe50ada14b6e31e947272232e4dc671/README.md).
These are **not Chapter 04 exercises**: the induction problems require
quantifiers and disjoint-variable declarations. Retain the following targets
for a later arithmetic chapter.

In this database `+ a b` is prefix notation for `a+b`, `S t` is successor,
and `= s t` is equality. `var` is a type for object-language variable names;
`term` is the type for arbitrary arithmetic terms. Syntax helpers include
`tvar`, `tzero`, `tsucc`, `binop_plus`, `tbinop`, `binpred_equals`, and
`wff_atom`. The order of proof-stack inputs to `tbinop` is its two terms,
then the operator.

**`nn26l1`** ([source](https://github.com/pbrosnan/ntg/blob/15332ee0dfe50ada14b6e31e947272232e4dc671/peano.mm#L2884-L2891)):
prove the addition identity `(a+b)+0 = a+(b+0)` without assuming
associativity, by composing the zero law with congruence. The old worksheet
used target `expa1`, but use the source's actual label when building the
appropriate exercise database.

```metamath
nn26l1 $p |- = + + a b 0 + a + b 0 $= ? $.
```

**`pa_ax3cl2`** ([source](https://github.com/pbrosnan/ntg/blob/15332ee0dfe50ada14b6e31e947272232e4dc671/peano.mm#L2817-L2820)):
the implication `t=0+t -> S(t)=0+S(t)`, using successor congruence and
the addition-successor law. The old worksheet called it `expa2`.

```metamath
pa_ax3cl2 $p |- implies = t + 0 t = S t + 0 S t $= ? $.
```

**`pa_ax3c`** ([source](https://github.com/pbrosnan/ntg/blob/15332ee0dfe50ada14b6e31e947272232e4dc671/peano.mm#L2812-L2835)):
use the already proved induction rule `nindd` to establish `t=0+t`.
Its induction interface expects a base case, a successor step, and
substitution-compatibility lemmas. The old worksheet used `expa3` and
supplied `pa_ax3cl1`, `pa_ax3cl3`, and `expa2`. The distinct-variable
requirements include `(x,y)`, `(y,t)`, and restrictions involving the
formulas substituted for `phi`.

**`addcom`** ([source](https://github.com/pbrosnan/ntg/blob/15332ee0dfe50ada14b6e31e947272232e4dc671/peano.mm#L2930-L2959)):
prove `a+b=b+a` by induction using the two zero laws and the two
successor-distribution laws; the worksheet supplied the substitution
compatibility lemma `addcom_sub`. Its old target was `expa4`.

The former worksheet pointed to support and solved files named
[sources/ntg-practice-support.mm](sources/ntg-practice-support.mm) and
[sources/ntg-practice-solutions.mm](sources/ntg-practice-solutions.mm).
**Those paths refer to an external exercise bundle, not files bundled
with this chapter.** The source repository and linked theorem locations
are the persistent references.

## Other proof-system puzzles to revisit

A small *context-sharing* sequent calculus in the prior worksheet used
`seq G => A` as its assertion, with `sid`, implication-left `il`, and
`cut` primitive. There, the target `mp` (from `seq G => A` and
`seq G => ( A -> B )`, derive `seq G => B`) can be built with `sid`,
`il`, and `cut`. Unlike `hol.mm`'s `mpd`, this was original instructional
code, not a named theorem from a published database. Useful when we want
a minimal alternative architecture.

The supplementary geometrical exercise is original Metamath code built
from Tarski-style segment congruence. Its two rules say `Cg A B B A` and,
from `Cg A B C D` with `Cg A B E F`, infer `Cg C D E F`. The target is
`Cg A B A B`. Keep this as a non-propositional system to implement,
not as a named theorem from `set.mm`.
Sources: [`set.mm`'s Tarski geometry](https://us.metamath.org/mpeuni/df-trkg.html)
and [GeoCoq's Tarski axioms](https://geocoq.github.io/GeoCoq/html/GeoCoq.Axioms.tarski_axioms.html).

The last guided Meredith problem was a **claim of equivalence of proof
systems**, not just a theorem in one system. It compares the Church P₂
presentation H (`ax-1`, `ax-2`, `ax-3`), Meredith's single-axiom system M,
and Łukasiewicz's three-axiom system L (`luk-1`–`luk-3`). The specific
derivations are:

- H proves M: see [Meredith's theorem](https://us.metamath.org/mpeuni/meredith.html)
  and the old source path [sources/church-to-meredith.mm](sources/church-to-meredith.mm).
- M proves the three L schemas: [sources/meredith-only.mm](sources/meredith-only.mm).
- L proves the H schemas: [sources/lukasiewicz-only.mm](sources/lukasiewicz-only.mm),
  with `ax1`, `ax2`, `ax3` as the key labels.

The further step is to state precisely what 'same theorems' means and build
a translation that replaces an axiom instance with a known derivation,
preserving modus-ponens steps. Checking several instance translations is
one project; formalizing that it works for all proofs is another.
The `sources/` links above are retained pointers from the earlier
exercise collection, **not files included with this Markdown file**.

## Formalization work to recover later

These are project prompts, not conclusions:

- Encode a database's syntax and derivations as data (possibly inside `set.mm`).
  Define 'a valid proof of statement X exists', then state MIU's
  nonderivability result in that language. Investigate the
  [Mathlib MIU formalization](https://leanprover-community.github.io/mathlib4_docs/Archive/MiuLanguage/Basic.html).
- Compare a **verified proof of one instance**, a **proof-producing program**,
  and a **verified theorem about all outputs**. The bridge between them is
  itself a worthwhile formalization target.
- Write proof translators: Hilbert proofs to sequent proofs; proofs with
  assumptions to implication proofs; proofs using cut to cut-free proofs.
  Measure proof-size overhead as well as correctness.
- Define a truth assignment as actual data, with an evaluation operation
  on syntax trees. Study both `Γ ⊨ φ` and `Γ ⊢ φ` only after defining
  their respective objects. Then express soundness and completeness
  as claims relating the two representations.
- Explore when two different deductive systems are equivalent as sets
  of derivable formulas, as categories of proofs, or as algorithms for
  constructing proofs. These are *different questions*. Explicit
  translations may eliminate what first appeared to be a disagreement
  in notation, while leaving genuine computational differences.
- Investigate formalizations of proof checkers and metatheory by
  Mario Carneiro (including Metamath Zero) before committing to a
  representation of provability.

## Source and reading pointers retained from the earlier exercises

The original guided collection links to the following material; keep
these references even when the associated exercise is deferred:

- Hofstadter's [*GEB* Chapter I excerpt](https://www.ratiocination.org/Courses/phil3505/wp-content/uploads/2017/08/Hofstadter__Godel-Escher-Bach-excerpt-on-MU-puzzle.pdf),
  [*Metamath* Appendix D](https://us.metamath.org/downloads/metamath.pdf#page=225),
  and [`miu.mm`](https://us.metamath.org/metamath/miu.mm).
- The original small-exercise source locations for [`a1i`](https://us.metamath.org/mpeuni/a1i.html),
  [`id`](https://us.metamath.org/mpeuni/id.html),
  [`mpd`](https://us.metamath.org/mpeuni/mpd.html),
  [`syl`](https://us.metamath.org/mpeuni/syl.html),
  [`pm2.43i`](https://us.metamath.org/mpeuni/pm2.43i.html), and
  [`pm2.21i`](https://us.metamath.org/mpeuni/pm2.21i.html).
- The separate exercise bundle's
  [sources/hol-practice.mm](sources/hol-practice.mm) and
  [sources/iset-practice.mm](sources/iset-practice.mm) are reference names,
  not files included with this chapter.

## Answers and further work

(To be written as exercises are attempted.)