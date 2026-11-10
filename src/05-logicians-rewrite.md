---
title: "05 Talking to Logicians: Folk Knowledge, Notation, and History"
---

<h1 id="05-logicians" style="border-bottom: none;">05 Talking to Logicians: Folk Knowledge, Notation, and History</h1>

<nav class="nav">
    <span class="activenav"><a href="04-propmm.html">← Previous</a></span>
    <span class="activenav"><a href="index.html">↑ Up</a></span>
    <span class="inactivenav" aria-disabled="true">Next →</span>
</nav>

> [!NOTE]
> Draft rewrite of chapter 05. It absorbs the MIU and sequent calculus sections
> of chapter 04 (4.2.4, 4.2.5), so those can be deleted there.

@toc

# 5 Talking to Logicians

Everything in chapter 04 was a `$p` statement that the chapter 03 verifier
accepted. A logic textbook is mostly a different kind of object: English claims
*about* what can and can't be proved. "MU is not derivable." "Any proof from a
hypothesis can be converted into a proof of an implication." "This system is
consistent."

None of those is a `$p` in any file we have. This chapter learns the
vocabulary, the notation, and the history anyway, because that is how
logicians talk. The one rule is that every claim is labelled by what the
verifier has actually seen.

## 5.1 Ground rules

### 5.1.1 Three tags

| Tag | The claim is... | How it gets upgraded |
| --- | --- | --- |
| **[checked]** | "this file verifies", and it does. | Nothing to do. |
| **[IOU]** | that one specific `$p` has a proof, which nobody has written down yet. | Write the proof, run the verifier. |
| **[folk]** | about *all* proofs, or about the *absence* of a proof. | Needs a new database in which proofs are themselves the objects (section 5.8). |

"Folk" doesn't mean doubtful. Every folk claim in this chapter is standard,
and I'd be astonished if any were wrong. The tag records how much of it the
verifier has seen, which is none of it. Until section 5.8 is carried out,
*metatheorem* is itself a folk word: it's what logicians call these claims,
and we have no definition of it.

### 5.1.2 Two kinds of folk claim

**Recipes.** "Any proof of this shape can be turned into a proof of that
shape." The deduction theorem, cut elimination, completeness, and "these two
axiom systems prove the same things" are all recipes.

A recipe never has to be believed. Each *use* of it is an IOU: apply the
recipe to the one proof you care about, and check the result. A program that
implements the recipe is an untrusted helper; only its output goes through
the verifier. If the program is wrong, the verifier says so.

**Barriers.** "No proof of X exists." MU, consistency, "Peirce's law doesn't
follow from `ax-1` and `ax-2`" are barriers. There is no IOU to cash. A search
that fails is not something the verifier can look at.

So the stubborn position has a comfortable half and an uncomfortable half.
Recipes can be tolerated as folk knowledge indefinitely, because they pay out
in checked proofs whenever asked. Barriers are where the real debt is.

### 5.1.3 The closure clause

Why are barriers different? A `.mm` file lists the steps that are allowed.
Nowhere does it say "and nothing else is a theorem." That sentence is a fact
about the verifier, not a statement in the file. Adding an `$a` can only make
more things provable, so no `$a` added to `miu.mm` could ever say that `M U`
is unprovable.

Every barrier argument in this chapter has the same four parts:

1. Pick a property P of strings.
2. Check that each rule, given premises with P, produces a conclusion with P.
   This is a finite check, one per rule.
3. Check that the target string lacks P.
4. *Closure:* theorems arise only by applying the rules, so every theorem
   has P, so the target is not a theorem.

Parts 1 to 3 are concrete. Part 4 is *induction on derivations*, and it is
the piece of folk reasoning this whole chapter leans on. Recipes need it too,
but only to argue that they work on every input, never for one use.

This also says what formalizing a barrier requires: a database where "theorem
of system S" is *defined* as the smallest set of strings closed under S's
rules, so that part 4 becomes a provable induction principle.

### 5.1.4 "How do you know your checker is right?"

You don't. You shrink what has to be trusted until it is small enough to
stare at, and you write a second one independently (chapter 03). This is the
*de Bruijn criterion*: a proof system should emit proof objects that a small,
separately written program can check. The same question applies to a referee's
brain; the difference is that the checker's trusted part is written down.
See Pollack, "How to believe a machine-checked proof" (1998).

In conversation, the position of these notes is roughly: "formal proofs are
finite strings checked by a mechanical procedure; I accept simple combinatorial
arguments about strings informally, and I treat the rest of the metatheory as
unformalized until it is machine-checked." Logicians will recognize this as
close to Hilbert's formalism, with *finitary* reasoning as the accepted
informal part. It is a respectable position with a long history, which is
next.

## 5.2 History

Dates are for orientation. Each entry says what it left behind in our files
or our vocabulary.

- **Frege, *Begriffsschrift* (1879).** The first formal system in the modern
  sense: axioms plus modus ponens. `ax-1` and `ax-2` are his. The turnstile
  `⊢` descends from his "judgment stroke."
- **Whitehead and Russell, *Principia Mathematica* (1910–13).** The source of
  labels like `pm2.43` (theorem ∗2.43), and of the fear of "wasting your
  undergrad proving 1+1=2."
- **Hilbert's program (1920s).** Treat proofs as finite strings and study
  them with elementary, *finitary* reasoning. Hilbert called this
  *Metamathematik*, the origin of the word. A *Hilbert system* is
  one with many axioms and very few rules, like chapter 04's. Textbook:
  Hilbert and Ackermann (1928).
- **Post (1921, 1943).** Truth tables, and the first proof that the
  propositional calculus proves exactly the tautologies. Later, *Post
  canonical systems*: pure string-rewriting rules. MIU is one, and a Metamath
  database is close to one.
- **Łukasiewicz (around 1930).** The three axioms `ax-1`, `ax-2`, `ax-3`,
  trimmed down from Frege's six. Meredith's single axiom is from 1953.
- **Herbrand, Tarski (1930).** The deduction theorem.
- **Gödel (1930, 1931).** Completeness of predicate logic. Then
  incompleteness, whose method is the one section 5.8 needs: encode formulas
  and proofs as data inside a system, so the system can talk about them.
- **Tarski (1933).** The object language / metalanguage split, and a
  definition of truth in a structure. `⊨` belongs to this tradition.
- **Gentzen (1934–35).** Natural deduction and the sequent calculus, built so
  that "deducible from assumptions" is itself an object the rules manipulate.
  Cut elimination (the *Hauptsatz*). Jaśkowski found natural deduction
  independently in 1934.
- **Church, Turing (1936).** Precise definitions of "mechanical procedure",
  and with them "decidable."
- **Kleene, *Introduction to Metamathematics* (1952).** Fixed much of the
  notation still in use, including `Γ ⊢ φ`. Lorenzen (1955) introduced
  *admissible* rules.
- **de Bruijn, Automath (1967 onward).** The first system for writing
  complete proofs that a computer checks. Van Benthem Jutting checked
  Landau's *Grundlagen der Analysis* in it (1977). The "de Bruijn criterion"
  was named later by Barendregt.
- **Mizar (1973), LCF (Milner, 1972 onward), Boyer–Moore.** LCF's idea is the
  recipe idea of 5.1.2: arbitrary untrusted programs may construct proofs,
  but only a small kernel can mint a theorem. Shankar checked Gödel's
  incompleteness theorem in the Boyer–Moore prover in 1986, an early case of
  a barrier-style result fully machine-checked.
- **Megill, Metamath (1990s).** Tarski's 1965 predicate calculus without
  "free variable" side conditions, plus Megill's own axioms (1995), in a
  system whose only built-in operation is substitution.
- **Checkers checking checkers (2006 onward).** Harrison, "Towards
  self-verification of HOL Light" (2006). Carneiro, "Models for Metamath"
  (2016) and Metamath Zero (2019), designed so that its verifier can be
  specified and proved correct in its own logic.

## 5.3 A dictionary

Left column: what a logician says. Right column: the nearest thing in our
files. The definitions are for recognition, not for proving anything.

### 5.3.1 Words

| Logician's term | Meaning | In our files |
| --- | --- | --- |
| object language | The formal strings being studied. | What appears after the typecode in a statement. |
| metalanguage | The language used to talk about them (usually English). | Comments, and these notes. |
| formula, wff | A string built by the grammar. | Anything with a `wff` syntax proof. |
| schema, metavariable | A pattern standing for all its instances. | Every statement with `ph` in it. Textbooks also have fixed atoms p, q; `set.mm` has none. |
| rule of inference | Premises and a conclusion. | An `$a` with `$e` hypotheses, such as `ax-mp`. |
| Hilbert system | Many axioms, few rules. | Chapter 04's database. |
| derivation, deduction, proof | A finite sequence or tree of formulas, each justified by a rule. | The RPN proof after `$=`, which is that tree in postorder. |
| theorem | A formula with a derivation. | A `$p` that verifies. |
| derivable rule | The conclusion can be derived from the premises. | A `$p` with `$e` hypotheses. **[checked]** when it verifies. |
| admissible rule | Whenever the premises are theorems, so is the conclusion. | Nothing. A recipe at best. |
| metatheorem | A claim about all derivations of a system. | Nothing yet (5.8). |
| valuation, truth assignment | A choice of true/false for each atom. | Nothing yet. |
| tautology | True under every valuation. | Nothing yet. |
| sound | Every theorem is a tautology. | Folk. The standard source of barriers. |
| complete | Every tautology is a theorem. | Folk recipe. |
| consistent | Some formula is not a theorem. | Folk barrier. |
| decidable | A program answers "theorem or not?" and always halts. | Recipe for "yes", barrier for "no". |
| independent | An axiom can't be derived from the others. | Folk barrier. |
| finitary | Elementary reasoning about finite strings; later pinned down as primitive recursive arithmetic (PRA). | The kind of informal argument these notes accept. |
| proof theory, model theory | The study of derivations; the study of structures and truth. | This chapter is nearly all proof theory. |

Two false friends. In `set.mm`, "deduction form" (suffix `d`) means the
shared-antecedent convention, and "inference" means a rule with bare
hypotheses; a logician's "deduction" is just a derivation from assumptions.
And some authors call every schema a "metatheorem", which is a much weaker
sense than the one above.

### 5.3.2 Symbols

- **`⊢ φ`**: "φ is a theorem." This is a metalanguage sentence. Metamath's
  `|-` is a declared constant at the front of a string. They are related by
  convention only.
- **`Γ ⊢ φ`**: "φ is derivable from the assumptions Γ." A `$p` with `$e`
  hypotheses is the checked analogue for a finite Γ of schemas. Enderton
  writes `Γ; α` for adding one assumption.
- **`Γ ⊨ φ`**: every valuation making all of Γ true makes φ true. A different
  claim from `⊢`; soundness and completeness are the two directions between
  them. The `|=` in `hol.mm` is unrelated: there it is a constant separating
  a context from a conclusion.
- **Rule notation**: premises above a line, conclusion below.

  ```text
    φ      φ → ψ
   ───────────────  MP
          ψ
  ```

- **Arrows**: `→` is our `->`. Older books write `⊃`. `⇒` can be the sequent
  separator, Mendelson's implication, or plain English "implies". `Γ ⇒ Δ` and
  `Γ ⊢ Δ` are both used for sequents.
- **`Γ, Δ`**: lists or sets of formulas. `⊥` is a constant for falsehood,
  which `set.mm`'s propositional axioms do without.

**Books.** For a three-axiom Hilbert system like ours, Mendelson chapter 1 is
the closest match. Enderton takes every tautology as an axiom, so his
propositional proofs look nothing like chapter 04. For sequent calculus,
Negri and von Plato, *Structural Proof Theory*.

## 5.4 Specimen: MIU, the smallest barrier

MIU is Hofstadter's toy system from *Gödel, Escher, Bach*. It is too simple
to hold interesting proofs, which makes it a clean display case. See
[`miu.mm`](https://us.metamath.org/metamath/miu.mm) (Appendix D of the
Metamath book is a copy of it).

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

`wff` here just means "string": `we` is the empty string, `wM`/`wI`/`wU`
append a letter, `wxy` concatenates. The rules: append `U` after a final
`I`; double everything after the `M`; replace `I I I` by `U`; delete `U U`.

**Question 1.** Prove these. Both become **[checked]**.

```metamath
theorem1 $p |- M U I I U $= ? $.

${
  II2.1 $e |- M x $.
  II2 $p |- M x x x x $= ? $.
$}
```

**Question 2.** `|- M I I I I I I I I` is an **[IOU]**; cash it. Then the
recipe: "for every k, `M` followed by 2^k `I`s is a theorem." Write the
program that prints the proof for a given k. The claim for all k stays
**[folk]**; each k you run is **[checked]**.

**The barrier.** `|- M U` has no proof. **[folk]** In the four-part form of
5.1.3:

1. P: the number of `I`s is not divisible by 3.
2. `ax` has one `I`. `I_` and `IV` don't change the count, `II` doubles it,
   `III` subtracts 3. None of these turns a non-multiple of 3 into a multiple.
3. `M U` has zero `I`s.
4. Closure.

Notice what the MIU language cannot do. It has no string that *says* "MU is
unprovable." The barrier isn't a missing `$p` in `miu.mm`; it isn't a
statement of `miu.mm` at all.

**Question 3.** The same shape, different outcomes:

```metamath
${
  bad.1 $e |- M U $.
  bad $p |- U $= ? $.
$}
```

Argue (folk) that `bad` can't be proved: find a property that every string
derivable from `ax` and `bad.1` has, and that `U` lacks. Then note that the
rule "from `M U` infer `U`" is nevertheless *admissible*, vacuously, because
its premise is never a theorem. *Derivable* means there is a proof from the
premises as `$e` hypotheses. *Admissible* only promises something when the
premises are outright theorems. Derivable is a checked notion; admissible is
a folk one.

**Folk, for the record.** The MIU theorems are exactly the strings `M`
followed by `I`s and `U`s whose `I`-count is not divisible by 3. One
direction is the barrier above; the other is a recipe. The
[Mathlib archive](https://leanprover-community.github.io/mathlib4_docs/Archive/MiuLanguage/Basic.html)
has all of this machine-checked in Lean, which is what a cashed-in version
looks like.

## 5.5 Specimen: the deduction theorem, the standard recipe

> If Γ; α ⊢ β, then Γ ⊢ (α → β). **[folk recipe]**

In our terms: a proof of `ps` using the hypothesis `$e |- ph` can be converted
into a proof of `|- ( ph -> ps )`. The recipe rewrites every line `ch` of the
old proof as `( ph -> ch )`, and chapter 04 already built a tool for each case:

- the line is the hypothesis `ph` itself: `id`;
- the line is an axiom or another hypothesis: `a1i`;
- the line came from `ax-mp`: `mpd` on the two rewritten lines.

The opposite direction is not folk at all. From `|- ( ph -> ps )` and a
hypothesis `|- ph`, one `ax-mp` gives `|- ps`. **[checked]**, every time.

Megill took the same hard line about this theorem. From the Metamath book:
"the Standard Deduction Theorem is invoked simply to claim that it can be
done in principle, without actually doing it." `set.mm` never invokes it.
Instead it uses *deduction style*: carry the antecedent `ph ->` on every line
from the start, and prove a `d` version of each rule (`mpd`, `syld`, `a1d`,
...). That is why chapter 04 was full of `i`/`d` variants: they are the
recipe, unrolled by hand, with each piece checked. See
[mmnatded](https://us.metamath.org/mpeuni/mmnatded.html).

**Question 4.** Take a chapter 04 inference with one hypothesis, say `con4i`
or `a1i`, apply the recipe by hand to its proof, and verify the resulting
closed theorem.

**Question 5 (project).** Write the recipe as a program for proofs that use
only `ax-1`, `ax-2`, `ax-mp`, and hypotheses. Run it on several inferences
from 4.1. This also answers the first TODO in 4.1.6.

**Preview.** With quantifiers, the recipe needs a side condition. `set.mm`
has `ax-gen`: from `|- ph` infer `|- A. x ph`. Rewriting that line naively
would produce `( ph -> A. x ph )`, which is wrong when `ph` is `x = y`.

### 5.5.1 The question from 4.1.6

There I asked: if I invent a symbol `=>` to mean "deduces" and write axioms
for it, why does anyone say I still need a metatheorem?

Split the worry into its three parts.

- *Everything my `=>` axioms prove corresponds to a real deduction.* Recipe.
- *Every real deduction is reflected by a `=>` proof.* Recipe.
- *When there is no deduction, `=>` says so.* Barrier. No set of `$a`
  statements can do this, by 5.1.3: axioms only add.

So the invented arrow does capture deduction, in both directions, in the
cashable sense. What it can't capture is the closure clause. That is the
whole philosophical gap, and it is the same gap as in MIU. The invented
arrow also already exists: it is Gentzen's.

## 5.6 Lab: sequent calculus

In a Hilbert system, assumptions live outside the formulas, in `$e`
statements. Gentzen's sequent calculus (1934) puts them in the string. A
*sequent* `Γ ⇒ Δ` has a list of formulas on each side, read as "if everything
on the left holds, something on the right holds." This is the place where the
existence of a deduction from assumptions is an ordinary object-language
statement, so it is the right lab for this chapter.

### 5.6.1 The database

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

A `ctx` is a list of wffs: `c0` is empty, `cadd` appends one. No commas are
needed, since every wff is a variable, starts with `-.`, or is wrapped in
parentheses. `G ph H` means "a list with `ph` somewhere in it", so each rule
works at any position.

Each connective has a *left* rule (how to use it as an assumption) and a
*right* rule (how to prove it). `ax-id` closes a goal when the same formula
appears on both sides. A worked example, with all contexts empty:

```metamath
seqid $p |- => ( ph -> ph ) $=
  wph wph c0 c0 c0 c0 wph c0 c0 c0 c0 ax-id ax-impr $.
```

The syntax proof of the two-formula context `ph ps` is `wps wph c0 cadd cadd`:
the formula goes on the stack before the context it is appended to. mmj2
expects every `|-` statement to parse as a `wff`, so use `metamath.exe` or
the chapter 03 checker.

**Question 6.** Prove the three Hilbert axioms, Peirce's law, and double
negation elimination.

```metamath
seqax1 $p |- => ( ph -> ( ps -> ph ) ) $= ? $.

seqax2 $p |- => ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $= ? $.

seqax3 $p |- => ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $= ? $.

seqpeirce $p |- => ( ( ( ph -> ps ) -> ph ) -> ph ) $= ? $.

seqnotnotr $p |- => ( -. -. ph -> ph ) $= ? $.
```

*Hint:* work from the goal backwards. Pick any compound formula and apply
its rule; the premises are smaller. Stop when a formula appears on both
sides. There is nothing to be clever about, which is the point: compare
`seqpeirce` with the effort `peirce` took in 4.1.5.

### 5.6.2 The trade

`ax-impr` moves an assumption from the left of `=>` into an antecedent. That
is the deduction theorem, and here it is a primitive rule. So what did it
cost?

**Question 7.** Try to prove modus ponens:

```metamath
${
  seqmp.1 $e |- => ph $.
  seqmp.2 $e |- => ( ph -> ps ) $.
  seqmp $p |- => ps $= ? $.
$}
```

Look at the conclusion of each rule. Which could end in `=> ps`? Write down
your argument that none can, and notice that it is a barrier argument: it
uses closure.

The cost was modus ponens. Each system makes one of the two primitive and
leaves the other as folk knowledge, or pays to have both:

| System | Where assumptions live | Discharging an assumption | Modus ponens |
| --- | --- | --- | --- |
| Hilbert (4.1) | `$e` hypotheses | folk recipe (5.5) | primitive: `ax-mp` |
| `set.mm` deduction style | an antecedent on every line | not needed | checked: `mpd` |
| `hol.mm` | a context term in every statement | checked | checked: `mpd`, from `ax-eqmp` |
| sequent calculus, as above | left of `=>` | primitive: `ax-impr` | folk recipe |
| sequent calculus with cut | left of `=>` | primitive: `ax-impr` | checked: Question 8 |

*Cut* is the rule that buys modus ponens back:

```metamath
${
  ax-cut.1 $e |- G => D ph $.
  ax-cut.2 $e |- H ph => E $.
  ax-cut $a |- G H => D E $.
$}
```

**Question 8.** With `ax-cut` added, prove `seqmp`. *Hint:* first prove
`|- ph ( ph -> ps ) => ps` with one `ax-impl` and two `ax-id`s. Cut it
against `seqmp.2`, then against `seqmp.1`.

**Question 9 (project).** Questions 6 and 8 are the ingredients of a recipe:
every theorem of chapter 04's system has a sequent proof using cut. Replace
each `ax-1`, `ax-2`, `ax-3` step by the matching `seqax` proof and each
`ax-mp` by `seqmp`. Write the translator and run it on `id` and `peirce`
from `myset.mm`.

### 5.6.3 Search, and where truth tables come from

Working backwards through any rule except cut removes one connective. So
backward search always halts, and it ends in one of two ways.

- Every branch closes with `ax-id`. The search has written a proof. Each
  success is **[checked]**. As a recipe: "every tautology has a cut-free
  proof" (completeness).
- Some branch reaches only variables, with none shared between the sides,
  such as `ph ps => ch`. No rule applies. Read it as a truth assignment: left
  side true, right side false. That assignment makes the original formula
  false.

So valuations are not an extra idea imported from outside; they are what
failed branches look like. And a falsifying assignment is a small, concrete
certificate. What it certifies is "not a tautology." Getting from there to
"not provable" is soundness, which is a barrier argument with P = "true under
every assignment". The certificate is parts 1 to 3 of 5.1.3. Part 4 is still
closure.

**Question 10 (project).** Write the backward search for this database,
printing proofs the checker accepts on success and an assignment on failure.
The SICP query language from chapter 02 is a natural fit.

**Question 11 (project, harder).** Compose the search with a translator from
cut-free sequent proofs back to Hilbert proofs, reading `ph ps => ch` as
`( ph -> ( ps -> ch ) )` (extra right-hand formulas become negated
antecedents) and proving one deduction-form lemma per sequent
rule. The result is a program that proves any propositional tautology in
`myset.mm`. That cashes the completeness theorem for chapter 04's system,
settles the third TODO in 4.1.6, and retires the remaining hand proofs of
4.1.4 and 4.1.5.

**Question 12.** Use the three-part certificate on a different barrier:
Peirce's law is not provable from `ax-1`, `ax-2`, and `ax-mp` alone.
**[folk]** Take three truth values 0 < ½ < 1, and let `a -> b` be 1 when
a ≤ b and b otherwise (give `-.` any table you like). Check by computation that `ax-1` and `ax-2` always
evaluate to 1, that `ax-mp` preserves "always 1", and that Peirce's law takes
the value ½ at `ph` = ½, `ps` = 0. Which of the four parts did you just do,
and which is missing?

### 5.6.4 Derivable versus admissible, again

**Question 13.** *Weakening* adds an unused assumption:

```metamath
${
  wk.1 $e |- G => D $.
  wk $p |- G ph => D $= ? $.
$}
```

Argue that this has no proof: which rule's conclusion could match? Then
describe the recipe that makes weakening admissible: given an actual proof of
a concrete sequent, add the extra formula to every line. The recipe needs the
proof *behind* the premise. A `$e` hypothesis hides it. That is the precise
difference between the two words.

**Cut elimination** (Gentzen's *Hauptsatz*): any proof using `ax-cut`, with
no extra `$e` hypotheses, can be converted to one without it. **[folk
recipe]** In other words, cut is admissible in the cut-free system, though
by Question 7 it is not derivable. Two things follow, both folk:

- *Subformula property.* A cut-free proof contains only pieces of its final
  sequent. This is why the search of 5.6.3 doesn't have to guess anything.
- *Consistency of chapter 04's system.* If it proved both `ph` and `-. ph`,
  then Question 9 and two cuts would give a proof of the empty sequent
  `|- =>`. Cut elimination would give a cut-free one. But no rule's
  conclusion is empty. This is a barrier assembled from two recipes and one
  inspection, and it never mentions truth tables.

**Preview.** With quantifiers, the ∀-right rule requires that `x` not occur
in the context, which in Metamath is a `$d` between `x` and each of
`G H D E`. Without it the rule proves `ph ⇒ ∀x ph`, the same mistake as the
`ax-gen` preview in 5.5.

## 5.7 Scoreboard

| Claim | Kind | Standing in these notes |
| --- | --- | --- |
| `id`, `peirce`, `seqid`, ... | theorem | checked |
| ⊢ (φ → ψ) gives a rule from φ to ψ | derivable rule | checked (`ax-mp`) |
| Deduction theorem | recipe | folk; cashable per use (Q4, Q5) |
| Hilbert proofs translate to sequent proofs with cut | recipe | folk; cashable (Q9) |
| Systems H, Meredith, Łukasiewicz prove the same theorems (4.3) | recipe, both ways | folk; ingredients checked in 4.3 |
| Weakening is admissible | recipe | folk; cashable |
| Cut elimination | recipe | folk; cashable with real work |
| Completeness (every tautology is provable) | recipe | folk; cashable (Q10, Q11) |
| Soundness (every theorem is a tautology) | barrier-maker | folk |
| `M U` is not a theorem | barrier | folk |
| Peirce needs `ax-3` | barrier | folk |
| `wk`, `seqmp`, `bad` are not derivable | barrier | folk |
| Chapter 04's system is consistent | barrier | folk |

## 5.8 Paying off barriers, later

To turn a barrier into a `$p`, proofs of the system under study have to be
objects in some other database, with the closure clause as a definition.
This needs quantifiers and at least a little set theory or arithmetic, so it
waits until after `set.mm` proper. Things to look at when the time comes:

- **`set.mm` already contains Metamath.** Carneiro's "Metamath formal
  systems" section formalizes Appendix C of the Metamath book. Its `mCls`
  (see [`df-mcls`](https://us.metamath.org/mpeuni/df-mcls.html)) is defined
  as an intersection of all sets closed under the axioms and substitution,
  which is exactly the closure clause; `mThm` (`df-mthm`) is the set of
  theorems. A barrier for MIU would be a `set.mm` theorem of the form "this
  string is not in `mThm` of that system."
- **`set.mm` also contains Gödel-style encodings** of first-order formulas as
  sets (`df-goal`, `df-fmla`, `df-sat`, `df-prv`), in the same author's
  section on model theory.
- **Solovay's [`peano.mm`](https://github.com/pbrosnan/ntg/blob/15332ee0dfe50ada14b6e31e947272232e4dc671/peano.mm)**
  separates its formal statements from its informal metamathematics in the
  header, and adds: "All our metamathematical arguments are quite
  constructive and certainly could be formalized in Primitive Recursive
  Arithmetic." That names a target far weaker than ZFC. Barriers like MU
  need only induction over finite strings.
- **Metamath Zero** is the same idea pushed to the verifier itself.
- **The Lean MIU development**, for a complete small example in another
  system.

Two things to expect, both folk for now.

*The regress stops at an inspection.* A `set.mm` theorem about MIU is a
theorem about a set-theoretic definition. That the definition matches
`miu.mm` is checked by reading both. This is the same kind of act as
trusting that the verifier implements substitution, and it is small.

*The tower has no top.* A barrier about system S is proved in a stronger
system T, and T's own consistency is a new barrier. Gödel's second
incompleteness theorem says that, for systems containing enough arithmetic,
T can't supply that one itself. The practical consequence is modest:
barriers about tiny systems such as MIU or propositional calculus need very
little, and that little is what Hilbert called finitary.

## 5.9 Parking lot

Material from earlier drafts, kept for later chapters.

- **Arithmetic.** The [Number Theory Game for Metamath](https://github.com/pbrosnan/ntg)
  uses Solovay's `peano.mm`; it needs quantifiers and `$d`. Targets, at a
  fixed revision:
  [`nn26l1`](https://github.com/pbrosnan/ntg/blob/15332ee0dfe50ada14b6e31e947272232e4dc671/peano.mm#L2884-L2891),
  [`pa_ax3cl2`](https://github.com/pbrosnan/ntg/blob/15332ee0dfe50ada14b6e31e947272232e4dc671/peano.mm#L2817-L2820),
  [`pa_ax3c`](https://github.com/pbrosnan/ntg/blob/15332ee0dfe50ada14b6e31e947272232e4dc671/peano.mm#L2812-L2835),
  [`addcom`](https://github.com/pbrosnan/ntg/blob/15332ee0dfe50ada14b6e31e947272232e4dc671/peano.mm#L2930-L2959).
  Its notation is prefix: `+ a b`, `S t`, `= s t`.
- **A geometry puzzle.** Rules: `Cg A B B A`, and from `Cg A B C D` and
  `Cg A B E F` infer `Cg C D E F`. Write the database and prove `Cg A B A B`.
  Patterned on [Tarski's axioms](https://us.metamath.org/mpeuni/df-trkg.html).
- **Threads.** Lambda calculus, recursive functions, Turing machines, and
  which equivalences between them are theorems. Curry–Howard, for one
  specific proof calculus and one specific typed language. How Automath,
  Mizar, LCF, and Boyer–Moore each represent a proof and what each trusts.
- **Reading.** Hofstadter's
  [MU puzzle chapter](https://www.ratiocination.org/Courses/phil3505/wp-content/uploads/2017/08/Hofstadter__Godel-Escher-Bach-excerpt-on-MU-puzzle.pdf);
  the Metamath book section 3.9 on the deduction theorem
  ([html](book/metamath.html#3.9.3-deduction-style));
  Carneiro, "Models for Metamath"; Pollack, "How to believe a machine-checked
  proof."
