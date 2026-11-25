---
title: "6. Proving theorems in set.mm"
---

<nav class="nav">
    <span class="activenav"><a href="05-predicate-calculus.html">← Previous</a></span>
    <span class="activenav"><a href="index.html">↑ Up</a></span>
    <span class="inactivenav" aria-disabled="true">Next →</span>
</nav>

<h1 id="06-setmm" style="border-bottom: none;">6. Proving theorems in set.mm</h1>

Links: [Chapter html, 3.4.3 Definitions for Set Theory](book/index.html#3.4.3-definitions-for-set-theory),
[3.5 Tricks of the Trade](book/index.html#3.5-tricks-of-the-trade),
[3.6 A Theorem Sampler](book/index.html#3.6-a-theorem-sampler).

@toc(hn)

## Introduction

> [!WARNING]
> This section is AI-generated and has not been reviewed.

Chapter 5 ended with `axextb`: two sets are equal exactly when they have the same members. This
chapter extends that idea from sets to **classes**, and classes are what make `set.mm` readable as
mathematics. `axextb` proves the membership criterion for equality of sets. `df-cleq` uses the same
criterion to *define* equality between class expressions. A class is
either a set variable or a *class abstraction* `{ x | ph }`, "the class of sets `x` such that
`ph`". Union, intersection, ordered pairs, relations, function values, and groups are all class
expressions built on top of abstractions. Once you can take one apart, you can read the rest of the
database.

The order follows section 3.4.3 of the Metamath book: class abstraction first, then the Boolean
operations, unions and intersections of families, then relations and functions. Along the way we pick up the conventions catalogued in
3.5 (implicit substitution hypotheses, `A e. _V` hypotheses, not-free hypotheses), and two
theorems from the 3.6 sampler, `ru` and `canth`.

Work in a copy of the [chapter 5 set.mm](code-05/set.mm), say `myset.mm`. For each exercise:

```text
MM> read myset.mm
MM> prove inss1
MM-PA> delete all
MM-PA> assign last ssriv
...
MM-PA> save new_proof /compressed
MM-PA> exit
MM> verify proof inss1
MM> write source myset.mm
```

`save new_proof` only stores the proof in memory. Until `write source`, your work is lost when you
quit. (`write source` keeps the previous file as a numbered backup unless you pass
`/no_versioning`.) If you change a *statement* rather than a proof, `verify proof *` re-checks
everything downstream of it. `verify markup *` checks the comments, for example a `~ label`
reference to a label that doesn't exist. That only matters once you write your own theorems. The
checks a contribution to upstream `set.mm` must pass are listed in its
[CONTRIBUTING.md](https://github.com/metamath/set.mm/blob/develop/CONTRIBUTING.md).

The proof assistant only lets you use statements that appear *earlier* in the file, so you can't
accidentally cite the theorem you're proving or anything built on it. `verify proof` is not
optional here: MM-PA does not check `$d` conditions, and in this chapter they start to matter
(see `elabg`). A few labels have proof modification discouraged. For those, `prove` refuses and
you need `prove LABEL /override`.

As in chapter 5, hints assume you work from the goal backwards. "Assign `syl`" means `assign last
syl` (or the equivalent in Yamma/mmj2), which splits the goal into the hypotheses of `syl`. With
classes it is often worth writing down an intermediate line first, because the unifier can't guess
which dummy set variable or which middle class you want. In MM-PA that's `let step` or
`let variable`. In Yamma or mmj2 you just type the line.

## 6.0 What a class is

> [!WARNING]
> This section is AI-generated and has not been reviewed.

There are three grammatical categories now: `setvar` (`x`, `y`, ...), `class` (`A`, `B`,
`{ x | ph }`, `( A i^i B )`, ...), and `wff`. The syntax axiom `cv` (`class x`) lets a set
variable appear anywhere a class can. The reverse is not allowed: you can't put a class
expression in a slot that wants a `setvar`. That single asymmetry is behind most of the
machinery in 6.4.

Three axiomatic statements give classes their meaning:

```metamath
df-clab $a |- ( x e. { y | ph } <-> [ x / y ] ph ) $.
df-cleq $a |- ( A = B <-> A. x ( x e. A <-> x e. B ) ) $.
df-clel $a |- ( A e. B <-> E. x ( x = A /\ x e. B ) ) $.
```

(`df-cleq` and `df-clel` carry justification hypotheses in the current database, and `$d`
conditions on the dummy variables. Look at them with `show statement df-cleq /full`.)

`df-clab` says what it means for a *set* to be a member of an abstraction. `df-cleq` says classes
are equal when they have the same members. `df-clel` reduces membership *of* a class to
membership of some set equal to it. Between them, every class expression can be eliminated in
favour of plain `e.` and quantifiers. The book calls this an *eliminable and conservative
extension*: classes add convenience but no new theorems about sets. Levy's appendix (pp. 357–366)
has the proof. Quine's *Set Theory and Its Logic* (pp. 15–21) calls them "virtual classes" and is
the readable version.

The gold mines here are the comments on these three definitions, and the page they all point to:

- [`df-clab`](https://us.metamath.org/mpeuni/df-clab.html): six numbered remarks. They cover why
  `df-clab` doesn't have the form of a definition, why `x` and `y` need not be distinct, how
  `vtoclg` moves a theorem from a set variable to a class, and whether these are definitions or
  axioms.
- [`df-cleq`](https://us.metamath.org/mpeuni/df-cleq.html) and
  [`df-clel`](https://us.metamath.org/mpeuni/df-clel.html): what their hypotheses are for, and
  why the definition checker can't verify them.
- [`eqabb`](https://us.metamath.org/mpeuni/eqabb.html): a short recipe for converting between
  theorems with wff variables and theorems with class variables. Its worked example is
  `sepgi` → `inex1`, which you will prove in 6.3.
- [The theory of classes](https://us.metamath.org/mpeuni/mmset.html#class) on the Metamath Proof
  Explorer home page.

**Proper substitution.** `df-clab` is stated with `[ x / y ] ph`, which chapter 5 didn't need.
Read it as "`ph` with `x` properly substituted for `y`". The notation is Curry's (1977). The
comment on [`df-sb`](https://us.metamath.org/mpeuni/df-sb.html) explains why `set.mm` defines it
with a single formula, not the usual recursive definition over free and bound occurrences. You won't
unfold `df-sb` in this chapter. You will use a handful of theorems about it: `sbid`
(`[ x / x ] ph <-> ph`), `elsb1`, `spsbbi`, and `sbievw` (substitution computed from an implicit
substitution hypothesis).

## 6.1 Class abstraction

> [!WARNING]
> This section is AI-generated and has not been reviewed.

Prove [`abid`](https://us.metamath.org/mpeuni/abid.html), [`abbi`](https://us.metamath.org/mpeuni/abbi.html),
and [`cvjust`](https://us.metamath.org/mpeuni/cvjust.html).

`abid` is the abstraction principle in its simplest form: `x` belongs to the class of `x` such
that `ph` exactly when `ph`. `abbi` says equivalent formulas give equal classes. It's the first time
you prove two classes equal, and the method (prove they agree at an arbitrary element) is the one
you'll use all chapter. `cvjust` motivates the syntax axiom `cv` by showing that a set variable
equals the class of its members, so writing `x` where a class is expected is harmless. It's a
motivation, not a justification. Its own comment points out that the proof already uses `cv`.

```metamath
abid $p |- ( x e. { x | ph } <-> ph ) $= ? $.

$( Equivalent formulas define equal classes. $)
abbi $p |- ( A. x ( ph <-> ps ) -> { x | ph } = { x | ps } ) $= ? $.

${
  $d x y $.
  $( A set variable is the class of its own members. $)
  cvjust $p |- x = { y | y e. x } $= ? $.
$}
```

#### Hints

- `abid`: `bitri` through `[ x / x ] ph`. One half is `df-clab` with both variables `x`. Search
  for the other half.
- `abbi`: assign `eqrdv`. It turns class equality under an antecedent into equal membership at a
  fresh `y`, keeping the antecedent. Use `let` to pick `y` if your tool doesn't ask. The goal is now
  `( A. x ( ph <-> ps ) -> ( y e. { x | ph } <-> y e. { x | ps } ) )`. Assign `3bitr4g`. Its two
  side premises are `df-clab`. The middle one says substitution respects equivalence:
  `( A. x ( ph <-> ps ) -> ( [ y / x ] ph <-> [ y / x ] ps ) )`, which is `spsbbi`. The inference
  form `abbii`, which you'll cite far more often, is `mpg` applied to `abbi`. That's the "closed
  theorem, then `mpg`" pattern from 5.1.1.
- `cvjust`: `df-cleq` is an axiom with hypotheses. The theorem `dfcleq` is the same statement
  without them, and that's the one to use. Assign `mpgbir` with `dfcleq` as its first premise.
  What's left is `( z e. x <-> z e. { y | y e. x } )` at a fresh `z`. `df-clab` turns the right side
  into `[ z / y ] y e. x`, and `elsb1` evaluates that substitution. Notice the orientation:
  `bitr2i`.

## 6.2 Union, intersection, and subclass

> [!WARNING]
> This section is AI-generated and has not been reviewed.

Prove [`elin`](https://us.metamath.org/mpeuni/elin.html), [`inss1`](https://us.metamath.org/mpeuni/inss1.html),
[`ssun1`](https://us.metamath.org/mpeuni/ssun1.html), [`inidm`](https://us.metamath.org/mpeuni/inidm.html),
and [`ssin`](https://us.metamath.org/mpeuni/ssin.html).

These are book 3.4.3's next definitions:

```metamath
df-ss $a |- ( A C_ B <-> A. x ( x e. A -> x e. B ) ) $.
df-un $a |- ( A u. B ) = { x | ( x e. A \/ x e. B ) } $.
df-in $a |- ( A i^i B ) = { x | ( x e. A /\ x e. B ) } $.
```

`elin` is worth doing carefully, because the pattern in it is how `set.mm` computes membership in
*any* abstraction when the candidate is a class `A` rather than a set variable. If `A` is a set,
`elab2g` calculates the membership. If `A` is a proper class, it belongs to nothing, so both sides
of the biconditional are false. `pm5.21nii` glues the two cases together. `elun`, `elrab`, `elpw`,
and dozens of other "membership in a constructor" theorems are proved the same way. Have a look at
the proof of `elrab` after you're done.

The rest are textbook facts once `elin` and `elun` are available. `ssriv` and `eqriv` turn inclusion
and equality goals into goals about an arbitrary element `x`. The hard one is `ssin`. One
direction is a payoff for `inss1`, and the whole thing can also be done as a chapter 5 quantifier
calculation. The library proves `inss1` in one step from a lemma `elinel1`. Do it from `elin`
instead.

```metamath
elin $p |- ( A e. ( B i^i C ) <-> ( A e. B /\ A e. C ) ) $= ? $.

inss1 $p |- ( A i^i B ) C_ A $= ? $.

ssun1 $p |- A C_ ( A u. B ) $= ? $.

inidm $p |- ( A i^i A ) = A $= ? $.

$( A class is included in an intersection iff it is included in both. $)
ssin $p |- ( ( A C_ B /\ A C_ C ) <-> A C_ ( B i^i C ) ) $= ? $.
```

#### Hints

- `elin`: assign `pm5.21nii`. Look at its three hypotheses before going further:
  `( ph -> ps )`, `( ch -> ps )`, and `( ps -> ( ph <-> ch ) )`. Here `ps` is `A e. _V`.
  - The first two say each side forces `A` to be a set. `elex` does the left side. For the right,
    `elex` on `A e. C` plus `adantl`.
  - The third is `elab2g`. Give it `df-in` as the hypothesis naming the class, and the implicit
    substitution `( x = A -> ( ( x e. B /\ x e. C ) <-> ( A e. B /\ A e. C ) ) )`, which is
    `anbi12d` of two `eleq1`s.
- `inss1`: assign `ssriv`, then `simplbi` with `elin`.
- `ssun1`: assign `ssriv`. Now you need `( x e. A -> x e. ( A u. B ) )`. `elun` says what the right
  side means. Assign `sylibr` and supply `elun` and a disjunction introduction (`orc`).
- `inidm`: assign `eqriv`, then `bitri` with `elin`. The other half is chapter 4's conjunction
  idempotence, `anidm`.
- `ssin`: assign `impbii` and take the directions separately.
  - Forward: take an element. `ssrdv` is the deduction form of `ssriv` and keeps the antecedent
    `( A C_ B /\ A C_ C )`. Each inclusion turns `x e. A` into a membership (`ssel`). Combine the
    two memberships with `jcad`, and recognize the result with `elin`. The label that rewrites the
    consequent of a nested implication is `imbitrrdi` (older material calls it `syl6ibr`).
  - Reverse: if `A` is inside `( B i^i C )`, and `( B i^i C )` is inside `B` by `inss1`, then `A`
    is inside `B` (`sstr`, via `mpan2`). Do the same with `inss2`, then `jca`.
- `ssin`, second route: unfold all three `C_` with `df-ss` (`3bitr4i`, with `anbi12i` on the left). You now need
  `( ( A. x ( x e. A -> x e. B ) /\ A. x ( x e. A -> x e. C ) ) <-> A. x ( x e. A -> x e. ( B i^i C ) ) )`.
  Work from the right-hand side: `elin` inside the implication (`imbi2i`, then `albii`), then
  `jcab` to split `( x e. A -> ( _ /\ _ ) )` into two implications (`albii` again), and finally
  5.1.2's `19.26`. `3bitrri` chains three equivalences in the direction you need.

## 6.3 Sets and proper classes

> [!WARNING]
> This section is AI-generated and has not been reviewed.

Prove [`eqabbw`](https://us.metamath.org/mpeuni/eqabbw.html), [`ru`](https://us.metamath.org/mpeuni/ru.html),
[`vneqv`](https://us.metamath.org/mpeuni/vneqv.html), and [`inex1`](https://us.metamath.org/mpeuni/inex1.html).

A class is a *set* if some set variable equals it. `set.mm` writes this `A e. _V`, and
[`isset`](https://us.metamath.org/mpeuni/isset.html) is the bridge:
`( A e. _V <-> E. x x = A )`. Book 3.5 lists `|- A e. _V` as a standard hypothesis ("`A` is a set").
You'll meet it again as `canth.1` and in the sethood hypotheses of `brco` and `brcnv`.

For `ru` and `inex1`, use `isset` to turn sethood into `E. z z = A`. Then `eqabbw` or `dfcleq`
turns `z = A` into a statement about the members of `z`. In `ru`, chapter 5’s `ru0` rules out
such a set. In `inex1`, separation supplies one. The comment on `eqabb` uses this second proof
(`sepgi` to `inex1`) as its example of turning a wff theorem into a class theorem.
For `vneqv`, use `exlimiiv`, the last exercise in 5.2.1, to show that no set equals the universe.

There is a shorter route when you already have a set containing all the elements of your class.
In 6.4, `ssrab2` gives `{ x e. A | ph } C_ A`. Once you know `A` is a set, `ssexg` gives
sethood of the restricted abstraction.

`ru` has proof modification discouraged, so start it with `prove ru /override`.

```metamath
${
  $d x y $.  $d y A $.  $d ph y $.  $d ps x $.
  eqabbw.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
  $( Equality of a class with an abstraction, at a fresh variable y. $)
  eqabbw $p |- ( A = { x | ph } <-> A. y ( y e. A <-> ps ) ) $= ? $.
$}

$( Russell's paradox with classes. $)
ru $p |- { x | x e/ x } e/ _V $= ? $.

vneqv $p |- -. x = _V $= ? $.

${
  inex1.1 $e |- A e. _V $.
  inex1 $p |- ( A i^i B ) e. _V $= ? $.
$}
```

#### Hints and answers

- `eqabbw`: `bitri` with `dfcleq` first. That leaves rewriting `y e. { x | ph }` to `ps` inside
  `A. y ( y e. A <-> _ )`. `albii` and `bibi2i` get you inside. `df-clab` and `sbievw` (fed the
  hypothesis) do the rewrite.
- `ru`: `e/` is defined by `df-nel`, and `nelir` strips it from the goal. Then:
  - `mtbir` with `isset` turns `-. { x | x e/ x } e. _V` into `-. E. z z = { x | x e/ x }`.
  - `nex` removes the existential.
  - `mtbir` with `eqabbw` turns `z = { x | x e/ x }` into the `A. y` statement of `ru0`.
  - `eqabbw` needs the implicit substitution `( x = y -> ( x e/ x <-> -. y e. y ) )`. Get
    `( x e/ x <-> y e/ y )` from `neleq12d` (both premises `id`), then `bitrdi` with `df-nel`.
- `vneqv`: assign `exlimiiv`. For its existential premise, search for "there is a set not in `x`"
  (`exnelv`). The implication premise is `( -. y e. x -> -. x = _V )`. Take the contrapositive
  (`con3i`) and prove `( x = _V -> y e. x )` from `vex` and `eleq2`.
- `inex1`: assign `issetri`, so the goal is `E. x x = ( A i^i B )`. Separation, in the form `sepgi`,
  gives `E. x A. y ( y e. x <-> ( y e. A /\ y e. B ) )`. `mpbir` connects them if you prove
  `( E. x x = ( A i^i B ) <-> E. x A. y ( y e. x <-> ( y e. A /\ y e. B ) ) )`: `exbii`, then
  `dfcleq`, then `elin` inside `A. y ( _ <-> _ )`.

```text
MM> show proof ru /lemmon /renumber
 1 ru0           $p |- -. A. y ( y e. z <-> -. y e. y )
 2 id            $p |- ( x = y -> x = y )
 3 id            $p |- ( x = y -> x = y )
 4 2,3 neleq12d  $p |- ( x = y -> ( x e/ x <-> y e/ y ) )
 5 df-nel        $a |- ( y e/ y <-> -. y e. y )
 6 4,5 bitrdi    $p |- ( x = y -> ( x e/ x <-> -. y e. y ) )
 7 6 eqabbw      $p |- ( z = { x | x e/ x } <-> A. y ( y e. z <-> -. y e. y ) )
 8 1,7 mtbir     $p |- -. z = { x | x e/ x }
 9 8 nex         $p |- -. E. z z = { x | x e/ x }
10 isset         $p |- ( { x | x e/ x } e. _V <-> E. z z = { x | x e/ x } )
11 9,10 mtbir    $p |- -. { x | x e/ x } e. _V
12 11 nelir      $p |- { x | x e/ x } e/ _V
```

Run `show trace_back ru /axioms` and compare with `ru0`. The class version still uses no set
theory axioms beyond extensionality. The classes are pure bookkeeping. `inex1` is different:
trace it and `ax-sep` shows up.

## 6.4 Restricted builders and moving from set variables to classes

> [!WARNING]
> This section is AI-generated and has not been reviewed.

Prove [`dfin5`](https://us.metamath.org/mpeuni/dfin5.html), [`rabexg`](https://us.metamath.org/mpeuni/rabexg.html),
[`vtoclga`](https://us.metamath.org/mpeuni/vtoclga.html), and [`elabg`](https://us.metamath.org/mpeuni/elabg.html).

The restricted abstraction `{ x e. A | ph }` is defined by `df-rab` as `{ x | ( x e. A /\ ph ) }`.
Its point is sethood. A restricted abstraction over a set is a set (separation again), and
`rabexg` is the form you'll cite most. The library proves it from `rabelpw` in two steps. Prove it
instead from the subclass fact `ssrab2` and `ssexg` ("a subclass of a set is a set").

The second half of this section is about a problem the grammar creates. A theorem proved about a
set variable `x` can't be used at a class `A` by substitution, because `A` doesn't fit in a
`setvar` slot. The fix is book 3.5's *implicit substitution* hypothesis
`( x = A -> ( ph <-> ps ) )`. It says `ps` is what `ph` becomes when `x` is replaced by `A`.
[`vtoclg`](https://us.metamath.org/mpeuni/vtoclg.html) then turns a proof of `ph` into a proof of
`( A e. V -> ps )`. The sethood antecedent is the price of moving from sets to classes.

`vtoclg` carries `$d ps x`: `x` must not *occur* in `ps`. That's a statement about symbols, not
about free variables. For `elabg` it's too strong, because the formula you want to substitute into
mentions `{ x | ph }`, where `x` occurs bound. The remedy is the third convention in book 3.5: a
*not-free* hypothesis. `vtoclgf` replaces the `$d` conditions with `F/_ x A` ("`x` is not free in
the class `A`") and `F/ x ps`. You prove those hypotheses by recursion on the syntax of the
expression with `nfcv`, `nfv`, `nfab1`, `nfel`, `nfbi`, and friends.

```metamath
${
  $d x A $.  $d x B $.
  dfin5 $p |- ( A i^i B ) = { x e. A | x e. B } $= ? $.
$}

${
  $d x A $.
  rabexg $p |- ( A e. V -> { x e. A | ph } e. _V ) $= ? $.
$}

${
  $d x A $.  $d x B $.  $d ps x $.
  vtoclga.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
  vtoclga.2 $e |- ( x e. B -> ph ) $.
  $( A theorem about x in B, used at the class A. $)
  vtoclga $p |- ( A e. B -> ps ) $= ? $.
$}

${
  $d ps x $.  $d x A $.
  elabg.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
  elabg $p |- ( A e. V -> ( A e. { x | ph } <-> ps ) ) $= ? $.
$}
```

#### Hints and answers

- `dfin5`: both sides unfold to the same unrestricted abstraction. Assign `eqtr4i` and give it
  `df-in` and `df-rab`.
- `rabexg`: assign `mpan`. Its first premise is `ssrab2`, its second `ssexg`.
- `vtoclga`: apply `vtoclg` to the *whole* implication `( x e. B -> ph )`, with `B` as the class
  `V`. The implicit substitution is `imbi12d` of `eleq1` and `vtoclga.1`. That gives
  `( A e. B -> ( A e. B -> ps ) )`, and chapter 4's `pm2.43i` finishes.
- `elabg`: you already have `abid`, the theorem at `x`. Try `vtoclg` first, the same way as in
  `vtoclga`: use `abid` as the theorem and `bibi12d` of `eleq1` and `elabg.1` as the substitution.
  MM-PA will accept it. `verify proof elabg` won't:

  ```text
  There is a disjoint variable ($d) violation at proof step 33.  Assertion "vtoclg" requires
  that variables "ps" and "x" be disjoint.  But "ps" was substituted with
  "( A e. { x | ph } <-> ps )" and "x" was substituted with "x".
  ```

  Delete the `vtoclg` step and assign `vtoclgf` in its place. The two old premises stay the same.
  The two new ones are `F/_ x A` (`nfcv`) and `F/ x ( A e. { x | ph } <-> ps )`. Build that one
  outside-in with `nfbi`, `nfel`, `nfcv`, `nfab1`, and `nfv`.

```text
MM> show proof elabg /lemmon /renumber
 1 nfcv          $p |- F/_ x A
 2 nfcv          $p |- F/_ x A
 3 nfab1         $p |- F/_ x { x | ph }
 4 2,3 nfel      $p |- F/ x A e. { x | ph }
 5 nfv           $p |- F/ x ps
 6 4,5 nfbi      $p |- F/ x ( A e. { x | ph } <-> ps )
 7 eleq1         $p |- ( x = A -> ( x e. { x | ph } <-> A e. { x | ph } ) )
 8 elabg.1       $e |- ( x = A -> ( ph <-> ps ) )
 9 7,8 bibi12d   $p |- ( x = A -> ( ( x e. { x | ph } <-> ph ) <-> ( A e. { x | ph } <-> ps ) ) )
10 abid          $p |- ( x e. { x | ph } <-> ph )
11 1,6,9,10 vtoclgf  $p |- ( A e. V -> ( A e. { x | ph } <-> ps ) )
```

(The library's own proof goes through `elabgt` instead. Either is fine.)

### 6.4.1 `if` and the weak deduction theorem

> [!WARNING]
> This section is AI-generated and has not been reviewed.

No exercises here, just the answer to a question from chapter 5: what is the strange
`if ( A e. RR , A , 1 )` that shows up in proofs like
[`renegcl`](https://us.metamath.org/mpeuni/renegcl.html)?

It's an ordinary class abstraction:

```metamath
df-if $a |- if ( ph , A , B ) = { x | ( ( x e. A /\ ph ) \/ ( x e. B /\ -. ph ) ) } $.
```

`iftrue` and `iffalse` evaluate it. Nothing about it is specific to deduction. It's `set.mm`'s
piecewise-definition operator, and definitions use it directly: `df-exp` (`if ( y = 0 , 1 , ...`),
`df-bc`, `df-xneg`, `df-rdg`. The weak deduction theorem is one consumer of it. To turn an
inference "from `A e. RR` infer `ps`" into a closed theorem, feed the inference the class
`if ( A e. RR , A , 1 )`. That class is real whatever `A` is, because `1re` covers the other
branch. Under the antecedent `A e. RR` it equals `A`. Few proofs in the main library cite
`dedth` or `elimhyp` directly. Most modern proofs carry the antecedent from the start
(deduction style, 4.1.1). The [weak deduction theorem page](https://us.metamath.org/mpeuni/mmdeduction.html)
and [book 3.9.2](book/index.html#3.9.2-weak-deduction-theorem) explain the trick. The proof of
`iftrue` is a nice small read: `dfif2` rewrites the definition so that a single tautology,
`dedlem0a`, does all the work.

## 6.5 Unions and intersections of families

> [!WARNING]
> This section is AI-generated and has not been reviewed.

Prove [`intss1`](https://us.metamath.org/mpeuni/intss1.html) and [`0iin`](https://us.metamath.org/mpeuni/0iin.html).

The book's list continues with the union and intersection of a class, and `set.mm` adds indexed
versions:

```metamath
df-uni $a |- U. A = { x | E. y ( x e. y /\ y e. A ) } $.
df-int $a |- |^| A = { x | A. y ( y e. A -> x e. y ) } $.
df-iun $a |- U_ x e. A B = { y | E. x e. A y e. B } $.
df-iin $a |- |^|_ x e. A B = { y | A. x e. A y e. B } $.
```

`U. A` and `|^| A` combine the members of a class `A`. The indexed forms combine a family: `B` is a
class expression that may mention the index `x`, and `x` ranges over `A`. All four are
abstractions, so membership in them is computed the way you computed `elin`. The results are
`eluni`, `elint`, `eliun`, and `eliin`, and the bound variable in the definition becomes a
quantifier in the membership condition.

Chapter 7 uses both intersections right away. Closure in a topology is defined as an intersection
of a class:

```metamath
df-cls $a |- cls = ( j e. Top |-> ( x e. ~P U. j |-> |^| { y e. ( Clsd ` j ) | x C_ y } ) ) $.
```

The closure of `x` is the intersection of all closed sets containing `x`. `intss1` is why that
intersection is the *smallest* closed superset: it is contained in every member of the family.
Finite intersections of open sets use the indexed form, and
[`iinopn`](https://us.metamath.org/mpeuni/iinopn.html) carries the hypothesis `A =/= (/)` on the
index. `0iin` shows why. With an empty index, the membership condition is vacuous, every set
satisfies it, and the intersection is the universal class `_V`. That can't be an open set, since
it isn't even a set (`vprc`). The same holds for `|^| (/) = _V` (`int0`). So topology theorems about
intersections either assume the family is nonempty, like `iinopn`, or make sure it is. In `df-cls`
the carrier `U. j` is itself closed and contains `x`, so the family is never empty.

```metamath
$( The intersection of a class is contained in each of its members. $)
intss1 $p |- ( A e. B -> |^| B C_ A ) $= ? $.

$( An intersection over an empty index is the universe. $)
0iin $p |- |^|_ x e. (/) A = _V $= ? $.
```

#### Hints

- `intss1`: assign `ssrdv`, keeping `A e. B` as the antecedent, with a fresh element `x`. The goal
  is now `( A e. B -> ( x e. |^| B -> x e. A ) )`. `elint` (with `vex`) says `x e. |^| B` means
  `A. y ( y e. B -> x e. y )`. Instantiate `y` at the class `A`. `spcgv` is the version of `vtoclg`
  for specializing a universal: from the implicit substitution
  `( y = A -> ( ( y e. B -> x e. y ) <-> ( A e. B -> x e. A ) ) )` (`imbi12d` of `eleq1` and
  `eleq2`) it gives `( A e. B -> ( A. y ( y e. B -> x e. y ) -> ( A e. B -> x e. A ) ) )`.
  `pm2.43a` removes the repeated `A e. B`, and `biimtrid` swaps `elint` into the antecedent.
- `0iin`: assign `eqtr4i` and unfold the left side with `df-iin`. The other premise is
  `_V = { y | A. x e. (/) y e. A }`. `eqabi` reduces it to `( y e. _V <-> A. x e. (/) y e. A )`.
  Both sides are theorems, `vex` and `ral0`. Two theorems are equivalent by `2th`.

## 6.6 Ordered pairs and relations

> [!WARNING]
> This section is AI-generated and has not been reviewed.

Prove [`imass2`](https://us.metamath.org/mpeuni/imass2.html) and [`cnvco`](https://us.metamath.org/mpeuni/cnvco.html).

A relation is a class of ordered pairs, and `A R B` abbreviates `<. A , B >. e. R` (`df-br`).
Relations are mostly built with the ordered-pair abstraction `{ <. x , y >. | ph }`. Converse,
composition, cross product, and maps-to are all of this form:

```metamath
df-cnv $a |- `' A = { <. x , y >. | y A x } $.
df-co $a |- ( A o. B ) = { <. x , y >. | E. z ( x B z /\ z A y ) } $.
df-res $a |- ( A |` B ) = ( A i^i ( B X. _V ) ) $.
df-ima $a |- ( A " B ) = ran ( A |` B ) $.
```

Read the comment on [`df-op`](https://us.metamath.org/mpeuni/df-op.html). It's a short history of
ordered pairs: Wiener's 1914 definition, Kuratowski's 1921 simplification, Hausdorff's, one that
needs Regularity, and one that works for proper classes, each with the theorem in `set.mm` that
justifies it. It also explains why `set.mm`'s `<. A , B >.` is empty when `A` or `B` is a proper
class. That choice saves sethood hypotheses all over the library. In practice you never unfold
`df-op`. You use `opth` (pairs are equal iff their components are, given that the first pair's
components are sets) and `brco`/`brcnv`-style lemmas.

`cnvco` is the undergraduate fact (g∘f)⁻¹ = f⁻¹∘g⁻¹. The proof is the usual one: compare the two
relations pair by pair. Here "pair by pair" is `opabbii`, the ordered-pair version of `abbii`.
`brco` and `brcnv` need their arguments to be sets (book 3.5's `A e. _V` hypotheses). Since `x`,
`y`, and `z` are set variables, `vex` discharges every one.

```metamath
$( Image is monotone in its second argument. $)
imass2 $p |- ( A C_ B -> ( C " A ) C_ ( C " B ) ) $= ? $.

$( Converse of a composition. $)
cnvco $p |- `' ( A o. B ) = ( `' B o. `' A ) $= ? $.
```

#### Hints

- `imass2`: the image is the range of a restriction. Unfold both images with `df-ima` using
  `3sstr4g`, the inclusion version of `3bitr4g`. What's left is
  `` ( A C_ B -> ran ( C |` A ) C_ ran ( C |` B ) ) ``. That's `syl` of two monotonicity lemmas, one
  for restriction (`ssres2`) and one for range (`rnss`).
- `cnvco`: unfold both sides to `{ <. y , x >. | ... }` with `3eqtr4i`, `df-cnv`, and `df-co`,
  then `opabbii`. You need
  `` ( x ( A o. B ) y <-> E. z ( y `' A z /\ z `' B x ) ) ``.
  - `brco` turns the left side into `E. z ( x B z /\ z A y )`.
  - `brcnv` (twice, under `anbi12i` and `exbii`) turns the right side into
    `E. z ( z A y /\ x B z )`.
  - The two differ by the order of the conjuncts, which is `exancom`. `3bitr4i` ties the three
    together.

## 6.7 Functions

> [!WARNING]
> This section is AI-generated and has not been reviewed.

Prove [`fvconst`](https://us.metamath.org/mpeuni/fvconst.html), [`uzval`](https://us.metamath.org/mpeuni/uzval.html),
and [`canth`](https://us.metamath.org/mpeuni/canth.html).

`F : A --> B` is a statement (`F` is a function from `A` into `B`), built from `Fun`, `Fn`, `dom`,
and `ran` (`df-fun`, `df-fn`, `df-f`). ``( F ` A )`` is a class expression: the value of `F` at `A`.
It is defined for *every* `F` and `A`. The comment on
[`df-fv`](https://us.metamath.org/mpeuni/df-fv.html) explains that it evaluates to `(/)` when it
isn't meaningful, that the apostrophe notation goes back to Peano and *Principia*, and that the
current definition goes through the definite-description operator `iota`. Most functions are
written in maps-to notation, `( x e. A |-> B )`, which `df-mpt` defines as an ordered-pair
abstraction. [`fvmpt`](https://us.metamath.org/mpeuni/fvmpt.html) evaluates such a function. Its
three hypotheses are the same three ingredients as `elab2`: an implicit substitution, an equation
naming the definition being evaluated, and sethood. You used the first two already with `elab2g`
in `elin`.

`canth` is Cantor's theorem from book 3.6: no function from `A` onto its power set. The proof is
`ru` again, with `F` doing the indexing. The diagonal class
`` { x e. A | -. x e. ( F ` x ) } `` is a subset of `A`, so it should be some ``( F ` y )``. If it were,
`y` would belong to it exactly when it didn't. This is the hard problem of the chapter. The hint
breaks it into the two facts the proof needs.

```metamath
fvconst $p |- ( ( F : A --> { B } /\ C e. A ) -> ( F ` C ) = B ) $= ? $.

${
  $d k N $.
  $( The upper integers starting at N, evaluated from the definition df-uz. $)
  uzval $p |- ( N e. ZZ -> ( ZZ>= ` N ) = { k e. ZZ | N <_ k } ) $= ? $.
$}

${
  canth.1 $e |- A e. _V $.
  $( Cantor's theorem. $)
  canth $p |- -. F : A -onto-> ~P A $= ? $.
$}
```

#### Hints

- `fvconst`: the value lies in the codomain `{ B }` (`ffvelcdm`), and a member of a singleton is
  its element (`elsni`). `syl`.
- `uzval`: assign `fvmpt`. Fill the definition premise with `df-uz` first. That fixes the bound
  variable `j` and the body `{ k e. ZZ | j <_ k }`. The substitution premise is
  `( j = N -> { k e. ZZ | j <_ k } = { k e. ZZ | N <_ k } )`: `rabbidv` to get inside the
  restricted abstraction, then `breq1`. Sethood is `rabex` with `zex`.
- `canth`: write `D` for the diagonal class `` { x e. A | -. x e. ( F ` x ) } ``. Assign
  `pm2.65i`, so that from `F : A -onto-> ~P A` you derive both `D e. ran F` and `-. D e. ran F`.
  The first holds because `D` is a subset of `A` and `F` is onto. For the second, the line to aim
  for is `` ( y e. A -> -. ( F ` y ) = D ) ``. If `` ( F ` y ) = D `` held for some `y e. A`, then
  `y e. D` would be equivalent to its own negation, the same contradiction as in `ru0`.

### 6.7.1 Optional reading: a word as a function

> [!WARNING]
> This section is AI-generated and has not been reviewed.

In `df-word`, a word over an alphabet `S` is a function from `( 0 ..^ l )` into `S` for some
`l e. NN0`. A three-letter word has indices 0, 1, and 2. The definition says such an endpoint
exists. The theorem `wrdf` gives you the endpoint for a particular word `W`: its length
``( # ` W )``. Starting from `W e. Word S`, you now have the domain and codomain needed to
reason about the letter at a given index. [Definition of a word](https://us.metamath.org/mpeuni/df-word.html) · [A word as a function on its index set](https://us.metamath.org/mpeuni/wrdf.html)

## 6.8 Structures: groups

> [!WARNING]
> This section is AI-generated and has not been reviewed.

Prove [`grpcl`](https://us.metamath.org/mpeuni/grpcl.html) and [`grpinvinv`](https://us.metamath.org/mpeuni/grpinvinv.html).

A group in `set.mm` is not a pair (carrier, operation). It's an *extensible structure*, a function
from slot indices to components, read with selectors: ``( Base ` G )`` is the carrier,
``( +g ` G )`` the operation, ``( 0g ` G )`` the identity, ``( invg ` G )`` the inverse. Theorems
name these with hypotheses like `` grpcl.b $e |- B = ( Base ` G ) $. `` so that the statement can talk
about `B` and `.+` like a textbook does. A ring is a group with more slots, which is why group
theorems apply to rings without restatement. The
[introductory essay on extensible structures](https://us.metamath.org/mpeuni/mmtheorems174.html#mm17371s)
explains the design.

`grpcl` is a warm-up in reading those hypotheses. `grpinvinv`, (x⁻¹)⁻¹ = x, is the textbook
cancellation argument: x⁻¹ · (x⁻¹)⁻¹ = 0 = x⁻¹ · x, then cancel x⁻¹ on the left with `grplcan`. The
mathematics takes one line. Most of the formal proof is closure facts under the antecedent
`( G e. Grp /\ X e. B )`, and that ratio is typical of algebra in `set.mm`.

```metamath
${
  grpcl.b $e |- B = ( Base ` G ) $.
  grpcl.p $e |- .+ = ( +g ` G ) $.
  grpcl $p |- ( ( G e. Grp /\ X e. B /\ Y e. B ) -> ( X .+ Y ) e. B ) $= ? $.
$}

${
  grpinvinv.b $e |- B = ( Base ` G ) $.
  grpinvinv.n $e |- N = ( invg ` G ) $.
  $( Double inverse law for groups. $)
  grpinvinv $p |- ( ( G e. Grp /\ X e. B ) -> ( N ` ( N ` X ) ) = X ) $= ? $.
$}
```

#### Hints

- `grpcl`: a group is a monoid (`grpmnd`), and monoids are closed (`mndcl`, given the same two
  naming hypotheses). `syl3an1` replaces the first conjunct.
- `grpinvinv`: make both products equal the identity, then cancel. Both
  `` ( ( N ` X ) ( +g ` G ) ( N ` ( N ` X ) ) ) `` and `` ( ( N ` X ) ( +g ` G ) X ) `` are
  `` ( 0g ` G ) `` (`grprinv`, `grplinv`), and `grplcan` cancels ``( N ` X )`` on the left. Most of
  the work is closure facts (`grpinvcl`) under the antecedent `( G e. Grp /\ X e. B )`.
