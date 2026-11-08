---
title: "04 Studying Propositional Calculus with Metamath"
---

<h1 id="04-setmm" style="border-bottom: none;">04 Looking at set.mm</h1>

<nav class="nav">
    <span class="activenav"><a href="03-interpreter.html">← Previous</a></span>
    <span class="activenav"><a href="index.html">↑ Up</a></span>
    <span class="inactivenav" aria-disabled="true">Next →</span>
</nav>

[Read in html](book/metamath.html#abstract-mathematics-revealed) &nbsp;|&nbsp; [Read in pdf](book/metamath.pdf#page=77)

---

# 04 Studying Propositional Calculus with Metamath

Now that we're set on the intricacies of Metamath, sans 
disjoint variables and compressed proofs, I want to familiarize myself with logic with Metamath as grounding. 
This includes:

- The theorems and conventions in set.mm, up to predicate calculus.
- Other "propositional-like" proof databases.
- Proving substantive statements with a proof assistant (built-in proof assistant, or Yamma, or mmj2).

So, we'll work through basic formal systems.

## The MIU system.

(I thought we could do more here, but this is a pretty boring section after all, there's not that much interesting to do here with metamath yet).

The MIU system is described in chapter 1 of Hofstadter's Gödel, Escher, Bach (GEB). 

`miu.mm` has good exposition (Appendix D of the metamath book,
titled "The MIU system", is just a copy of this, so don't bother, just open `miu.mm`).

There's also [a quite cool Lean project](https://leanprover-community.github.io/mathlib4_docs/Archive/MiuLanguage/Basic.html) which states 
"The principal aim of this project is to give a Lean proof that the derivability of a string is a decidable predicate."

Here's a series of exposition with guided questions, with the intent that you shouldn't 
have to do any reading prereqs to be able to do them. I'll list my answers at the end.

### MIU System

The MIU setup can be described with the following proof database:

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

**Question 1.** Prove the theorem `ex-miu $p |- M U I I U $= ? $.`

As it turns out, the statement `|- M U` can never be proved in this
system. This is proved on p. 260 of GEB.

uhhhh from here we could describe algorithms to generate proofs of languages or whatever but there's not much to do from inside metamath with only these definitions. I'm not deleting this but I'll probably move it later. The following questions can only be solved for us at the level of English language arguments.

**Question 2.** Show that the statement `|- M U` is not derivable.

**Question 3.** Show that every string `M I^n` (eg. `M I`, `M I I`, `M I I I`) is derivable.

**Question 4.** Show that a finite string is derivable exactly when it has one `M` at the beginning and its number of `I`s is not divisible by $3.$

## B. A small working core of propositional calculus

We adapt notes from [the Metamath proof explorer, page 1 of 513](https://us.metamath.org/mpeuni/mmtheorems1.html), which is 
pretty good reading material. 

We'll start with the following database picking out some
stuff from `set.mm` for our purposes.

```metamath
$c wff |- -> -. ( ) $.
$v ph ps ch $.
wph $f wff ph $.
wps $f wff ps $.
wch $f wff ch $.
wn $a wff -. ph $.
wi $a wff ( ph -> ps ) $.
${
  min $e |- ph $.
  maj $e |- ( ph -> ps ) $.
  ax-mp $a |- ps $.
$}
ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
ax-2 $a |- ( ( ph -> ( ps -> ch ) ) ->
             ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.
ax-3 $a |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $.
```

The problems are freeform and build off of each other, so,
prove lemmas, use proof assistants, and apply results in
one problem to the next. We won't use `ax-3` or the not symbol `-.` 
for the first five questions.


```metamath
$( Prove that we can introduce an antecedent. $)
$( $)
${
  a1i.h $e |- ph $.
  a1i $p |- ( ps -> ph ) $= ? $.
$}

$( Prove Identity $)
idALT $p |- ( ph -> ph ) $= ? $.

$( Prove the deduction theorem $)

```


## 07 — Modus ponens under a common antecedent: mpd

**Mode:** Metamath proof construction. **Suggested effort:** 10–15 minutes. Source: [`mpd`](https://us.metamath.org/mpeuni/mpd.html).

### Question

In the shared Metamath propositional system, prove the following derived rule using `ax-2` and ordinary modus ponens:

```metamath
${
  mpd.h1 $e |- ( ph -> ps ) $.
  mpd.h2 $e |- ( ph -> ( ps -> ch ) ) $.
  ex-mpd $p |- ( ph -> ch ) $= ? $.
$}
```

There is no hypothesis `|- ph` available.

### Hint

The second essential hypothesis is the antecedent of `ax-2`. Detach it first. The resulting implication has the first essential hypothesis as its antecedent.

## 08 — Chain implications: syl

**Mode:** Metamath proof construction using derived rules. **Suggested effort:** 10–15 minutes. Source: [`syl`](https://us.metamath.org/mpeuni/syl.html).

### Question

In the shared Metamath propositional system, prove

```metamath
${
  syl.h1 $e |- ( ph -> ps ) $.
  syl.h2 $e |- ( ps -> ch ) $.
  ex-syl $p |- ( ph -> ch ) $= ? $.
$}
```

You may use these previously proved rules: `ex-a1i` takes `|- A` to `|- ( B -> A )`; `ex-mpd` takes `|- ( A -> B )` and `|- ( A -> ( B -> C ) )` to `|- ( A -> C )`.

### Hint

Use `ex-a1i` to turn the second hypothesis into `ph -> (ps -> ch)`. Now both hypotheses fit `ex-mpd`.

## 09 — Remove a repeated antecedent: pm2.43i

**Mode:** Metamath proof construction using derived rules. **Suggested effort:** 5–10 minutes. Source: [`pm2.43i`](https://us.metamath.org/mpeuni/pm2.43i.html).

### Question

In the shared Metamath propositional system, prove

```metamath
${
  contract.h $e |- ( ph -> ( ph -> ps ) ) $.
  ex-contract $p |- ( ph -> ps ) $= ? $.
$}
```

You may use `ex-id: |- ( A -> A )` and `ex-mpd`, which combines `A -> B` with `A -> (B -> C)` to give `A -> C`.

### Hint

Take `(A,B,C) = (ph,ph,ps)` in `ex-mpd`. Its other premise is now an instance of identity.

## 10 — Use the negation axiom: pm2.21i

**Mode:** Metamath proof construction. **Suggested effort:** 10–15 minutes. Source: [`pm2.21i`](https://us.metamath.org/mpeuni/pm2.21i.html).

### Question

In the shared Metamath propositional system, prove

```metamath
${
  explosion.h $e |- -. ph $.
  ex-explosion $p |- ( ph -> ps ) $= ? $.
$}
```

You may use `ex-a1i`, modus ponens, and the schema `ax-3: (¬A -> ¬B) -> (B -> A)`.

### Hint

From `¬ph`, use `ex-a1i` to obtain `¬ps -> ¬ph`. In `ax-3`, take `A=ps` and `B=ph`.













