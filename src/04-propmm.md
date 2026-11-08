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

> [!WARN]
> These notes have a lot of AI-suggested problems in them that have not yet
> been reviewed

@toc

# 4 Studying Propositional Calculus with Metamath

Now that we're set on the intricacies of Metamath, sans 
disjoint variables and compressed proofs, I want to familiarize myself with logic with Metamath as grounding. 
This includes:

- The theorems and conventions in set.mm, up to predicate calculus.
- Other "propositional-like" proof databases.
- Proving substantive statements with a proof assistant (built-in proof assistant, or Yamma, or mmj2).

So, we'll work through basic formal systems, as far as we can get until
our patience runs out, or we can no longer avoid disjoint variables.

## 04.1 Propositional calculus in `set.mm`

Let's start by building up some of the basic theorems and machinery of `set.mm`. We'll
pick apart and cannibalize the usual set proof database, but you still might find it useful
to visit [the Metamath Proof Explorer, page 1 of 513](https://us.metamath.org/mpeuni/mmtheorems1.html),
which is good reading. 

This section is formulated as a series of interdependent exercises which you can use to build up some 
pieces of set.mm, preferably in the start of a new file like `myset.mm`. There are hints and solutions,
and you can also find the theorem in `set.mm` or view it by editing the url
`https://us.metamath.org/mpeuni/<label>.html`. There's usually cool stuff to see in the metamath set 
explorer.

The foundation we'll use is:

```metamath
$c wff |- -> -. ( ) $.
$v ph ps ch th ta $.
wph $f wff ph $.
wps $f wff ps $.
wch $f wff ch $.
wth $f wff th $.
wta $f wff ta $.
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

Also note, metamath proof assistant commands:

- `assign n label`, `delete all`, `prove label`, `save new_proof`, `show new_proof/all/lemmon`, `improve all` should be familiar.
- `save new_proof` and `write source` to save and modify your target file (eg. myset.mm)
- `match term [proof step]` is super useful to list available unifications.

### 4.1.1 Implication: first proofs and useful derived rules

To start, here's some basic theorems: `a1i`, `a2i`, `mpd`, `syl`, and `id`.
(TODO: replace those labels with links to the proof explorer)

Note that here we start seeing some of the conventions of set.mm, where the suffix
i generally stands for inference form, suffix d stands for deduction form, and no
suffix generally stands for closed form. This is discussed various places in the proof explorer
[such as here](https://us.metamath.org/mpeuni/mmnatded.html) and in the book [html page](https://www.mathandcode.com/books/metamath/book/metamath.html#3.9.3-deduction-style) or [pdf page](TODO). The proof explorer
pages of these are really good, tons of info.

NB: For sections 4.1.1 to 4.1.3, you only need axioms `ax-1`, `ax-2`, and `ax-mp`, 
making these theorems intuitionistic. 

```metamath
$( Add an antecedent $)
${
  a1i.1 $e |- ph $.
  a1i $p |- ( ps -> ph ) $= ? $.
$}

$( Distribute an antecedent $)
${
  a2i.1 $e |- ( ph -> ( ps -> ch ) ) $.
  a2i $p |- ( ( ph -> ps ) -> ( ph -> ch ) ) $= ? $.
$}

$( Modus ponens under shared antecedent. AKA modus ponens in deductive form.
   You'll use it constantly! 
   Try proving this using a2i $)
${
  mpd.1 $e |- ( ph -> ps ) $.
  mpd.2 $e |- ( ph -> ( ps -> ch ) ) $.
  mpd $p |- ( ph -> ch ) $= ? $.
$}

$( syllogism, or "hypothetical syllogism" $)
${
  syl.1 $e |- ( ph -> ps ) $.
  syl.2 $e |- ( ps -> ch ) $.
  syl $p |- ( ph -> ch ) $= ? $.
$}

$( A standard "first proof" in Hilbert-style textbooks. It's lemma 1.8
   of Mendelson and "our first proof" in Hirst & Hirst.  $)
id $p |- ( ph -> ph ) $= ? $.
```

#### Hints and My Answers

Hints[^1].

[^1]: Unless otherwise stated, hints are given from the perspective of working 
back from the statement to be proved, so
"use `ax-mp`" means "assign `ax-mp` to the statement."

- `a1i` follows from modus ponens and an axiom.
- `a2i` follows from modus ponens and an axiom. 
- `mpd` can be proved using `a2i` in its proof.
- A short proof of `syl` doesn't use any axioms explicitly, only the theorems we proved.
- One theorem, then two axioms. 

I solved this without using the hints, and got the following rather long 
proofs. 

```mm
${  a1i.1 $e |- ph $.
  a1i $p |- ( ps -> ph ) $=
    wph wps wph wi a1i.1 wph wps ax-1 ax-mp $. $}
${ a2i.1 $e |- ( ph -> ( ps -> ch ) ) $.
   a2i $p |- ( ( ph -> ps ) -> ( ph -> ch ) ) $=
    wph wps wch wi wi wph wps wi wph wch wi wi a2i.1 wph wps wch ax-2 ax-mp $. $}
${ mpd.1 $e |- ( ph -> ps ) $.
   mpd.2 $e |- ( ph -> ( ps -> ch ) ) $.
   mpd $p |- ( ph -> ch ) $=
    wph wps wi wph wch wi mpd.1 wph wps wch wi wi wph wps wi wph wch wi wi
    mpd.2 wph wps wch ax-2 ax-mp ax-mp $. $}
${ syl.1 $e |- ( ph -> ps ) $.
   syl.2 $e |- ( ps -> ch ) $.
   syl $p |- ( ph -> ch ) $=
    wph wps wi wph wch wi syl.1 wph wps wch wi wi wph wps wi wph wch wi wi wps
    wch wi wph wps wch wi wi syl.2 wps wch wi wph ax-1 ax-mp wph wps wch ax-2
    ax-mp ax-mp $. $}
idALT $p |- ( ph -> ph ) $=
  wph wph wph wi wph wph wph ax-1 wph wph wph wi ax-1 mpd $.
```

After the hints, we can simplify the proofs of `mpd` and `syl` to be much shorter:

```mm
mpd $p |- ( ph -> ch ) $=
  wph wps wi wph wch wi mpd.1 wph wps wch mpd.2 a2i ax-mp $.
syl $p |- ( ph -> ch ) $=
  wph wps wch syl.1 wps wch wi wph syl.2 a1i mpd $.
```

### 4.1.2 More Advanced Implications

Prove  (TODO, hyperlinked to proof explorer).

Starting to get a little more difficult. 


```metamath
$( Remove repeated antecedent. AKA contraction.
   This is theorem 2.43 of Principia Mathematica. $)
${
  pm2.43i.1 $e |- ( ph -> ( ph -> ps ) ) $.
  pm2.43i $p |- ( ph -> ps ) $= ? $.
$}

$( The deduction form of a1i. A deduction form puts the same 
   antecedent `ph ->` in front of every hypothesis and conclusion. $)
${
  a1d.1 $e |- ( ph -> ps ) $.
  a1d $p |- ( ph -> ( ch -> ps ) ) $= ? $.
$}

$( The deduction form of a2i. $)
${
  a2d.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
  a2d $p |- ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) ) $= ? $.
$}

$( Syllogism inference with commutation of antecedents. $)
${
  sylcom.1 $e |- ( ph -> ( ps -> ch ) ) $.
  sylcom.2 $e |- ( ps -> ( ch -> th ) ) $.
  sylcom $p |- ( ph -> ( ps -> th ) ) $= ? $.
$}

$(  Inference that commutes antecedents in an implication. $)
${
  com12.1 $e |- ( ph -> ( ps -> ch ) ) $.
  com12 $p |- ( ps -> ( ph -> ch ) ) $= ? $.
$}

$( "Closed form" of modus ponens $)
pm2.27 $p |- ( ph -> ( ( ph -> ps ) -> ps ) ) $= ? $.

$( implication of implications $)
${
  imim2i.1 $e |- ( ph -> ps ) $.
  imim2i $p |- ( ( ch -> ph ) -> ( ch -> ps ) ) $= ? $.
$}
```


#### Out of place scratchwork

The differences between the inference form and the deduction form seems
like there's a metatheorem here. Two ways of phrasing this:

Number one, a statement something like "If we have a proof of propositional
logic statements of the form `${ foo.1 $e |- ch $. foo $p |- ps $= ? $. $}`
then we also have a proof of the form `$p |- ch -> ps $.` This is like we have
assumed chi, proved psi, then discharged the assumption of chi. Because it's a 
statement about the existence of a proof, it's a metatheorem. 

However, there's another way to think about this, that was is that I suppose
I have a theory, where I perform deductions, getting psi from chi. Now, 
I want to reason about those deductions, so I invent the double arrow symbol to mean
"deduces". Now I start reasoning with statements in the form `$p |- ch => ps $.`,
but someone comes along and tells me, "oh yeah, that's actually not enough to
make a statement about deduction, you need a metatheorem." But I literally
invented the arrow for that purpose! WTF? Is there some philosophical leap to 
make here, or are we confronted yet again with the notion of, "what if my 
`=>` properties and axioms that I define, don't fully encompass the consequences
of my original form of deduction [reaching statements by Metamath replacement rules]?" just like we were confronted at the beginning of our metamath journey,
"what if the proof checking system that I'm programming has bugs or inadequacies 
in it, and doesn't capture the colloquial idea of proof?"

#### Hints and My Answers

(TODO, rewrite these hints in the style of 4.1.1 and with respect paid to footnote 1.)

- *Hint:* for `pm2.43i`, apply `mpd` with an instance of `id` as the other premise.
- *Hint:* for `a1d` and `a2d`, each is `syl` with an axiom instance.
- *Hint:* for `sylcom`, apply `a2i` to `sylcom.2`, then use `syl`.
- *Hint:* for `com12` `a2i` gives `( ( ph -> ps ) -> ( ph -> ch ) )`, and `ax-1` gives `( ps -> ( ph -> ps ) )`. Chain them with `syl`.
- *Hint:* for `pm2.27` apply `com12` to an instance of `id`.
- *Hint:* for `imim2i`, use `a1i`, then `a2i`.

I didn't spend a bunch of time on finding the simplest proofs.

```mm
pm2.43i $p |- ( ph -> ps ) $=
    wph wph wps wph idALT pm2.43i.1 mpd $.
a1d $p |- ( ph -> ( ch -> ps ) ) $=
    wph wps wch wps wi a1d.1 wps wch wps wi wi wph wps wch ax-1 a1i mpd $.
a2d $p |- ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) ) $=
  wph wps wch wth wi wi wps wch wi wps wth wi wi a2d.1 wps wch wth ax-2 syl
  $.
sylcom $p |- ( ph -> ( ps -> th ) ) $=
  wph wps wch wi wps wth wi sylcom.1 wph wps wch wth wps wch wth wi wi wph
  sylcom.2 a1i a2d mpd $.
com12 $p |- ( ps -> ( ph -> ch ) ) $=
  wps wph wps wch wps wph ax-1 com12.1 sylcom $.
pm2.27 $p |- ( ph -> ( ( ph -> ps ) -> ps ) ) $=
  wph wps wi wph wps wph wps wps wps wps wi wph wps idALT a1i a2i com12 $.
imim2i $p |- ( ( ch -> ph ) -> ( ch -> ps ) ) $=
  wch wph wps wph wps wi wch imim2i.1 a1i a2i $.
```

### 4.1.3 More propositional calculus

Write proofs introducing more propositional calculus tools, (TODO insert links to mpdd and so on) 

I had a tough time on this section, but note that the Metamath proof explorer (TODO link to mmnatded again)
asserts that "once you have an assertion in deduction form, you can easily convert it to inference form or closed form", with instructions how! You still only need `ax-1`, `ax-2`, and `ax-mp` btw.

```metamath
$( Deduction form of mpd $)
${
  mpdd.1 $e |- ( ph -> ( ps -> ch ) ) $.
  mpdd.2 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
  mpdd $p |- ( ph -> ( ps -> th ) ) $= ? $.
$}

$( Deduction form of syl $)
${
  syld.1 $e |- ( ph -> ( ps -> ch ) ) $.
  syld.2 $e |- ( ph -> ( ch -> th ) ) $.
  syld $p |- ( ph -> ( ps -> th ) ) $= ? $.
$}


$( Note: This can be viewed as a syllogism but with the hypothesis syl.2
   "discharged" and turned into an antecedent. $)
${
  imim1i.1 $e |- ( ph -> ps ) $.
  imim1i $p |- ( ( ps -> ch ) -> ( ph -> ch ) ) $= ? $.
$}

$( The following closed forms of theorems we've already proved do the same
   trick. We discharge a hypothesis. $)
imim2 $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $= ? $.

imim1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $= ? $.

pm2.43 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $= ? $.

pm2.04 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $= ? $.
```

#### Hints and My Answers

(TODO: these hints are awful and incomplete lol. They literally only either handed me the complete answer on
a silver platter, or left me saying "WTF is this trying to say?" Need a total redo. )

- *Hint:* For `imim2`, `syl` of the `ax-1` instance `( ( ph -> ps ) -> ( ch -> ( ph -> ps ) ) )`
  and an `ax-2` instance.
- *Hint:* For `imim1`, `com12` applied to an instance of `imim2`.
- *Hint:* For `pm2.43`, `a2i` applied to `pm2.27`.
- *Hint:* `pm2.04` is the closed form of `com12`. `ax-2` takes `( ph -> ( ps -> ch ) )` to
  `( ( ph -> ps ) -> ( ph -> ch ) )`. To trade `( ph -> ps )` for `ps`, apply `imim1i`
  to the `ax-1` instance `( ps -> ( ph -> ps ) )`. Then use `syl`.

My answers. I didn't get `pm2.04` without help, hah!

```mm
mpdd $p |- ( ph -> ( ps -> th ) ) $=
  wph wps wch wi wps wth wi mpdd.1 wph wps wch wth mpdd.2 a2d mpd $.
syld $p |- ( ph -> ( ps -> th ) ) $=
  wps wph wth wps wph wch wth wph wps wch syld.1 com12 syld.2 sylcom com12 $.
imim1i $p |- ( ( ps -> ch ) -> ( ph -> ch ) ) $=
  wps wch wi wph wps wch wph wps wi wps wch wi imim1i.1 a1i wps wch wi id
  syld $.
imim2 $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $=
  wph wps wi wch wph wps wi wi wch wph wi wch wps wi wi wph wps wi wch ax-1 wch
  wph wps ax-2 syl $.
imim1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
  wps wch wi wph wps wi wph wch wi wps wch wph imim2 com12 $.
pm2.43 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $=
  wph wph wps wi wps wph wps pm2.27 a2i $.
pm2.04 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
  wph wps wch wi wi wph wps wi wph wch wi wi wps wph wch wi wi wph wps wch ax-2
  wps wph wps wi wph wch wi wps wph ax-1 imim1i syl $.
```

### 4.1.4 Negation and classical propositional calculus

**Question 16.** Prove the inference and deduction forms of `ax-3`, `con4i` and `con4d`.
("con" is for contraposition.)

```metamath
${
  con4i.1 $e |- ( -. ph -> -. ps ) $.
  con4i $p |- ( ps -> ph ) $= ? $.
$}

${
  con4d.1 $e |- ( ph -> ( -. ps -> -. ch ) ) $.
  con4d $p |- ( ph -> ( ch -> ps ) ) $= ? $.
$}
```

*Hint:* `ax-3` with `ax-mp`, and with `syl`.

**Question 17.** Prove that a contradiction implies anything (*explosion*, or *ex
falso quodlibet*).

```metamath
${
  pm2.21i.1 $e |- -. ph $.
  pm2.21i $p |- ( ph -> ps ) $= ? $.
$}

${
  pm2.24ii.1 $e |- ph $.
  pm2.24ii.2 $e |- -. ph $.
  pm2.24ii $p |- ps $= ? $.
$}
```

*Hint:* for `pm2.21i`, `a1i` gives `( -. ps -> -. ph )`, then use `con4i`.

**Question 18.** Prove the deduction form and closed forms of explosion.

```metamath
${
  pm2.21d.1 $e |- ( ph -> -. ps ) $.
  pm2.21d $p |- ( ph -> ( ps -> ch ) ) $= ? $.
$}

pm2.21 $p |- ( -. ph -> ( ph -> ps ) ) $= ? $.

pm2.24 $p |- ( ph -> ( -. ph -> ps ) ) $= ? $.
```

*Hint:* `pm2.21d` is `a1d` followed by `con4d`. `pm2.21` is `pm2.21d` applied to an
instance of `id`. `pm2.24` is `com12` of `pm2.21`.

**Question 19.** Prove the *Clavius law*: if a formula follows from its own negation,
it's true. This is the first question where you need a plan.

```metamath
pm2.18 $p |- ( ( -. ph -> ph ) -> ph ) $= ? $.
```

*Hint:* write H for `( -. ph -> ph )`. Work with H as a shared antecedent, and aim for
`( H -> ( -. ph -> -. H ) )`; then `con4d` gives `( H -> ( H -> ph ) )`.

*Second hint:* `id` gives `( H -> ( -. ph -> ph ) )`, and `pm2.21` gives
`( -. ph -> ( ph -> -. H ) )`. Combine them with `sylcom`, then use `con4d`, and
finish with `pm2.43i`.

**Question 20.** Prove double negation elimination and introduction.

```metamath
notnotr $p |- ( -. -. ph -> ph ) $= ? $.

notnot $p |- ( ph -> -. -. ph ) $= ? $.
```

*Hint:* `notnotr` is `syl` of the `pm2.21` instance `( -. -. ph -> ( -. ph -> ph ) )`
and `pm2.18`. `notnot` is `con4i` applied to the `notnotr` instance
`( -. -. -. ph -> -. ph )`.

**Question 21.** Prove the other three contraposition rules.

```metamath
${
  con2i.a $e |- ( ph -> -. ps ) $.
  con2i $p |- ( ps -> -. ph ) $= ? $.
$}

${
  con1i.1 $e |- ( -. ph -> ps ) $.
  con1i $p |- ( -. ps -> ph ) $= ? $.
$}

${
  con3i.a $e |- ( ph -> ps ) $.
  con3i $p |- ( -. ps -> -. ph ) $= ? $.
$}
```

*Hint:* in each case, use `syl` with `notnotr` or `notnot` (both, for `con3i`) to get
the hypothesis into the form `( -. A -> -. B )`, then use `con4i`.

**Question 22.** Prove `mto` (*modus tollens*).

```metamath
${
  mto.1 $e |- -. ps $.
  mto.2 $e |- ( ph -> ps ) $.
  mto $p |- -. ph $= ? $.
$}
```

*Hint:* `con3i`, then `ax-mp`.

**Question 23.** Prove `pm2.61i` (*proof by cases*). An ordinary proof that splits into
"suppose `ph`" and "suppose not `ph`" goes through this.

```metamath
${
  pm2.61i.1 $e |- ( ph -> ps ) $.
  pm2.61i.2 $e |- ( -. ph -> ps ) $.
  pm2.61i $p |- ps $= ? $.
$}
```

*Hint:* `con3i` on the first hypothesis, then `syl` with the second, gives
`( -. ps -> ps )`. Finish with `pm2.18`.

**Question 24.** Prove `pm2.65i` (*reductio ad absurdum*).

```metamath
${
  pm2.65i.1 $e |- ( ph -> ps ) $.
  pm2.65i.2 $e |- ( ph -> -. ps ) $.
  pm2.65i $p |- -. ph $= ? $.
$}
```

*Hint:* get `( ph -> -. ph )` with `con2i` and `syl`, then `( -. -. ph -> -. ph )` with
`notnotr`. Finish with `pm2.18` at `ph := -. ph`.

**Question 25.** Prove *Peirce's law*. It uses only `->`, but your proof will have to
go through negation. Why that can't be avoided is a chapter 05 topic.

```metamath
peirce $p |- ( ( ( ph -> ps ) -> ph ) -> ph ) $= ? $.
```

*Hint:* use `pm2.61i`, splitting on `ph`. In the `ph` case, an `ax-1` instance does
it. In the `-. ph` case, `pm2.21` gives `( ph -> ps )`, and an instance of `pm2.27`
takes it the rest of the way. Chain these with `syl`.

## 04.5 Other proof databases

The important comparison is what *the same Metamath verifier* does with very
different statements and primitive rules. Keep these exercises in separate
practice files: `id`, `mpd`, and even `|-` need not have the same role in
different databases. The links go to the actual source databases; where only
a small fragment is displayed, use that fragment as a new `.mm` file.

### `iset.mm`: intuitionistic negation

[`iset.mm`](https://github.com/metamath/set.mm/blob/develop/iset.mm)
uses familiar `wff`, `|-`, `->`, and `-.` notation, but begins its negation
development with `ax-in1` and `ax-in2` rather than `set.mm`'s `ax-3`:

```metamath
ax-in1 $a |- ( ( ph -> -. ph ) -> -. ph ) $.
ax-in2 $a |- ( -. ph -> ( ph -> ps ) ) $.
```

Assume we have already proved `id`, and `con2i`, whose premise and conclusion
are `|- ( ph -> -. ps )` and `|- ( ps -> -. ph )`. Prove the actual
[`notnot`](https://us.metamath.org/ileuni/notnot.html):

```metamath
notnot $p |- ( ph -> -. -. ph ) $= ? $.
```

*Hint:* apply `id` to `-. ph`, then `con2i`. In this case, the same result
holds in classical `set.mm` and intuitionistic `iset.mm`, although its proof
need not use the same rules. The converse is a different question.

### `ql.mm`: an equational language

The beginning of [`ql.mm`](https://github.com/metamath/set.mm/blob/develop/ql.mm)
is an equational system for ortholattices, with `term` variables and
orthocomplement written `'`. Its first `id` proof uses this small fragment:

```metamath
$c term wff |- ' = $.
$v a b c $.
wva $f term a $.
wvb $f term b $.
wvc $f term c $.
wn $a term a ' $.
wb $a wff a = b $.
ax-a1 $a |- a = a ' ' $.
${
  r1.1 $e |- a = b $.
  ax-r1 $a |- b = a $.
$}
${
  r2.1 $e |- a = b $.
  r2.2 $e |- b = c $.
  ax-r2 $a |- a = c $.
$}

id $p |- a = a $= ? $.
```

*Hint:* use double orthocomplementation, reverse that equation, and compose.
The proof uses neither implication nor a propositional modus ponens rule.

### `hol.mm`: explicit contexts

[`hol.mm`](https://github.com/metamath/set.mm/blob/develop/hol.mm)
uses simply typed terms. Statements look like `|- R |= S`, with an explicit
context `R`. `( S , T )` combines context assumptions, and `[ S ==> T ]`
is a term built using defined implication.

The actual early theorem [`syl2anc`](https://us.metamath.org/holuni/syl2anc.html)
is (below, only its essential hypotheses and target are shown):

```metamath
${
  syl2anc.1 $e |- R |= S $.
  syl2anc.2 $e |- R |= T $.
  syl2anc.3 $e |- ( S , T ) |= A $.
  syl2anc $p |- R |= A $= ? $.
$}
```

Use the primitive context-combination rule `ax-jca` and the primitive
transitivity rule `ax-syl`. The point is to construct `( S , T )` in context
`R`, then apply the third hypothesis. In the actual database there are type
hypotheses and syntax declarations in addition to the excerpt above.

Now the particularly good example: **modus ponens is itself a proved theorem
in `hol.mm`.** Its primitive inference mechanism includes equality transport
(`ax-eqmp`); implication has been *defined*. The actual theorem is
[`mpd`](https://us.metamath.org/holuni/mpd.html) (with its essential
hypotheses shown, but not the earlier `hol.mm` declarations):

```metamath
${
  mp.1 $e |- T : * $.
  mp.2 $e |- R |= S $.
  mp.3 $e |- R |= [ S ==> T ] $.
  mpd $p |- R |= T $= ? $.
$}
```

For this puzzle, use the preceding results `imval`, `a1i`, `mpbi`,
`mpbir`, `dfan2`, and `simprd`. `imval` rewrites implication as an equality
involving conjunction; `mpbi`/`mpbir` move along such equalities;
`dfan2` relates Boolean conjunction to context conjunction; `simprd`
projects the right conjunct. Starting with the two premises, obtain
`R |= [ [ S /\ T ] = S ]`, then `R |= [ S /\ T ]`, then `R |= ( S , T )`,
and finally `R |= T`.

This is a puzzle about *the actual rule dependencies*, not a claim that
one database has a special privilege to define what modus ponens 'really is'.

## 04.6 Optional: Meredith's single axiom

This is an advanced substitution puzzle, not a prerequisite to Chapter 05.
The [Metamath development of Meredith's axiom](https://us.metamath.org/mpeuni/meredith.html)
is unusually striking: using `->`, `-.`, and modus ponens, it connects
one very large axiom schema with familiar sets of three schemas. The
`set.mm` labels below are real labels; start from a separate small system
where the Meredith schema is available, rather than using the earlier
`set.mm` theorems to short-circuit the exercise.

Write `M(a,b,c,d,e)` for the schema

$$
M(a,b,c,d,e) =
\left(\left(\left((a\to b)\to(\neg c\to\neg d)\right)\to c\right)\to e\right)
\to\left((e\to a)\to(d\to a)\right).
$$

As a compact exercise sequence, use the supplied intermediate lemmas.
Their proofs in `set.mm` are deliberately *not* homework here. The difficult
part of the original discovery has already been done; reconstruct the
specified substitutions and modus-ponens steps.

**`merlem1`.** Derive

$$
((c\to(\neg a\to b))\to t)\to(a\to t).
$$

For a guided reconstruction, let
`N = (¬a → b)`, `X = (¬t → ¬c)`,
`Y = ((N → (¬X → ¬¬N)) → X) → t`, and
`Z = (t → ¬a) → (¬N → ¬a)`.
Use `M(¬a,b,X,¬N,t)`, `M(N,(¬X → ¬¬N),t,c,Z)`,
and `M(t,¬a,N,a,(c → N))`, in that order. See
[`merlem1`](https://us.metamath.org/mpeuni/merlem1.html).

**`luk-3`.** Derive `a → (¬a → b)` from `merlem1` and the supplied
[`merlem11`](https://us.metamath.org/mpeuni/merlem11.html),
`(x → (x → y)) → (x → y)`. Use `merlem11` with `(x,y)=(¬a,b)`;
then use `merlem1` with `c = ¬a` and `t = (¬a → b)`.
[Result: `luk-3`](https://us.metamath.org/mpeuni/luk-3.html).

**`luk-2`.** Derive `(¬a → a) → a`. You may use these lemmas, already
obtained from `M`:

- [`merlem4`](https://us.metamath.org/mpeuni/merlem4.html): `F(p,d,t) = t → ((t → p) → (d → p))`.
- [`merlem5`](https://us.metamath.org/mpeuni/merlem5.html): `D(p,q) = (p → q) → (¬¬p → q)`.
- `merlem11`: `W(p,q) = (p → (p → q)) → (p → q)`.

Put `N=(¬a → a)`, `R=(a → ¬N) → (¬¬a → ¬N)`, and `Q=(R → ¬a)`.
Use `D(a,¬N)`, `F(¬a,Q,R)`, `W(Q,¬a)`, `M(a,¬N,¬a,N,¬a)`, and
`W(N,a)`. [Result: `luk-2`](https://us.metamath.org/mpeuni/luk-2.html).

**`luk-1`.** Derive `(a → b) → ((b → c) → (a → c))`. The supplied lemma
[`merlem13`](https://us.metamath.org/mpeuni/merlem13.html) is

$$
B(p,q,r,s)=(p\to q)\to
\bigl(((s\to(\neg\neg r\to r))\to\neg\neg p)\to q\bigr).
$$

Set `S=(a → b)`, `T=(b → c) → (a → c)`,
`U=((c → c) → (¬¬¬a → ¬a)) → ¬¬a`, `V=(U → b)`, and
`Z=((T → a) → (¬¬¬S → ¬S)) → ¬¬S`.
Use `M(c,c,¬¬a,a,b)`, `B(a,b,¬a,(c → c))`,
`B(S,V,¬S,(T → a))`, and `M(T,a,¬¬S,S,V)`.
[Result: `luk-1`](https://us.metamath.org/mpeuni/luk-1.html).

`luk-1`, `luk-2`, and `luk-3` are the three Łukasiewicz schemas used
in this comparison, distinct from the `ax-1`, `ax-2`, and `ax-3` presentation
we began with. Deriving the three actual statements is suitable work here;
the *general assertion* that the presentations admit exactly the same
provable schemas is a Chapter 05 question. For the reverse derivations, see
[`ax1`](https://us.metamath.org/mpeuni/ax1.html),
[`ax2`](https://us.metamath.org/mpeuni/ax2.html), and
[`ax3`](https://us.metamath.org/mpeuni/ax3.html).

---

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
  [`idALT`](https://us.metamath.org/mpeuni/idALT.html),
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
