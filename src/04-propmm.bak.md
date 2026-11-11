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

> [!WARNING]
> These notes were discarded because I couldn't stand the suggestive but ultimately poor
> pedagogical statements about metamathematics. Nov 10 2026

> [!WARNING]
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

To start, here's some basic theorems: [`a1i`](https://us.metamath.org/mpeuni/a1i.html),
[`a2i`](https://us.metamath.org/mpeuni/a2i.html), [`mpd`](https://us.metamath.org/mpeuni/mpd.html),
[`syl`](https://us.metamath.org/mpeuni/syl.html), and [`id`](https://us.metamath.org/mpeuni/id.html).

Note that here we start seeing some of the conventions of set.mm, where the suffix
i generally stands for inference form, suffix d stands for deduction form, and no
suffix generally stands for closed form. This is discussed various places in the proof explorer
[such as here](https://us.metamath.org/mpeuni/mmnatded.html) and in the book [html page](https://www.mathandcode.com/books/metamath/book/metamath.html#3.9.3-deduction-style) or [pdf page](book/metamath.pdf#page=115). The proof explorer
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

#### Hints and my answers

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
id $p |- ( ph -> ph ) $=
  wph wph wph wi wph wph wph ax-1 wph wph wph wi ax-1 mpd $.
```

The proof explorer also has [`idALT`](https://us.metamath.org/mpeuni/idALT.html), which proves
`id` without `mpd` and which proves the same statement directly from the axioms, as well as
giving some nice exposition.

After the hints, we can simplify the proofs of `mpd` and `syl` to be much shorter:

```mm
mpd $p |- ( ph -> ch ) $=
  wph wps wi wph wch wi mpd.1 wph wps wch mpd.2 a2i ax-mp $.
syl $p |- ( ph -> ch ) $=
  wph wps wch syl.1 wps wch wi wph syl.2 a1i mpd $.
```

### 4.1.2 More advanced implications

Prove [`pm2.43i`](https://us.metamath.org/mpeuni/pm2.43i.html),
[`a1d`](https://us.metamath.org/mpeuni/a1d.html), [`a2d`](https://us.metamath.org/mpeuni/a2d.html),
[`sylcom`](https://us.metamath.org/mpeuni/sylcom.html), [`com12`](https://us.metamath.org/mpeuni/com12.html),
[`pm2.27`](https://us.metamath.org/mpeuni/pm2.27.html), and [`imim2i`](https://us.metamath.org/mpeuni/imim2i.html).

These start to get a little more interesting.


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

#### Hints and my answers

- For `pm2.43i`, `ax-mp` isn't quite the right tool.
- `a1d` and `a2d` use syllogism.
- For `sylcom`, I find this at least a bit clever: use `syl` with `sylcom.1` as its first premise. If you're still
stuck, use `which step n` to find the other theorem you have to use.
- `com12` basically yields to 1 theorem, so `which` is your friend.
- For `pm2.27`, use `com12`. Look carefully at the remaining goal before doing any more work!
- For `imim2i`, use `a2i`. The remaining goal differs from the hypothesis by just one antecedent.


My solns:

```mm
pm2.43i $p |- ( ph -> ps ) $=
    wph wph wps wph id pm2.43i.1 mpd $.

a1d $p |- ( ph -> ( ch -> ps ) ) $=
    wph wps wch wps wi a1d.1 wps wch wps wi wi wph wps wch ax-1 a1i mpd $.

$( Rewrite after realizing to use syl: $)
a1d $p |- ( ph -> ( ch -> ps ) ) $=
  wph wps wch wps wi a1d.1 wps wch ax-1 syl $.

a2d $p |- ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) ) $=
  wph wps wch wth wi wi wps wch wi wps wth wi wi a2d.1 wps wch wth ax-2 syl
  $.

sylcom $p |- ( ph -> ( ps -> th ) ) $=
  wph wps wch wi wps wth wi sylcom.1 wph wps wch wth wps wch wth wi wi wph
  sylcom.2 a1i a2d mpd $.
$(improved proof: $)
sylcom $p |- ( ph -> ( ps -> th ) ) $=
  wph wps wch wi wps wth wi sylcom.1 wps wch wth sylcom.2 a2i syl $.

com12 $p |- ( ps -> ( ph -> ch ) ) $=
  wps wph wps wch wps wph ax-1 com12.1 sylcom $.

pm2.27 $p |- ( ph -> ( ( ph -> ps ) -> ps ) ) $=
  wph wps wi wph wps wph wps wps wps wps wi wph wps id a1i a2i com12 $.

imim2i $p |- ( ( ch -> ph ) -> ( ch -> ps ) ) $=
  wch wph wps wph wps wi wch imim2i.1 a1i a2i $.
```

### 4.1.3 More propositional calculus

Write proofs introducing more propositional calculus tools,
[`mpdd`](https://us.metamath.org/mpeuni/mpdd.html), [`syld`](https://us.metamath.org/mpeuni/syld.html),
[`imim1i`](https://us.metamath.org/mpeuni/imim1i.html), [`imim2`](https://us.metamath.org/mpeuni/imim2.html),
[`imim1`](https://us.metamath.org/mpeuni/imim1.html), [`pm2.43`](https://us.metamath.org/mpeuni/pm2.43.html),
and [`pm2.04`](https://us.metamath.org/mpeuni/pm2.04.html).

I had a tough time on this section, and only read later that the [Metamath proof explorer](https://us.metamath.org/mpeuni/mmnatded.html)
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

#### Hints and my answers

- For `mpdd`, use `mpd`, keeping `ph` as the shared antecedent. Compare the remaining
  premise with the deduction form of `a2i`.
- For `syld`, try `mpdd`. One hypothesis already fits; the other needs an extra
  antecedent inside `ph ->`.
- For `imim1i`, use `syld` with `( ps -> ch )` as the shared antecedent.
  Remember that a whole implication can take the place of a wff variable.
- For `imim2`, use `syl`. Look for an intermediate formula that lets `ax-2`
  supply the second premise.
- For `imim1`, try commuting the outer two antecedents. The remaining goal is
  an instance of an earlier theorem, with the variables shuffled around.
- `pm2.43` has the form of `a2i`'s conclusion, with a compound wff in place of one variable.
- For `pm2.04`, use `syl` with `ax-2` as its first premise. The other premise keeps
  `( ph -> ch )` as its consequent; look for an inference that changes an antecedent.

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

Now we introduce `ax-3`, meaning we're in the realm of classical logic. Up until now, our theorems
have been acceptable intuitionistic theorems. Prove the basic theorems
[`con4i`](https://us.metamath.org/mpeuni/con4i.html), [`con4d`](https://us.metamath.org/mpeuni/con4d.html),
[`pm2.21i`](https://us.metamath.org/mpeuni/pm2.21i.html), [`pm2.24ii`](https://us.metamath.org/mpeuni/pm2.24ii.html),
[`pm2.21d`](https://us.metamath.org/mpeuni/pm2.21d.html), [`pm2.21`](https://us.metamath.org/mpeuni/pm2.21.html),
[`pm2.24`](https://us.metamath.org/mpeuni/pm2.24.html), and [`pm2.18`](https://us.metamath.org/mpeuni/pm2.18.html).

```metamath
$( Inference form of axiom 3. "Con" is short for "contraposition" $)
${
  con4i.1 $e |- ( -. ph -> -. ps ) $.
  con4i $p |- ( ps -> ph ) $= ? $.
$}

$( Deduction form of axiom 3. $)
${
  con4d.1 $e |- ( ph -> ( -. ps -> -. ch ) ) $.
  con4d $p |- ( ph -> ( ch -> ps ) ) $= ? $.
$}

$( Principle of explosion: A contradiction implies anything. $)
${
  pm2.21i.1 $e |- -. ph $.
  pm2.21i $p |- ( ph -> ps ) $= ? $.
$}
$( Also principle of explosion. $)
${
  pm2.24ii.1 $e |- ph $.
  pm2.24ii.2 $e |- -. ph $.
  pm2.24ii $p |- ps $= ? $.
$}
$( deduction form of explosion $)
${
  pm2.21d.1 $e |- ( ph -> -. ps ) $.
  pm2.21d $p |- ( ph -> ( ps -> ch ) ) $= ? $.
$}

$( closed forms of explosion $)
pm2.21 $p |- ( -. ph -> ( ph -> ps ) ) $= ? $.
pm2.24 $p |- ( ph -> ( -. ph -> ps ) ) $= ? $.

$( Clavius law: if a formula follows from its own negation, then it's true. $)
pm2.18 $p |- ( ( -. ph -> ph ) -> ph ) $= ? $.
```


#### Hints and my answers

- `con4i` follows from modus ponens and an axiom.
- For `con4d`, use `syl` with the given hypothesis as its first premise.
- For `pm2.21i`, use `con4i`. The remaining goal just adds an antecedent to the hypothesis.
- For `pm2.24ii`, use `ax-mp` with `ph` as its first premise. The other hypothesis
  lets you use the explosion rule we just proved.
- For `pm2.21d`, use `con4d`. Keep `ph` as the shared antecedent while adding
  an antecedent inside it.
- For `pm2.21`, use `pm2.21d`. Choose the shared antecedent to match the goal,
  then look carefully at the remaining premise.
- For `pm2.24`, try commuting the two antecedents.
- For `pm2.18`, use `pm2.43i` with `( -. ph -> ph )` as a single wff.
  The remaining goal fits `con4d`; keep that same shared antecedent as you work backwards.

### 4.1.5 Double negation and classical proof rules

**Question 20.** Prove double negation elimination and introduction.

```metamath
$( Double negation elimination $)
notnotr $p |- ( -. -. ph -> ph ) $= ? $.

$( Double negation introduction $)
notnot $p |- ( ph -> -. -. ph ) $= ? $.
$( who's there? $)

$( Contraposition with a negated consequent: from ph -> -. ps, infer ps -> -. ph. $)
${
  con2i.a $e |- ( ph -> -. ps ) $.
  con2i $p |- ( ps -> -. ph ) $= ? $.
$}

$( Contraposition with a negated antecedent: from -. ph -> ps, infer -. ps -> ph. $)
${
  con1i.1 $e |- ( -. ph -> ps ) $.
  con1i $p |- ( -. ps -> ph ) $= ? $.
$}

$( Contraposition: from ph -> ps, infer -. ps -> -. ph. $)
${
  con3i.a $e |- ( ph -> ps ) $.
  con3i $p |- ( -. ps -> -. ph ) $= ? $.
$}

$( Modus tollens $)
${
  mto.1 $e |- -. ps $.
  mto.2 $e |- ( ph -> ps ) $.
  mto $p |- -. ph $= ? $.
$}

$( Proof by cases $)
${
  pm2.61i.1 $e |- ( ph -> ps ) $.
  pm2.61i.2 $e |- ( -. ph -> ps ) $.
  pm2.61i $p |- ps $= ? $.
$}

$( Reductio ad absurdum $)
${
  pm2.65i.1 $e |- ( ph -> ps ) $.
  pm2.65i.2 $e |- ( ph -> -. ps ) $.
  pm2.65i $p |- -. ph $= ? $.
$}

$( Peirce's law. Note that it seems to not use negation... but
   it's in the section with ax-3? How curious. $)
peirce $p |- ( ( ( ph -> ps ) -> ph ) -> ph ) $= ? $.
```

#### Hints and my answers

- For `notnotr`, use `syl` with `pm2.18` as its second premise. The other premise
  is an instance of explosion.
- For `notnot`, use `con4i`. The remaining goal is a double negation theorem
  with a negated wff substituted for its variable.
- For `con2i` and `con1i`, use `con4i`. A double negation appears in the remaining
  goal; use `syl` to connect it with the given hypothesis.
- For `con3i`, try `con2i`. Double negation introduction will help with the remaining goal.
- For `mto`, use `ax-mp` with the negated hypothesis as its first premise.
  The other premise needs contraposition.
- For `pm2.61i`, use `ax-mp` with an instance of `pm2.18` as its second premise.
  For the remaining goal, try `syl`; one of the given hypotheses needs contraposition.
- For `pm2.65i`, use `pm2.61i`, splitting on `ph`. One case is an identity;
  in the other, try `syl` with the two conflicting hypotheses, using contraposition on one.
- For `peirce`, use `pm2.61i`, splitting on `ph`. One case is an axiom instance;
  for the other, try `syl` with explosion as its first premise.

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

### 4.2.5 Sequent calculus: moving formulas across a separator

We can make a proof system where an implication is proved by moving its
antecedent to the other side of a separator. This is the idea behind the
implication-right rule in *sequent calculus*.

A sequent has a list of formulas on the left and another list on the right:

```text
ph ps => ch th
```

The usual reading is: if all the formulas on the left hold, then at least one
formula on the right holds. An empty left side needs no assumptions. An empty
right side represents a contradiction. That's the intended interpretation;
below are the actual strings and rules we'll ask Metamath to check.

`G`, `H`, `D`, and `E` have type `ctx`, for a list of formulas. So `G ph H`
means a list with `ph` somewhere in it. The commas in a textbook's presentation
are unnecessary here: the formula syntax already tells us where each formula
ends.

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

`c0` makes an empty context. `cadd` appends a formula to a context. For example,
the syntax proof of `ctx ph ps` is `wps wph c0 cadd cadd`. The floating hypotheses
put the formula before the context on the proof stack, even though the context
comes first in the resulting string. Watch the declaration order!

The logical rules are named for the connective they handle and the side it
appears on. `ax-negl` handles negation on the left; `ax-impr` handles implication
on the right. The latter says that to prove

```text
G H => D ( ph -> ps ) E
```

we can instead prove

```text
G ph H => D ps E
```

That is already an ordinary Metamath rule. We don't need to teach the verifier
about assumptions, discharge, or implication. We just have to supply its premise.

`ax-id` closes a goal when the same formula occurs on both sides. Here is the
identity theorem, using empty contexts everywhere:

```metamath
seqid $p |- => ( ph -> ph ) $=
  wph wph c0 c0 c0 c0 wph c0 c0 c0 c0 ax-id ax-impr $.
```

Now prove the three familiar axioms as theorems of this new system, then
Peirce's law and double negation elimination:

```metamath
seqax1 $p |- => ( ph -> ( ps -> ph ) ) $= ? $.

seqax2 $p |- => ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $= ? $.

seqax3 $p |- => ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $= ? $.

seqpeirce $p |- => ( ( ( ph -> ps ) -> ph ) -> ph ) $= ? $.

seqnotnotr $p |- => ( -. -. ph -> ph ) $= ? $.
```

This little calculus has a different feel from the Hilbert-style proofs in
section 4.1. Working backwards, we can pick a connective in the goal and use
the corresponding rule to break it apart. We aren't hunting for an arbitrary
intermediate formula for `syl`.

One more exercise needs another rule. Add *cut*, which lets us connect a proof
of a formula with a proof that uses that formula:

```metamath
${
  ax-cut.1 $e |- G => D ph $.
  ax-cut.2 $e |- H ph => E $.
  ax-cut $a |- G H => D E $.
$}
```

In `ax-cut`, `ph` occurs on the right of the first premise and on the left of
the second. It disappears from the conclusion. The remaining contexts are
concatenated. Use this rule to prove a form of modus ponens:

```metamath
${
  seqmp.1 $e |- => ph $.
  seqmp.2 $e |- => ( ph -> ps ) $.
  seqmp $p |- => ps $= ? $.
$}
```

For now, keep cut in the file for this last exercise. Whether every use of cut
can be removed is a much larger question, which we'll return to in chapter 5.

#### Hints and my answers

- For the five closed theorems, start with `ax-impr`. Then inspect which
  connectives are on which side. When a formula appears on both sides, use `ax-id`.
- For `seqpeirce`, after the first `ax-impr`, try `ax-impl`. One branch needs
  another `ax-impr`; the other closes immediately.
- For `seqmp`, use `ax-cut` with `seqmp.1` as its first premise. For the remaining
  goal, use another cut with `seqmp.2`. The last little sequent can be proved
  using the implication-left rule.