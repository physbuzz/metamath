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

## 4.1 Propositional calculus in `set.mm`

Let's start by building up some of the basic theorems and machinery of `set.mm`. We'll
pick apart and cannibalize the usual set proof database, but you still might find it useful
to visit [the Metamath Proof Explorer, page 1 of 513](https://us.metamath.org/mpeuni/mmtheorems1.html),
which is good reading. 

This section is formulated as a series of interdependent exercises which you can use to build up some 
pieces of set.mm, preferably in the start of a new file like `myset.mm`. There are hints and solutions,
and you can also find the theorem in `set.mm` or view it by editing the url
`https://us.metamath.org/mpeuni/<label>.html`. There's usually cool stuff to see in the metamath set 
explorer.

The proof database we'll start with is:

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

[^1]: Unless otherwise stated, hints are given from the perspective of working back from the statement to be proved, so "use `ax-mp`" means "assign `ax-mp` to the statement."

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

Prove double negation elimination and introduction.

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

### 4.1.6 Notes and reflections and TODO on these exercises.


#### TODO on proof transformations

I got quite stuck on some proofs in 4.1 where I wanted to manipulate 
symbols deep inside the formulas. For example, if we have something like this:

`( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) )`

In the full set.mm database there's a theorem that shows we can commute psi and
phi in a formula like this. But I found it very difficult to figure out how to 
do this from scratch, or how to reason about "breaking out" the formula from the
implication. 

So number one, this is totally a skill I could develop if I studied it.

Number two, there should be an algorithm to convert the proof of "commutation
of antecedents" in inference form into a proof of this. (Though actually the sentence "once you have an assertion in deduction form, you can easily convert it to inference form or closed form" on the [Metamath proof explorer](https://us.metamath.org/mpeuni/mmnatded.html) page is relevant).

Number three, we should be able to create an algorithm, relying on `ax-3`, 
which uses the truth table of the statement to prove it. 

So there are tons of ways to prove this, I feel like I should skip those projects to
 save on time, but this might be something I wanna come back to later.

#### Thoughts on inference, deduction, closed

NB: Like always this is a beginner's question from a beginner's perspective.

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

## 4.2 Other proof databases

> [!WARNING]
> I'm not going into nearly as much detail with this section; I got burnt out on the
> entry level logic stuff. So yeah, not spending as much time to do proofreading.

### 4.2.1 `iset.mm` takeaways


The [intuitionistic database `iset.mm`](https://github.com/metamath/set.mm/blob/develop/iset.mm) develops theory with different axioms for defining negation
than in classical logic. These are
[`ax-in1`](https://us.metamath.org/ileuni/ax-in1.html) and
[`ax-in2`](https://us.metamath.org/ileuni/ax-in2.html):

```metamath
ax-in1 $a |- ( ( ph -> -. ph ) -> -. ph ) $.
ax-in2 $a |- ( -. ph -> ( ph -> ps ) ) $.
```

`ax-in1` looks a bit like the Clavius law 
$\vdash (\neg\varphi\to\varphi)\to\varphi)$, with the nots switched around.
`ax-in2`  is just `pm2.21` that we proved in classical logic. 

Theorems [`con2i`](https://us.metamath.org/ileuni/con2i.html) and
[`notnot`](https://us.metamath.org/ileuni/notnot.html) can still be 
proved with some changes.

```metamath
${
  con2i.a $e |- ( ph -> -. ps ) $.
  con2i $p |- ( ps -> -. ph ) $= ? $.
$}

notnot $p |- ( ph -> -. -. ph ) $= ? $.
```

However `con4i` and `notnotr` don't hold!

*Hints for filling in the proofs yourself:*

- For `con2i`, use `syl` with an instance of `ax-in1` as its second premise.
  For the remaining goal, try `com12`. Explosion will help further back.
- For `notnot`, use `con2i`. The remaining goal is an identity.

### 4.2.2 Quantum Logic `ql.mm`

[`ql.mm`](https://github.com/metamath/set.mm/blob/develop/ql.mm) develops
ortholattices and quantum logic cf. [Pavičić 1992](https://doi.org/10.1007/BF00671784), 
"A new axiomatization of unified quantum logic". Let's just 
borrow its very first proof, `id`. An important operation is known as the
orthocomplement, and of course the orthocomplement, having the word "complement"
in its name, should have `a = a ' '`, which is an axiom of the system.

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

#### Hints and my answers

- Use `ax-r2`. Pick an intermediate term that lets `ax-a1` supply one premise;
  the other premise will need its direction reversed.

```mm
$( kinda fun not gonna lie $)
id $p |- a = a $=
  wva wva wn wn wva wva ax-a1 wva wva wn wn wva ax-a1 ax-r1 ax-r2 $.
```

### 4.2.3 Higher Order Logic `hol.mm`

In section 4.1, an assumption was usually a separate `$e` statement. The
[higher-order logic database `hol.mm`](https://github.com/metamath/set.mm/blob/develop/hol.mm)
also has statements of the form

```text
|- R |= S
```

Read this as "under assumption `R`, we have `S`." The assumption is now part of
the expression! `R` and `S` have type `term`, and `( S , T )` combines two
assumptions. The `|=` symbol separates the context from the conclusion. It is
another declared constant, not an instruction to the Metamath program.

Here is enough of the language to try a first exercise in its own file. These
are the context-combination and transitivity rules from `hol.mm`, together with
the syntax they need.

```metamath
$c term |- |= ( , ) $.
$v A B R S T $.
ta $f term A $.
tb $f term B $.
tr $f term R $.
ts $f term S $.
tt $f term T $.
kct $a term ( A , B ) $.

${
  ax-syl.1 $e |- R |= S $.
  ax-syl.2 $e |- S |= T $.
  ax-syl $a |- R |= T $.
$}
${
  ax-jca.1 $e |- R |= S $.
  ax-jca.2 $e |- R |= T $.
  ax-jca $a |- R |= ( S , T ) $.
$}

${
  syl2anc.1 $e |- R |= S $.
  syl2anc.2 $e |- R |= T $.
  syl2anc.3 $e |- ( S , T ) |= A $.
  syl2anc $p |- R |= A $= ? $.
$}
```

Prove [`syl2anc`](https://us.metamath.org/holuni/syl2anc.html). Its first two
hypotheses get us `S` and `T` in context `R`; its third knows how to get `A`
from their combination. We still have to express that little argument as
substitutions and proof steps.

The next exercise needs more of the database. Use [hol.mm](code-04/hol.mm), which
supplies the supporting theorems and leaves `syl2anc` and `mpd` blank. Some of the
supplied proofs are compressed; you can use their statements without unpacking
their proofs. For example, start with:

```text
read hol.mm
prove syl2anc
```

Then try [`mpd`](https://us.metamath.org/holuni/mpd.html):

```metamath
${
  mp.1 $e |- T : bool $.
  mp.2 $e |- R |= S $.
  mp.3 $e |- R |= [ S ==> T ] $.
  mpd $p |- R |= T $= ? $.
$}
```

There are two different kinds of type information here. `$f term T` says that
`T` is a syntactic term. The hypothesis `|- T : bool` is an assertion *about*
that term: it has Boolean type. On the proof explorer, `bool` is displayed as
`∗`. Use `bool` in the source file.

`[ S ==> T ]` is implication, while `[ S /\ T ]` is Boolean conjunction.
The square brackets are part of the syntax. Context conjunction `( S , T )`
and Boolean conjunction `[ S /\ T ]` look related, but they are different
strings, so we need a theorem to pass between them.

The interesting bit is that modus ponens is a theorem here. Implication has
been defined using equality and conjunction. One of the primitive rules,
`ax-eqmp`, transports an assertion along an equality. The derived rules `mpbi`
and `mpbir` do that with the bracket notation, in opposite directions.

These are the useful tools to inspect before starting:

| Label | What to look for |
| --- | --- |
| `imval` | Relates `[ S ==> T ]` to `[ [ S /\ T ] = S ]`. |
| `a1i` | Moves a theorem from the true context `T.` into a Boolean context `R`. |
| `mpbi`, `mpbir` | Replace a term by an equal term inside a fixed context. |
| `dfan2` | Relates `[ S /\ T ]` to `( S , T )`. |
| `simprd` | Extracts the right member of a context conjunction. |
| `ax-cb1`, `ax-cb2` | Extract Boolean type assertions about the context and conclusion. |

The names overlap with `set.mm`, but read their statements again. In particular,
the hypotheses required by `a1i` are different. This is a good place to let the
proof assistant show us exactly which strings are still missing.

#### Hints and my answers

- For `syl2anc`, use `ax-syl` with the third hypothesis as its second premise.
- For `mpd`, use `simprd`. The remaining goal needs a context conjunction;
  `dfan2` will let you work back to a Boolean conjunction.
- A second hint for `mpd`: to obtain the Boolean conjunction from the hypothesis
  `R |= S`, look at `mpbir`. Its equality premise comes from the implication
  hypothesis and `imval`. Keep track of the context when using that theorem.

### 4.2.4 MIU: just rewriting strings

The [MIU system](https://us.metamath.org/metamath/miu.mm) comes from the beginning
of Hofstadter's *Gödel, Escher, Bach*. This time, we don't even need to pretend
that the strings are logical formulas. We start with `M I` and apply four
rewriting rules.

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

Read the syntax declarations first. `we` makes the empty string, and `wM`,
`wI`, and `wU` append a letter. `wxy` concatenates two strings. The typecode is
called `wff`, but it allows any finite string of these letters, including the
empty string. It doesn't mean "propositional formula" in this file.

The four rules say:

- `I_`: if a string ends in `I`, append `U`.
- `II`: after an initial `M`, double the rest of the string.
- `III`: replace an occurrence of `I I I` with `U`.
- `IV`: delete an occurrence of `U U`.

For the last two, `x` and `y` are the pieces on either side of the occurrence
we picked. Either piece can be empty. If unification gives several choices,
we're choosing *which part of the string* to rewrite.

Prove the database's `theorem1`, then prove a rule that doubles twice:

```metamath
theorem1 $p |- M U I I U $= ? $.

${
  II2.1 $e |- M x $.
  II2 $p |- M x x x x $= ? $.
$}
```

For an extra exercise, construct a proof of `|- M I I I I I I I I`.
Writing down the sequence of strings first is useful here. Then translate
each rewrite into a rule application, including the syntax proofs for the
strings substituted for `x` and `y`.

The famous MU puzzle asks whether we can reach `M U`. That is worth thinking
about, but don't spend forever trying to fill in a `$p` for it. In chapter 5
we'll ask how to establish that a target has *no* proof.

#### Hints and my answers

- For `theorem1`, try `III` as the last step. A useful earlier string has only
  `M` followed by `I`s; look for one whose length you can reach by doubling.
- For `II2`, use `II`. The string substituted for its `x` need not be a single
  copy of our variable `x`; `wxy` is useful for its syntax proof.
- For the eight-`I` exercise, keep using `II` until the remaining goal is `ax`.

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

## 4.3 Optional: Meredith's single axiom

Back to implication and negation. We started with three logical axioms and
modus ponens. Could we replace those three axioms with just one?

[Meredith's axiom](https://us.metamath.org/mpeuni/meredith.html) does this.
It is a fairly intimidating string, but it uses the same formula syntax we
already know how to parse:

```metamath
meredith $a |- ( ( ( ( ( ph -> ps ) -> ( -. ch -> -. th ) ) -> ch ) -> ta ) ->
                ( ( ta -> ph ) -> ( th -> ph ) ) ) $.
```

Use [meredith.mm](code-04/meredith.mm) for these exercises. Its logical axioms
are `meredith` and `ax-mp`; it also has the familiar syntax declarations. The
supporting lemmas are supplied as `$p` statements. They eventually depend on
`merlem1`, which is the first blank to fill in.

We won't try to rediscover the whole development. That would be a very different
exercise! The task here is to assemble some carefully chosen instances with
modus ponens. The notation in the hints abbreviates formulas; it doesn't add
new symbols to the database.

### 4.3.1 A first lemma

Prove [`merlem1`](https://us.metamath.org/mpeuni/merlem1.html):

```metamath
merlem1 $p |- ( ( ( ch -> ( -. ph -> ps ) ) -> ta ) -> ( ph -> ta ) ) $= ? $.
```

Here is a more guided hint than usual. Write `M(a,b,c,d,e)` for the Meredith
axiom with those five formulas substituted for `ph`, `ps`, `ch`, `th`, and `ta`.
For this paragraph, rename the variables of the target to `a,b,c,t`, and put

```text
N = (¬a → b)
X = (¬t → ¬c)
Z = ((t → ¬a) → (¬N → ¬a))
```

The three instances you need are

```text
M(¬a, b, X, ¬N, t)
M(N, (¬X → ¬¬N), t, c, Z)
M(t, ¬a, N, a, (c → N))
```

Start with `ax-mp` at the target, and work out which instance can supply the
implication. The remaining goal needs one more use of modus ponens. Writing
the three instances out is probably less painful than trying to hold them in
your head.

### 4.3.2 Recovering three familiar statements

Once `merlem1` is filled in, the supplied proofs establish the remaining
`merlem` lemmas. Use them to prove the following, in the order `luk-3`, `luk-2`,
then `luk-1`:

```metamath
luk-3 $p |- ( ph -> ( -. ph -> ps ) ) $= ? $.

luk-2 $p |- ( ( -. ph -> ph ) -> ph ) $= ? $.

luk-1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $= ? $.
```

These are the [Łukasiewicz axioms](https://us.metamath.org/mpeuni/luk-1.html)
used in this development. We recognize their statements as explosion, Clavius
law, and a closed form of syllogism. Here they are theorems derived from
Meredith's axiom, so borrowing their section 4.1 proofs would defeat the point.

The useful supplied lemmas are:

| Label | Formula, with variables renamed for readability |
| --- | --- |
| `merlem4` | `t → ((t → p) → (d → p))` |
| `merlem5` | `(p → q) → (¬¬p → q)` |
| `merlem11` | `(p → (p → q)) → (p → q)` |
| `merlem13` | `(p → q) → (((s → (¬¬r → r)) → ¬¬p) → q)` |

#### Hints and my answers

- For `luk-3`, use `ax-mp` with an instance of `merlem1` as the implication.
  Look for a way to make its antecedent an instance of `merlem11`.
- For `luk-2`, use `ax-mp` with `merlem11` as the implication, treating
  `( -. ph -> ph )` as a single wff. An instance of `meredith` supplies the
  repeated-antecedent goal after another detachment.
- For `luk-1`, the outer step is again `ax-mp`. One premise is an instance of
  `meredith`; the other takes more detachment steps using `merlem13` and `meredith`.

For the last two, these substitutions give a more detailed route if needed.
Write `D(p,q)`, `F(p,d,t)`, `W(p,q)`, and `B(p,q,r,s)` for the four lemmas in
the order `merlem5`, `merlem4`, `merlem11`, and `merlem13`.

For `luk-2`, let

```text
N = (¬a → a)
R = ((a → ¬N) → (¬¬a → ¬N))
Q = (R → ¬a)
```

Combine `D(a,¬N)`, `F(¬a,Q,R)`, `W(Q,¬a)`, `M(a,¬N,¬a,N,¬a)`, and `W(N,a)`
using modus ponens. Each formula you detach becomes an input to another step.

For `luk-1`, let

```text
S = (a → b)
T = ((b → c) → (a → c))
U = (((c → c) → (¬¬¬a → ¬a)) → ¬¬a)
V = (U → b)
```

Combine `M(c,c,¬¬a,a,b)`, `B(a,b,¬a,(c → c))`, `B(S,V,¬S,(T → a))`,
and `M(T,a,¬¬S,S,V)`.

The proof explorer continues by deriving our original axioms as
[`ax1`](https://us.metamath.org/mpeuni/ax1.html),
[`ax2`](https://us.metamath.org/mpeuni/ax2.html), and
[`ax3`](https://us.metamath.org/mpeuni/ax3.html). In the other direction,
`set.mm` proves Meredith's formula from its original axioms. That gives us
the ingredients for translating proofs between the presentations.

---

# 5 Metatheorems, notation, and history

We've been asking for particular strings and checking particular proofs.
Now some different questions are starting to pile up. Why can't we prove
`M U`? Why do so many theorems have inference, deduction, and closed forms?
If we change the axioms but can recover the old ones, have we kept *all* the
same theorems?

These are things we can investigate with programs, too. We can represent a
formula as data, write a function that checks a proof, and write another
function that transforms it. Eventually we can express claims about those
functions in a Metamath database and try proving them there.

This chapter is still a set of working notes. I want to keep the concrete
questions in view while learning the vocabulary people use to talk about them.

## 5.1 Statements about statements

Logicians call the language being studied the *object language*, and the
language used to discuss it the *metalanguage*. In our files, the object
language is what appears in the assertions. English sentences such as
"this proof verifies" and "there is no proof of `|- M U`" are statements
about those assertions and their proofs.

Metamath doesn't force us to stop there. We could encode MIU strings and MIU
derivations as objects in `set.mm`, then write a theorem about those objects.
We would have changed which strings represent the thing we're discussing.
The verifier would still be doing substitution and checking proof steps.

This helps me separate three tasks:

1. Check a particular proof.
2. Write a program that produces or transforms proofs.
3. Prove that the program works for every input of the required kind.

Getting task 1 to work is useful evidence while doing task 2. Task 3 needs
definitions of the inputs, outputs, and what "works" means. That's a project
we haven't carried out yet.

### 5.1.1 Some notation to recognize

`Γ ⊢ φ` usually means that `φ` is derivable from assumptions `Γ`. The special
case `⊢ φ` has no assumptions. A textbook may display an inference rule like
this:

```text
  φ      φ → ψ
 ───────────────
        ψ
```

We recognize `ax-mp`. Its two `$e` statements go above the line and its
assertion goes below. A Metamath proof of an instance supplies substitutions
and proofs of those premises.

Our literal `|-` is a declared constant. The textbook's `⊢` is often notation
for a claim about derivability. The resemblance is intentional, but we should
check which role it has in a particular sentence.

`Γ ⊨ φ` is usually a different claim: every interpretation satisfying `Γ`
also satisfies `φ`. For propositional logic, the interpretations can be truth
assignments. To work with that claim concretely, we would define truth
assignments and evaluation, then ask how they relate to our proof rules.
The characters `|=` in `hol.mm` are part of that database's context notation;
they don't instruct Metamath to evaluate truth assignments.

Arrows are similarly overloaded. `->` is our implication connective. Books
also write `→`, `⊃`, or sometimes `⇒`. In our sequent file, `=>` separates two
contexts. Read the declarations before trusting the shape of the symbol.

### 5.1.2 Schemas and deductions

In many textbooks, `p` is a particular propositional variable and `φ` ranges
over formulas. Our `ph` plays the latter role: we may substitute any expression
with a suitable `wff` proof. Thus `|- ( ph -> ph )` gives a *schema* of
theorems, rather than just one fixed sentence about an atom named `ph`.

The word *deduction* also shifts around. A textbook deduction is often a
sequence of formulas, each an assumption, an axiom instance, or the result of
an inference rule. In `set.mm`, "deduction form" means the convention with
a shared antecedent. Related ideas, but the suffix `d` isn't itself a
theorem about arbitrary proof sequences.

A *metatheorem* is a theorem about a formal system. The questions below are
examples. Calling something a metatheorem doesn't prevent us from representing
its subject matter inside another formal system.

## 5.2 The deduction theorem as a proof transformation

Suppose we have a proof of `ps` that uses `ph` as a hypothesis. Can we turn it
into a proof of `( ph -> ps )` without that hypothesis?

For the propositional calculus from section 4.1, the usual deduction theorem
says yes. In textbook notation:

```text
If Γ; α ⊢ β, then Γ ⊢ (α → β).
```

There is a fairly concrete program hiding in the usual proof. Process the
original proof one line at a time, turning each formula `χ` into `α -> χ`.

- If the line is the assumption `α`, use `id`.
- If it is an axiom or another available assumption, use `a1i`.
- If it follows by modus ponens, use `mpd` on the transformed earlier lines.

Those are all tools we proved. We could first implement this for proofs using
only primitive rules. Derived rules can be expanded into their proofs, or we
can give the transformer suitable deduction-form replacements.

A useful first project would be to transform one of our small proofs and
have Metamath check the result. Then try a batch of proofs. The general
correctness argument says that each transformed line has the claimed form
and still has a valid justification. Formalizing that argument requires a
representation of proof sequences and of this transformation.

Quantifiers complicate the story. `set.mm` has a generalization rule, `ax-gen`,
which takes `|- ph` to `|- A. x ph`. Blindly treating it like the propositional
rules would suggest `( ph -> A. x ph )`. Taking `ph` to be `x = y` shows the
problem: knowing that this `x` equals `y` doesn't say that every `x` does.
The deduction theorem needs a restriction on generalizing variables that are
free in the assumption being discharged. We'll return to that with `$d`.

## 5.3 When a proof doesn't exist

The MIU exercises gave us proofs of specific strings. The MU puzzle asks for
something else: show that *no* sequence of the rules reaches `M U`.

Try tracking the number of `I`s modulo 3. Work out what each rule does to
that number, starting from the one `I` in the axiom. This is an invariant
argument about possible derivations. It isn't a missing MIU proof of some
new string saying "MU is impossible"; our MIU language has no such assertion.

Some projects to build up from there:

- Write a program that produces a proof of `M` followed by `2^k` copies of `I`.
  We already did the case `k = 3`.
- Encode a finite MIU derivation as data, and implement its checker.
- State and prove the invariant for those encoded derivations.
- Investigate the stronger characterization: the derivable strings are
  exactly those starting with one `M`, followed by `I`s and `U`s, whose
  number of `I`s is nonzero modulo 3. The reverse direction needs a construction,
  not just the invariant.

The [Mathlib MIU formalization](https://leanprover-community.github.io/mathlib4_docs/Archive/MiuLanguage/Basic.html)
is worth reading alongside [`miu.mm`](https://us.metamath.org/metamath/miu.mm).
The latter is also reproduced in Appendix D of the Metamath book.

### 5.3.1 Derivable and admissible rules

Here is another MIU puzzle:

```metamath
${
  bad.1 $e |- M U $.
  bad $p |- U $= ? $.
$}
```

Even if we grant the hypothesis `M U`, our rewriting rules don't give us a
way to remove the initial `M`. So this isn't a blank we should expect to fill.
The claim needs an argument about all rule applications, now allowing that
extra starting hypothesis.

A rule is *derivable* if its conclusion can be proved from its premises.
A rule is *admissible* if, whenever its premises are theorems, its conclusion
is also a theorem. These can come apart. Once we establish that `M U` is not
a theorem, the proposed rule above is admissible vacuously: its premise never
arises as a theorem. That still doesn't supply a proof from the hypothetical
premise `bad.1`.

The sequent system gives a less vacuous example to investigate. Consider adding
an extra formula on the left:

```metamath
${
  wk.1 $e |- G => D $.
  wk $p |- G ph => D $= ? $.
$}
```

This operation is called *weakening*. Inspect the conclusions of our primitive
rules. Which one could be the last step of this schematic proof? Then consider
a different task: given a concrete proof of `G => D`, transform every sequent
in it to carry the extra formula. The second task has access to the proof
behind the premise, which a single use of `wk.1` doesn't expose.

## 5.4 Cut and proof search

In the sequent exercises, working backwards through a logical rule removes
a connective from the selected formula. Each resulting premise has fewer
connectives in total than the goal. If the same formula appears on both
sides, `ax-id` finishes that branch.

That suggests a proof-search program. Choose a connective, apply its rule
backwards, and recursively solve the resulting premises. The recursion
terminates because the formulas get smaller. A branch with only atoms and
no common formula is stuck. To turn this into a decision procedure, we also
need to justify that the search doesn't miss a proof. For these rules,
that is the role of the invertibility arguments.

Cut behaves differently. Its cut formula is absent from the conclusion, so
working backwards would mean guessing a formula that might be arbitrarily
large. In our `seqmp` proof we knew what to choose, because the hypotheses
gave us useful formulas to connect.

*Cut elimination* says that a closed derivation using cut can be transformed
into one without cut in calculi of this kind. Here "closed" means that all
leaves are axioms; arbitrary extra `$e` leaves need separate treatment. This
qualification matters for our `seqmp` exercise, whose premises are supplied
as hypotheses.

Projects for this particular encoding:

- Implement the backward search and have it emit proofs our checker accepts.
- Show that the logical rules preserve provability when used backwards.
- Work out a cut-elimination transformation for closed derivations.
- Formalize the *subformula property*: the formulas in a cut-free closed
  proof come from pieces of its final sequent.
- Use this to investigate consistency. No rule of the cut-free system can
  conclude the empty sequent `|- =>`.

The `seqax1`–`seqax3` proofs and `seqmp` also suggest a translator from our
Hilbert-style proofs to sequent proofs. That would be a nice way to connect
the two sets of exercises: feed in an existing proof, get out a proof written
in the other language, and check it.

## 5.5 Changing the axioms

The Meredith exercises suggest another translator. If one system can prove
each axiom schema of another and has the same modus ponens rule, we can try
replacing every axiom use in an old proof with the corresponding derivation.

There are three presentations to compare:

| Presentation | Logical axioms, besides modus ponens |
| --- | --- |
| Our original `set.mm` fragment | `ax-1`, `ax-2`, `ax-3` |
| Meredith | `meredith` |
| Łukasiewicz | `luk-1`, `luk-2`, `luk-3` |

The relevant derivations are linked in section 4.3. First make a translator
work on a few proofs. Then describe why replacement commutes with substitution
and why each resulting proof step is valid. That is how the finite list of
axiom derivations supports a claim about *all* theorems.

There are other comparisons where this won't be enough. For example, our
intuitionistic fragment doesn't recover `ax-3`. To show a separation, we need
to establish that a target really is unprovable in the weaker system. Peirce's
law is an especially interesting target because its statement doesn't even
contain negation.

## 5.6 Further directions

There is plenty here before we need to add more syntax. A few things I want
to keep on the list:

- Truth tables and models: define evaluation of formulas, then investigate
  soundness and completeness for a chosen set of proof rules.
- Gentzen's sequent calculus and cut elimination: connect the textbook rules
  with the concrete calculus in section 4.2.5.
- Lambda calculus, recursive functions, and Turing machines: work through
  explicit translations between models of computation.
- Curry–Howard: find a particular proof calculus and a particular typed
  programming language, and see what their correspondence actually does.
- Automath, Mizar, LCF, and the Boyer–Moore prover: compare how they represent
  proofs and what their checkers trust.
- Mario Carneiro's work on Metamath and [Metamath Zero](https://github.com/digama0/mm0):
  look for concrete definitions of syntax, proofs, and verification that we
  can build on.

### 5.6.1 Arithmetic, later

The [Number Theory Game for Metamath](https://github.com/pbrosnan/ntg) develops
arithmetic using Robert Solovay's `peano.mm`. This will be useful once we've
worked with quantifiers and disjoint variables.

Its notation is another reminder to read the syntax declarations. `+ a b`
is prefix addition, `S t` is successor, and `= s t` is an equality. The
variables themselves have type `var`; expressions built from them have type
`term`. Even the order of syntax inputs deserves a look: `tbinop` takes the
two terms followed by the operator.

Some targets to return to, with links to a fixed source revision:

- [`nn26l1`](https://github.com/pbrosnan/ntg/blob/15332ee0dfe50ada14b6e31e947272232e4dc671/peano.mm#L2884-L2891):
  prove `(a+b)+0 = a+(b+0)` using the zero law and congruence.
- [`pa_ax3cl2`](https://github.com/pbrosnan/ntg/blob/15332ee0dfe50ada14b6e31e947272232e4dc671/peano.mm#L2817-L2820):
  from `t=0+t`, prove `S(t)=0+S(t)`.
- [`pa_ax3c`](https://github.com/pbrosnan/ntg/blob/15332ee0dfe50ada14b6e31e947272232e4dc671/peano.mm#L2812-L2835):
  prove `t=0+t` using the induction rule `nindd`.
- [`addcom`](https://github.com/pbrosnan/ntg/blob/15332ee0dfe50ada14b6e31e947272232e4dc671/peano.mm#L2930-L2959):
  prove `a+b=b+a` by induction.

The introduction to that database also discusses the distinction between its
formal statements and mathematical arguments about the system. That seems
like useful reading alongside our attempts to turn those arguments into
explicit proof transformations.

### 5.6.2 A small geometry puzzle

One more possible change of scenery: let `Cg A B C D` say that segment `AB`
is congruent to segment `CD`. Suppose our rules say

```text
Cg A B B A

from Cg A B C D and Cg A B E F, infer Cg C D E F
```

Can we prove `Cg A B A B`? Write the declarations and rules as a little
Metamath file, then fill in the proof. These are patterned on segment-congruence
axioms in [Tarski-style geometry](https://us.metamath.org/mpeuni/df-trkg.html).
The small exercise is ours; there is no need to import a whole geometry
database to try it.
