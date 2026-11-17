---
title: "4. Studying Propositional Calculus with Metamath"
---


<nav class="nav">
    <span class="activenav"><a href="03-interpreter.html">← Previous</a></span>
    <span class="activenav"><a href="index.html">↑ Up</a></span>
    <span class="activenav"><a href="05-predicate-calculus.html">Next →</a></span>
</nav>

<h1 id="04-propmm" style="border-bottom: none;">4. Studying Propositional Calculus with Metamath</h1>

Links: [Chapter html](book/index.html#abstract-mathematics-revealed), [pdf on metamath.org](https://us.metamath.org/downloads/metamath.pdf#page=77).

> [!NOTE]
> These notes have some AI-suggested problems in them that have not yet
> been reviewed.

@toc

## Introduction

Now that we're set on the intricacies of Metamath, sans 
disjoint variables and compressed proofs, I want to familiarize myself with classical logic
and similar systems with Metamath as grounding. 
Towards the end of these notes, I also try to tackle a few more creative systems in Metamath.

Note: I'm not going to write down tutorial information about proof assistants here, but this is
certainly the time to start using the built-in proof assistant, or Yamma or mmj2. 

I also got a bit frustrated mid-chapter and doubted whether it was worth it to work on these problems,
since things always expand to take up much more time than I think. Probably, it's good to work on these
for no other reason than to be able to interact with the Metamath community. 

## 4.0 Important Logic Notations and Citations

Okay, as someone independently studying things and from the rather biased and pigheaded view that 
I cannot take things as "proven" or "beyond folk-knowledge" until I've formalized them in Metamath,
I run the risk of developing crazy terminology that doesn't agree with literature. So I have to make sure
I get my citations right! 

While on the surface in this section we're battling propositional calculus, underneath we're really 
battling fundamental notions of proof. To my understanding, the requirement of making things concrete makes 
things so difficult
that we can't easily tackle them until we've got through a formalization of set theory and then some.
And from there, use set theory to build up a model[^1] of a formal language, and then prove theorems
in our Metamath + set.mm + model. That becomes our metatheorem, and the assertion that our model 
accurately describes the formal language could turn out to be a philosophically fraught question. 
There's some series of unproductive
arguments to have here, something like, "that's just a model of a system, not the system itself" -> "yeah
so is everything you've ever proved about it, there the model was parsed by your brain, here the model is
parsed by Metamath." Well, it will be nice to see how these statements age once I learn what they actually
mean anyways--"actually" = "as formalized in mm" of course :)

[^1]: I am using this term totally informally.

### 4.0.1 Hilbert-type inference rules

TODO: use the word "axiom scheme" where appropriate. Buss is particularly precise about this.

Okay, right, formalization. For the notation most useful to us, I'll use three sources:

**Source 1.** The course notes [A Hilbert Type Deductive System for Sentential Logic, Completeness and Compactness](https://www.columbia.edu/~hg17/ViewMathLogic/view1-deductive-system.pdf) (Gaifman 2002). These are wonderful, just 9pgs and cover
some results on satisfiability of the axioms of sentential (propositional) logic. Not at the level we can formalize
yet in these notes, I'm pretty sure. The definitions are very direct: inference rule, conclusion, and
premises. In Gaifman's notes, the inference rule of modus ponens is written as:

$$\frac{\alpha\to\beta,\;\alpha}{\beta}$$

Gaifman defines a Hilbert-type deductive system as follows. We won't follow it exactly, because we want to keep
"wff" out of our definition:

> A (Hilbert type) deductive system is a system consisting of a language and of (I) a set of
> wffs called axioms, and (II) a set of inference rules. An inference rule consists of (i) a list
> of wffs called the premises of the rule, (ii) a wff called the rule’s conclusion. 

**Source 2.** The book Practical Foundations for Programming Languages (Harper 2012). Chapter one defines and proves alpha-equivalence, which FYI is a concept that appears in the top of `peano.mm`. But chapter 2 defines
inference rules. Metamath's "typecode plus sequence of math symbols" is the analogue of a judgement
here, and a Metamath assertion (proof or axiom) would be called a rule. In Harper's terminology, "a collection of rules
forms an inductive definition of a judgement."
Inference rules with no premises are called axioms, else are called proper rules (we won't be adopting this
definition). For example, trees can be described by:

$$\begin{align*}\frac{}{\texttt{empty tree}} & &\frac{a_1\texttt{ tree}\quad a_2\texttt{ tree}}{\texttt{node}(a_1;a_2)\texttt{ tree}}\end{align*}$$

which I would translate to Metamath as:

```mm
$c tree ( ; ) node empty $. $v a1 a2 $.
ta1 $f tree a1 $. ta2 $f tree a2 $.
tempty $a tree empty $.
tpair $a tree node ( a1 ; a2 ) $.
```

**Source 3.** Sam Buss's 2023 book/notes [Introduction to Mathematical Logic](https://mathweb.ucsd.edu/~sbuss/IntroMathLogic/Fullbook_Draft.pdf) also uses similar notation. He defines a proof system for propositional logic called PL, using 
"the symbol $\vdash A$ to denote that $A$ has a propositional proof, $B_1,\ldots B_k\vdash A$ to denote that 
$A$ has a PL-proof from hypotheses $B_i.$" and "$\vDash$ for tautological validity/implication." Sam Buss's book
also has the wonderful footnote:

> Hilbert-style systems are named after David Hilbert, one of the founding fathers of mathematical logic, as this style of proof was used in D. Hilbert and W. Ackermann’s 1928 book
> Grundzüge der theoretischen Logik (Foundations of Mathematical Logic). A system similar
> to a Hilbert-style system was already used by A.N. Whitehead and B. Russell in 1910 in
> their classic Principia Mathematica. Even earlier, G. Frege used a precursor to Hilbert-style
> proof systems in his 1879 Begriffsschrift. All three of these were landmark developments in establishing
> the modern study of mathematical logic.

To repeat myself, Buss writes modus ponens as:

$$\frac{A\quad A\to B}{B}$$


Okay, there's a little worry that I have here. Going by Gaifman's notes, interpreted liberally,
we might call anything written in 
Metamath a Hilbert type system (or perhaps an extended Hilbert type system). But Megill is very careful to write
in [section 3.9.4](book/index.html#3.9.4-natural-deduction),
"The Metamath Proof Explorer (MPE) as defined in set.mm is fundamentally a Hilbert-style system," as opposed to
a broad statement that Metamath systems in general are Hilbert-style systems.

I hemmed and hawed about the phrasing of this for too long; it seems like "Hilbert-style" is something to split
hairs about. This is especially troublesome because all the logic texts I read--except for set.mm of course--
have the correctness of all of their definitions and terminology checked solely by the squishy lump of grey matter
sitting on top of mathematicians' shoulders. As such, from Gaifman's definition, even though I argue we can translate
one-to-one from the Hilbert style rules to `$a` and `$p` statements, we should sometimes take care not to say
"the logic we're representing is Hilbert-style" if it represents a vastly different logic. For example, if I make
a novel Metamath database using some kind of trick to represent type theoretic or sequent calculus constructions,
then the Metamath proof mechanism is still "Hilbert-style" but the garbage I'm representing and so too the database
and style of proof shouldn't be said to be "Hilbert-style."

### 4.0.2 Inference rules for us

For these notes, we'll write rules along with their typecode and label where possible.
Two examples from `set.mm` are modus ponens

$$\frac{\vdash \varphi\quad\vdash(\varphi\to \psi)}{\vdash \psi}
\quad\href{https://us.metamath.org/mpeuni/ax-mp.html}{\texttt{ax-mp},}$$

and hypothetical syllogism

$$\frac{\vdash(\psi\to \varphi)\quad\vdash(\varphi\to \chi)}{\vdash(\psi\to \chi)}
\quad\href{https://us.metamath.org/mpeuni/syl.html}{\texttt{syl}}.$$

While `ax-mp` is an axiom, `syl` is (in Harper's terminology) a derived rule, or in our 
terminology a theorem. It should be noted that
`ax-mp` also requires premises $\texttt{wff }\varphi$ and $\texttt{wff }\psi,$ but we omit them for
brevity.

An important convention for working in `set.mm` is that for practical purposes, a given theorem
may come in inference form, deduction form, and closed form. Modus ponens has deduction form
[`mpd`](https://us.metamath.org/mpeuni/mpd.html)

$$\frac{\vdash \varphi\to \psi\quad\vdash(\varphi\to (\psi\to \chi))}{\vdash (\varphi\to\chi)}\quad\texttt{mpd}$$

and closed form [`pm2.27`](https://us.metamath.org/mpeuni/pm2.27.html)

$$\frac{}{\vdash \varphi\to((\varphi\to\psi)\to\psi)}\quad\texttt{pm2.27}$$


## 4.1 Propositional calculus in `set.mm`

Let's start by building up some of the basic theorems and machinery of `set.mm`. We'll
pick apart and cannibalize the usual set proof database and build up our own as a series of interdependent exercises.
The problems are doable just using the metamath.exe proof assistant, but it's also a good opportunity
to learn Yamma or mmj2. I recommend reading bits of 
[the Metamath Proof Explorer](https://us.metamath.org/mpeuni/mmtheorems1.html), 
and the theorem documentation at `https://us.metamath.org/mpeuni/<label>.html`.

I also wrote a little cheatsheet at [TODO URL](), which you can use to keep a checklist or to 
remember different theorems we proved. The goal is to get the idea of how theorems are proved and
how they're used in different forms, certainly not to memorize or to become a total expert at 
propositional logic.  

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
- `match step n` (or `match all`) is super useful to list available unifications.
- `improve last /depth 1` attempts a more substantial proof search. Depth 2, 3, etc. quickly makes the search expensive.
- `search` does a textual search of the proof database (TODO, check, reference ch5) `/comments` 
- `show new_proof /unknown` or `/essential`
- `let variable $32 = "A = B"` assigns something mid-expression to the expression you want.
- `undo` and `redo`
- In order to allow pressing the up arrow, try installing `rlwrap` and launching `rlwrap metamath set.mm`

### 4.1.1 Implication: first proofs and useful derived rules

To start, here's some basic theorems: [`a1i`](https://us.metamath.org/mpeuni/a1i.html),
[`a2i`](https://us.metamath.org/mpeuni/a2i.html), [`mpd`](https://us.metamath.org/mpeuni/mpd.html),
[`syl`](https://us.metamath.org/mpeuni/syl.html), and [`id`](https://us.metamath.org/mpeuni/id.html).

Note that here we start seeing some of the conventions of set.mm, where the suffix
i generally stands for inference form, suffix d stands for deduction form, and no
suffix generally stands for closed form. This is discussed various places in the proof explorer
[such as here](https://us.metamath.org/mpeuni/mmnatded.html) and in the book [html page](book/index.html#3.9.3-deduction-style) or [pdf page](book/metamath.pdf#page=115). The proof explorer
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

Hints[^2].

[^2]: Unless otherwise stated, hints are given from the perspective of working back from the statement to be proved, so "use `ax-mp`" means "assign `ax-mp` to the statement."

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

These start to get a little more interesting. Note that "pm" stands for Principia Mathematica, so we're already 
working through The Book :)


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
stuck, use `match step n` to find the other theorem you have to use.
- `com12` basically yields to 1 theorem, so `match step` is your friend.
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

> [!NOTE]
> Here's where I started to hit a wall! Use the hints, ask questions, etc.
> This is a step up in difficulty from introductory logic class, and it's a specialized
> skillset that ... maybe we don't really want to become experts at. 

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

My answers:

```mm
con4i $p |- ( ps -> ph ) $=
  wph wn wps wn wi wps wph wi con4i.1 wph wps ax-3 ax-mp $.
con4d $p |- ( ph -> ( ch -> ps ) ) $=
  wph wps wn wch wn wi wch wps wi con4d.1 wps wch ax-3 syl $.
pm2.21i $p |- ( ph -> ps ) $=
  wps wph wph wn wps wn pm2.21i.1 a1i con4i $.
pm2.24ii $p |- ps $=
  wph wps pm2.24ii.1 wph wps pm2.24ii.2 pm2.21i ax-mp $.
pm2.21d $p |- ( ph -> ( ps -> ch ) ) $=
  wph wch wps wph wps wn wch wn pm2.21d.1 a1d con4d $.
pm2.21 $p |- ( -. ph -> ( ph -> ps ) ) $=
  wph wn wph wps wph wn id pm2.21d $.
pm2.24 $p |- ( ph -> ( -. ph -> ps ) ) $=
  wph wn wph wps wph wps pm2.21 com12 $.
pm2.18 $p |- ( ( -. ph -> ph ) -> ph ) $=
  wph wn wph wi wph wph wn wph wi wph wph wn wph wi wph wn wph wph wn wph wi wn
  wph wph wn wph wi wn pm2.21 a2i con4d pm2.43i $.
```

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
  For the remaining goal, don't be thrown off by `-. ps -> ps`, with our hypotheses this can be shown. Try `syl`.
- For `pm2.65i`, use `pm2.61i`, splitting on `ph`. One case is an identity;
  in the other, try `syl` with the two conflicting hypotheses, using contraposition on one.
- For `peirce`, use `pm2.61i`, splitting on `ph`. One case is an axiom instance;
  for the other, try `syl` with explosion as its first premise.

My answers. I found that it started to be fun again after I learned to use the 
various `con` theorems.

```mm
notnotr $p |- ( -. -. ph -> ph ) $=
  wph wn wn wph wn wph wi wph wph wn wph pm2.21 wph pm2.18 syl $.
notnot $p |- ( ph -> -. -. ph ) $=
  wph wn wn wph wph wn notnotr con4i $.
con2i $p |- ( ps -> -. ph ) $=
  wph wn wps wph wn wn wph wps wn wph notnotr con2i.a syl con4i $.
con1i $p |- ( -. ps -> ph ) $=
  wph wps wn wph wn wps wps wn wn con1i.1 wps notnot syl con4i $.
con3i $p |- ( -. ps -> -. ph ) $=
  wph wn wps wn wph wn wn wph wps wn wn wph notnotr wph wps wps wn wn con3i.a
  wps notnot syl syl con4i $.
mto $p |- -. ph $=
  wps wn wph wn mto.1 wph wps mto.2 con3i ax-mp $.
pm2.61i $p |- ps $=
  wps wn wps wi wps wps wn wph wn wps wph wps pm2.61i.1 con3i pm2.61i.2 syl
  wps pm2.18 ax-mp $.
pm2.65i $p |- -. ph $=
  wps wn wph wn wph wps pm2.65i.1 con3i wph wps wn pm2.65i.2 con3i pm2.61i $.
peirce $p |- ( ( ( ph -> ps ) -> ph ) -> ph ) $=
  wph wph wps wi wph wi wph wi wph wph wps wi wph wi ax-1 wph wn wph wps wi wph
  wps wi wph wi wph wi wph wps pm2.21 wph wps wi wph pm2.27 syl pm2.61i $.
```

### 4.1.6 The other connectives

From here, it's natural to introduce other connectives like `<->` for iff, `/\` for and, and
`\/` for or. I'm not going to do practice problems for this, it would be an exercise in tedium, 
but it's worthwhile to see the definitions using `df-*` notation.

The pages are quite good, especially [`df-bi`](https://us.metamath.org/mpeuni/df-bi.html) 
and [`wb`](https://us.metamath.org/mpeuni/wb.html)
which explains the reason
that we naturally want to pull in all of the machinery of these connectives:

> On the other hand, definitions are often useful
> to write shorter proofs, so in (i)set.mm we will generally not try to avoid
> them.  This is why, for instance, some theorems which do not contain
> disjunction in their statement are placed after the section on disjunction
> because a shorter proof using disjunction is possible.

The definitions are:

```metamath
df-bi $a |- -. ( ( ( ph <-> ps ) -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) )
              -> -. ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) -> ( ph <-> ps ) ) ) $.
df-an $a |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) $.
df-or $a |- ( ( ph \/ ps ) <-> ( -. ph -> ps ) ) $.
```

These are axiom `$a` statements, and Metamath doesn't check that these are honest definitions (which
should not allow us to prove any theorems we couldn't otherwise prove). cf.
[Appendix 4, A Note on Definitions](https://us.metamath.org/mpeuni/mmset.html#definitions).

Some of the more useful theorems are given here:

$$
\begin{array}{ccc}
\href{https://us.metamath.org/mpeuni/biimpi.html}{\texttt{biimpi}} &
\href{https://us.metamath.org/mpeuni/biimpri.html}{\texttt{biimpri}} &
\href{https://us.metamath.org/mpeuni/impbii.html}{\texttt{impbii}} \\[8pt]
\displaystyle \frac{\vdash (\varphi\leftrightarrow \psi)}{\vdash (\varphi\to\psi)} &
\displaystyle \frac{\vdash (\varphi\leftrightarrow \psi)}{\vdash (\psi \to\varphi)} &
\displaystyle \frac{\vdash (\varphi\to \psi) \quad \vdash (\psi\to\varphi)}{\vdash (\varphi\leftrightarrow\psi)}
\end{array}
$$

$$
\begin{array}{ccc}
\href{https://us.metamath.org/mpeuni/simpl.html}{\texttt{simpl}} &
\href{https://us.metamath.org/mpeuni/simpr.html}{\texttt{simpr}} &
\href{https://us.metamath.org/mpeuni/jca.html}{\texttt{jca}} \\[8pt]
\displaystyle \frac{}{\vdash((\varphi\land\psi)\to\varphi)} &
\displaystyle \frac{}{\vdash((\varphi\land\psi)\to\psi)} &
\displaystyle \frac{\vdash(\varphi\to\psi)\quad\vdash(\varphi\to\chi)}
                   {\vdash(\varphi\to(\psi\land\chi))}
\end{array}
$$

$$
\begin{array}{ccc}
\href{https://us.metamath.org/mpeuni/orc.html}{\texttt{orc}} &
\href{https://us.metamath.org/mpeuni/olc.html}{\texttt{olc}} &
\href{https://us.metamath.org/mpeuni/jaoi.html}{\texttt{jaoi}} \\[8pt]
\displaystyle \frac{}{\vdash(\varphi\to(\varphi\lor\psi))} &
\displaystyle \frac{}{\vdash(\varphi\to(\psi\lor\varphi))} &
\displaystyle \frac{\vdash(\varphi\to\psi)\quad\vdash(\chi\to\psi)}
                   {\vdash((\varphi\lor\chi)\to\psi)}
\end{array}
$$

One interesting thing this allows us to do is proof by cases. 

Suppose we have $\vdash ((\varphi\land\psi)\lor(\varphi\land\chi)),$
which we'll write as $D$ for short,
and we want to prove $\vdash \varphi.$ First, in steps 2 and 3 we 
show that each implication holds individually. Then, in step 4 
we combine the cases to show $\vdash D\to\varphi.$ And finally we use 
modus ponens to show $\vdash \varphi.$

$$
\begin{array}{rll}
1. & \vdash D & \text{given} \\[4pt]
2. & \vdash((\varphi\land\psi)\to\varphi) &
\texttt{simpl} \\[4pt]
3. & \vdash((\varphi\land\chi)\to\varphi) &
\texttt{simpl} \\[4pt]
4. & \vdash(D\to\varphi) &
\texttt{jaoi}\;2,3 \\[4pt]
5. & \vdash\varphi &
\texttt{ax-mp}\;1,4
\end{array}
$$

To remember the application of such theorems, we'll just rely on using a proof assistant (yamma, mmj2).

### 4.1.7 Notes and reflections on these exercises

#### Thought on proof transformations

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

Once we start proving things about inference, deduction, and closed forms, 
we're pretty naturally confronted with the idea of a metatheorem. 
With a bit more elbow grease, we know--in our heart of hearts--that an algorithm
relying on proof tables exists to determine all theorems like this. Or, we know
in our heart of hearts that we can take an essential hypothesis and discharge it 
to get the closed form of the theorem. 

The existence of a proof should clearly be called a metatheorem, since we would like to
eventually formalize it and it's a theorem about theorems. And we clearly do not yet
have the tools to formalize, 
"If we have a proof of propositional
logic statements of the form `${ foo.1 $e |- ch $. foo $p |- ps $= ? $. $}`
then we also have a proof of the form `$p |- ch -> ps $.`" I can live with that 
so long as we get to it later.

However, there's another way to think about this: If I wanted to reason about 
performing deductions, I might, instead of writing  `${ foo.1 $e |- ch $. foo $p |- ps $= ? $. $}`,
write `$p |- ch => ps $.`, which I endow with the intention of meaning "with chi as
an essential axiom, I deduce psi through Hilbert-style reasoning." And then, if I
build up enough axioms of my scheme that accurately captures things, I eventually might
wind up at `$p |- => ch -> ps $.`, meaning, "with no filled essential hypothesis in my
Hilbert-style scheme, chi implies psi." 

The deduction theorem is then something like 

`${ foo.1 $e |- ch => ps $. foo $p |- => ch -> ps $= ? $. $}`

But we're left with a philosophical issue: is my intention of what the `=>` symbol means
properly matched by the extra axioms I have to come up with?

And you have to understand where I'm coming from: the "non-mathematician's quest for truth" is 
troublesome because if you say, "study model theory" or whatnot, then fine, but we'll phrase 
model theory in terms of Metamath so we're really still in the weeds.

I used de Bruijn's criterion as a way to get out of ground 0 of these troublesome issues; do
we have to apply such a criterion again? Say `=>` is endowed with meaning by a description of Metamath we write
in Metamath. Then the simple, inspectability of the description of this Metamath interpreter is important,
and there remains a bit of philosophical faith in the veracity of our meta-theorem.

## 4.2 Other proof databases

### 4.2.1 `iset.mm` takeaways


The [intuitionistic database `iset.mm`](https://github.com/metamath/set.mm/blob/develop/iset.mm) 
develops theory with different axioms for defining negation
than in classical logic. These are
[`ax-in1`](https://us.metamath.org/ileuni/ax-in1.html) and
[`ax-in2`](https://us.metamath.org/ileuni/ax-in2.html):

```metamath
ax-in1 $a |- ( ( ph -> -. ph ) -> -. ph ) $.
ax-in2 $a |- ( -. ph -> ( ph -> ps ) ) $.
```

`ax-in1` looks a bit like the Clavius law 
$\vdash ((\neg\varphi\to\varphi)\to\varphi)$, with the nots switched around.
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

*Hints:*

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

The [higher-order logic database `hol.mm`](https://us.metamath.org/holuni/mmhol.html)
contains statements of the form, "under assumption $R,$ we have $S,$" written as the Metamath expression:
`|- R |= S`. 
If two expressions $R$ and $T$ gave rise to $S,$ then we'd write 
`|- ( R , T ) |= S`. 

It might seem like the $(R,T)$ syntax is a lot like conjunction, and `|=` is a lot like implication; but 
note that we don't introduce an axiom that lets us nest `|=` statements! So we quickly diverge from the
approach of `set.mm`. Instead if we want
our host of implication-like theorems, we use `==>`. 

Essential reading here is:

- Farmer 2008 (rev. 2019), [The Seven Virtues of Simple Type Theory](https://imps.mcmaster.ca/doc/seven-virtues.pdf). https://doi.org/10.1016/j.jal.2007.11.001
- A. Church 1940, A Formulation of the Simple Theory of Types. https://doi.org/10.2307/2266170

Here is enough of the language to try a first exercise, do `prove syl2anc` and `delete all`
if you're so inclined. Later in the database, modus ponens `mpd` comes up as a theorem, rather than
an axiom.

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
  syl2anc $p |- R |= A $=
    tr ts tt kct ta tr ts tt syl2anc.1 syl2anc.2 ax-jca syl2anc.3 ax-syl $.
$}
```


```metamath
$( ... in the full database $)
${
  mp.1 $e |- T : bool $.
  mp.2 $e |- R |= S $.
  mp.3 $e |- R |= [ S ==> T ] $.
  mpd $p |- R |= T $=
    tr ts tt ts tt tan kbr ts tt kct tr ts ts tt tan kbr tr mp.2 ts tt tim
    kbr ts tt tan kbr ts ke kbr tr mp.3 ts tt tim kbr ts tt tan kbr ts ke kbr
    ke kbr tr ts tr mp.2 ax-cb1 ts tt ts tr mp.2 ax-cb2 mp.1 imval a1i mpbi
    mpbir ts tt tan kbr ts tt kct ke kbr tr ts tr mp.2 ax-cb1 ts tt ts tr
    mp.2 ax-cb2 mp.1 dfan2 a1i mpbi simprd $.
$}
```

## Quiz Questions

### Question 1

In our terminology tailored for Metamath, we write modus ponens as follows:

$$\frac{\vdash \varphi\quad\vdash(\varphi\to \psi)}{\vdash \psi}\quad\texttt{ax-mp}$$

What is this notation called? How does it differ from the usual logician or computer scientist notation?

#### Answer

This is a notation for *inference rules.*

In Metamath, in `set.mm`, the symbol $\vdash$ (or as its written in .mm files `|-`) is a typecode,
and so the turnstile tells us what the typecodes of statements we unify with must be. 
There are also two implicit premises here: $\texttt{wff }\varphi$ and $\texttt{wff }\psi,$
which we must infer from the fact that $\varphi$ and $\psi$ are metavariables.

Whatever I write about the use of turnstile in other fields, after 20 attempts and citations,
still gets torn apart. So just just cf. [sequent calculus](https://en.wikipedia.org/wiki/Sequent#Rules) and
[type theory](https://en.wikipedia.org/wiki/Typing_rule), where we might write things like

$$\frac{\Gamma,\alpha\vdash\Sigma\quad\Gamma\vdash\alpha}{\Gamma\vdash\Sigma}$$

or 

$$\frac{\Gamma\vdash e:\tau\quad \tau\lt :\sigma}{\Gamma\vdash e:\sigma}$$

respectively, and know that in a machine-checked implementation $\vdash$ and other symbols
need not translate into actual string comparisons. Use notation and argue about it insofar as it's useful
to you.

### Question 2

What does it mean to say that a formal system is Hilbert-type? Is it ok to say "Metamath is Hilbert-type?"

#### Answer

From [Gaifman's 2002 student notes](https://www.columbia.edu/~hg17/ViewMathLogic/view1-deductive-system.pdf):

> A (Hilbert type) deductive system is a system consisting of a language and of (I) a set of
> wffs called axioms, and (II) a set of inference rules. An inference rule consists of (i) a list
> of wffs called the premises of the rule, (ii) a wff called the rule’s conclusion. 

This definition seems to be overly broad when applied in the context of Metamath, since
every Metamath assertion can be cast into the form of premises and conclusions, but we
**don't** colloquially say "Metamath is a Hilbert-type system." Rather we say that 
Metamath is Hilbert-inspired, while the logics that it represents in metamath databases
may or may not be Hilbert-type.

Note: It's unclear to me whether this is due to historical and social baggage around the term, 
or if a widely-accepted strict definition of "Hilbert-type" exists and simply requires much more 
metatheoretic machinery in order to write "$T$ is Hilbert-type" as a theorem inside a Metamath database.

### Question 3

What are modus ponens, modus tollens, and hypothetical syllogism?
Write them as inference rules.

#### Answer

Modus ponens:

$$\frac{\vdash\varphi\quad\vdash(\varphi\to\psi)}{\vdash\psi}
\quad\texttt{ax-mp}$$

Modus tollens:

$$\frac{\vdash\neg\psi\quad\vdash(\varphi\to\psi)}{\vdash\neg\varphi}
\quad\texttt{mto}$$

Hypothetical syllogism:

$$\frac{\vdash(\varphi\to\psi)\quad\vdash(\psi\to\chi)}
{\vdash(\varphi\to\chi)}\quad\texttt{syl}$$

In Metamath inside `set.mm`, `ax-mp` is an `$a` statement. `mto` and `syl` are `$p` statements.

### Question 4

What are the three axioms of propositional calculus used in
`set.mm`?

#### Answer

Jan Łukasiewicz' P2 is:

$$\begin{aligned}
\texttt{ax-1}:&\quad\vdash(\varphi\to(\psi\to\varphi))\\
\texttt{ax-2}:&\quad\vdash((\varphi\to(\psi\to\chi))\to
  ((\varphi\to\psi)\to(\varphi\to\chi)))\\
\texttt{ax-3}:&\quad\vdash((\neg\varphi\to\neg\psi)\to(\psi\to\varphi)).
\end{aligned}$$

cf. [Metamath book 3.2.1](book/index.html#3.2.1-propositional-calculus).

They can be remembered as:

- `ax-1` is simplification, or adding an unused assumption $\psi.$
- `ax-2` is traditionally called Frege's axiom. It says we can distribute a shared antecedent.
- `ax-3` is contraposition in closed form, though note the fact the $\neg$ 
is on the LHS is significant. $(\varphi\to\psi)\to(\neg\psi\to\neg\varphi)$ is valid
intuitionistically as well!

### Question 5

Metamath's `set.mm` has the convention of having 
inference, deduction, and closed forms of a theorem. 
Explain this convention and illustrate it using modus ponens.

#### Answer

An inference form has essential hypotheses:

$$\frac{\vdash\varphi\quad\vdash(\varphi\to\psi)}{\vdash\psi}
\quad\texttt{ax-mp}.$$

A deduction form carries a shared antecedent:

$$\frac{\vdash(\chi\to\varphi)\quad\vdash(\chi\to(\varphi\to\psi))}
{\vdash(\chi\to\psi)}\quad\texttt{mpd}.$$

A closed form has no essential hypotheses:

$$\vdash(\varphi\to((\varphi\to\psi)\to\psi))\quad\texttt{pm2.27}.$$

The suffixes `i` and `d` usually indicate inference and deduction forms, respectively. 
cf. [the roof explorer's discussion](https://us.metamath.org/mpeuni/mmnatded.html) of the three forms.

### Question 6

What does it mean to discharge a hypothesis?
How does Metamath's `set.mm` deal with not being able to easily discharge hypotheses?

#### Answer

Discharging a hypothesis means removing our dependence on it as an assumption.
For example, we can imagine discharging the hypotheses of `ax-mp` to get `pm2.27`:

$$
\begin{array}{cc}
\href{https://us.metamath.org/mpeuni/ax-mp.html}{\texttt{ax-mp}} &
\href{https://us.metamath.org/mpeuni/pm2.27.html}{\texttt{pm2.27}} \\[8pt]
\displaystyle \frac{\vdash\varphi\quad\vdash(\varphi\to\psi)}{\vdash\psi}
&
\displaystyle \frac{}{\vdash \varphi\to((\varphi\to\psi)\to\psi)}
\end{array}
$$

For propositional calculus, there exists an algorithm to convert a proof of the 
former into a proof of the latter, and this is a metatheorem known as the
deduction theorem, which takes much more machinery to tackle.

Normally, we avoid any application of the deduction theorem by directly applying 
theorems in inference, deduction, or closed form. 
Much later in `set.mm` there is machinery to apply a "weak deduction theorem." 
See [converting deductions to theorems](https://us.metamath.org/mpeuni/mmdeduction.html#convert).

### Question 7

Are there theorems (theorem schemes) in classical propositional logic,
which contain no negation, but are not true in intuitionistic logic? 
If so, give an example.

#### Answer


Peirce's law is an example of such a theorem. 

$$\vdash(((\varphi\to\psi)\to\varphi)\to\varphi).$$

It says that if $\varphi$ follows from assuming $\varphi\to\psi,$
then $\varphi$ holds, and it relies on the classical axiom for negation.
See [`peirce`](https://us.metamath.org/mpeuni/peirce.html). In general,
a formula doesn't need to contain negation to rely on negation axioms in its proof.

### Question 8

What is Clavius's law?

#### Answer


[Clavius's law](https://en.wikipedia.org/wiki/Consequentia_mirabilis) is

> If we ought to philosophise, then we ought to philosophise; and if we ought not to philosophise, then we ought to philosophise (i.e. in order to justify this view); in any case, therefore, we ought to philosophise.

This is usually written, in classical logic (theorem 2.18 of Principia Mathematica) as

$$\vdash((\neg\varphi\to\varphi)\to\varphi)
\quad\href{https://us.metamath.org/mpeuni/pm2.18.html}{\texttt{pm2.18}}.$$

There's an interesting and very similar statement in intuitionistic logic, which does not 
rely on reductio ad absurdum or the law of the excluded middle:

$$\vdash((\varphi\to\neg\varphi)\to\neg\varphi)
\quad\href{https://us.metamath.org/ileuni/ax-in1.html}{\texttt{ax-in1}}.$$

### Question 9

How does `set.mm` introduce conjunction, disjunction, and biconditional?

#### Answer

First we define axioms that say and, or, and biconditional are `wff`s with axioms 
[`wa`](https://us.metamath.org/mpeuni/wa.html),
[`wo`](https://us.metamath.org/mpeuni/wo.html),
[`wb`](https://us.metamath.org/mpeuni/wb.html). Then, we give the axioms
[`df-bi`](https://us.metamath.org/mpeuni/df-bi.html),
[`df-an`](https://us.metamath.org/mpeuni/df-an.html), and
[`df-or`](https://us.metamath.org/mpeuni/df-or.html), which determine how
these connectives expand into implication and negation:

```metamath
df-bi $a |- -. ( ( ( ph <-> ps ) -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) )
              -> -. ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) -> ( ph <-> ps ) ) ) $.
df-an $a |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) $.
df-or $a |- ( ( ph \/ ps ) <-> ( -. ph -> ps ) ) $.
```

In general, new definitions won't guarantee conservativity (that we cannot prove anything in the
new system that we couldn't in the old).
Establishing conservativity requires a separate argument,
See [Appendix 4, A Note on Definitions](https://us.metamath.org/mpeuni/mmset.html#definitions).

### Question 10

If you know a Metamath manipulation you want to make, but don't know the statement label,
what are some options for finding it in the various proof assistants?

#### Answer

In the Metamath proof assistant:

- You could use `match step n` to find assertions whose conclusions unify 
with a given step.
- If `match step n` gives you too many results, you could first substitute variables
with `let variable $32 = "( ph -> ps )"` before trying match again with your more
specific expression.
- You can use `search` to find expressions in the given metamath database.
- You can see if `improve all` fills in any blank steps.

Yamma: 

TODO

mmj2:

TODO

