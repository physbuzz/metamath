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
> These notes have a lot of AI-suggested problems in them that have not yet
> been reviewed. I put a warning at the start of each section that has not been human-reviewed.
> I tend to rewrite all the AI stuff I read.

@toc

# 4 Studying Propositional Calculus with Metamath

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

$$\frac{A\qquad A\to B}{B}$$


Okay, there's a little worry that I have here. Going by Gaifman's notes, interpreted liberally,
we might call anything written in 
Metamath a Hilbert type system (or perhaps an extended Hilbert type system). But Megill is very careful to write
in [section 3.9.4](https://www.mathandcode.com/books/metamath/book/metamath.html#3.9.4-natural-deduction),
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
Two examples from set.mm are
[`ax-mp`](https://us.metamath.org/mpeuni/ax-mp.html) and 

$$\frac{\vdash \varphi\quad\vdash(\varphi\to \psi)}{\vdash \psi}\quad\texttt{ax-mp}$$

and the more complicated [`syl`](https://us.metamath.org/mpeuni/syl.html)

$$\frac{\vdash(\psi\to \varphi)\qquad\vdash(\varphi\to \chi)}{\vdash(\psi\to \chi)}\quad\texttt{syl}.$$

While `ax-mp` is an axiom, `syl` is (in Harper's terminology) a derived rule, or in our 
terminology a theorem. It should be noted that
`ax-mp` also requires premises $\texttt{wff }\varphi$ and $\texttt{wff }\psi,$ but we omit them for
brevity.

An important convention for working in `set.mm` is that for practical purposes, a given theorem
may come in inference form, deduction form, and closed form. Modus ponens has deduction form
[`mpd`](https://us.metamath.org/mpeuni/mpd.html)

$$\frac{\vdash \varphi\to \psi\quad\vdash(\varphi\to (\psi\to \chi))}{\vdash (\psi\to\chi)}\quad\texttt{mpd}$$

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

> [!WARNING]
> I got stuck here at pm2.21 and decided I didn't want to make a cheat sheet of logic terms
> and get deep into the weeds. I might get back to it later as a way to practice proof assistants.
> It's very fun but just not somewhere I want to spend time developing expertise. 
>
> (So the hints and stuff, or that these are good problems, haven't been thoroughly checked!)


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

### 4.1.6 Supplied connectives for predicate calculus

> [!WARNING]
> This section was generated by AI and has not been human-reviewed. The reference proofs have been checked by Metamath.

Chapter 5 needs a few operations on equivalence, conjunction, and disjunction,
along with implication and negation rules. These are supplied tools; there are
no exercises in this section. The standalone files
`ai/predicate-calculus/predicate-reference.mm` and
`ai/predicate-calculus/predicate-exercises.mm` contain the complete prerequisite
chain. They leave `src/code-04/myset.mm` alone.

A syntax rule constructs a formula; a defining assertion relates that formula
to older connectives. The defining assertions below are `$a` statements.
Metamath checks consequences of those assertions, not whether a proposed
definition is sound. See the Proof Explorer's
[Appendix 4, A Note on Definitions](https://us.metamath.org/mpeuni/mmset.html#definitions).
In particular, `df-bi` uses only implication and negation to introduce the
biconditional. After its elementary rules have been derived, `df-an` and
`df-or` can use that biconditional in their definitions.

The interface used most often in chapter 5 is:

| Operation | Supplied rules |
| --- | --- |
| Extract or assemble an equivalence | `biimpi`, `biimpri`, `impbii` |
| Transport or compose equivalences | `notbii`, `bitri` |
| Extract or assemble a conjunction | `simpl`, `simpr`, `jca` |
| Move between conjunction and nested implication | `imp`, `ex` |
| Lift an implication through disjunction | `orim1i`, `orim2i` |
| Compose, contrapose, or change an antecedent | `syl`, `con3i`, `imim1i` |

The exact interfaces follow, including their prerequisites. A `$p` proof body
shown as `...` means **supplied**, not a blank to fill in. Its uncompressed
proof is in the reference file under the same label. Familiar rules from
4.1.1–4.1.5 are repeated in this ledger to make the starting file explicit;
do not paste duplicate declarations into an existing database. The `.h1`,
`.h2`, etc. labels name local essential hypotheses. All floating hypotheses
are declared once here and remain available in 5.1.

```metamath
$c ( ) -. -> /\ <-> \/ wff |- $.
$v ch et ph ps ta th $.
wph $f wff ph $.
wps $f wff ps $.
wch $f wff ch $.
wth $f wff th $.
wta $f wff ta $.
wet $f wff et $.
```

<details>
<summary>Supplied tools and their exact interfaces</summary>

```metamath
wb $a wff ( ph <-> ps ) $.

wi $a wff ( ph -> ps ) $.

wn $a wff -. ph $.

df-bi $a |- -. ( ( ( ph <-> ps ) -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) -> -. ( -. ( ( ph -> ps
  ) -> -. ( ps -> ph ) ) -> ( ph <-> ps ) ) ) $.

ax-1 $a |- ( ph -> ( ps -> ph ) ) $.

ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.

${
  ax-mp.h1 $e |- ph $.
  ax-mp.h2 $e |- ( ph -> ps ) $.
  ax-mp $a |- ps $.
$}

${
  a2i.h1 $e |- ( ph -> ( ps -> ch ) ) $.
  a2i $p |- ( ( ph -> ps ) -> ( ph -> ch ) ) $= ... $.
$}

${
  mpd.h1 $e |- ( ph -> ps ) $.
  mpd.h2 $e |- ( ph -> ( ps -> ch ) ) $.
  mpd $p |- ( ph -> ch ) $= ... $.
$}

id $p |- ( ph -> ph ) $= ... $.

${
  a1i.h1 $e |- ph $.
  a1i $p |- ( ps -> ph ) $= ... $.
$}

${
  syl.h1 $e |- ( ph -> ps ) $.
  syl.h2 $e |- ( ps -> ch ) $.
  syl $p |- ( ph -> ch ) $= ... $.
$}

${
  a1d.h1 $e |- ( ph -> ps ) $.
  a1d $p |- ( ph -> ( ch -> ps ) ) $= ... $.
$}

ax-3 $a |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $.

con4 $p |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $= ... $.

${
  con4d.h1 $e |- ( ph -> ( -. ps -> -. ch ) ) $.
  con4d $p |- ( ph -> ( ch -> ps ) ) $= ... $.
$}

${
  pm2.21d.h1 $e |- ( ph -> -. ps ) $.
  pm2.21d $p |- ( ph -> ( ps -> ch ) ) $= ... $.
$}

pm2.21 $p |- ( -. ph -> ( ph -> ps ) ) $= ... $.

${
  sylcom.h1 $e |- ( ph -> ( ps -> ch ) ) $.
  sylcom.h2 $e |- ( ps -> ( ch -> th ) ) $.
  sylcom $p |- ( ph -> ( ps -> th ) ) $= ... $.
$}

${
  mt4d.h1 $e |- ( ph -> ps ) $.
  mt4d.h2 $e |- ( ph -> ( -. ch -> -. ps ) ) $.
  mt4d $p |- ( ph -> ch ) $= ... $.
$}

${
  pm2.18d.h1 $e |- ( ph -> ( -. ps -> ps ) ) $.
  pm2.18d $p |- ( ph -> ps ) $= ... $.
$}

pm2.18 $p |- ( ( -. ph -> ph ) -> ph ) $= ... $.

${
  jarli.h1 $e |- ( ( ph -> ps ) -> ch ) $.
  jarli $p |- ( -. ph -> ch ) $= ... $.
$}

notnotr $p |- ( -. -. ph -> ph ) $= ... $.

${
  syl5com.h1 $e |- ( ph -> ps ) $.
  syl5com.h2 $e |- ( ch -> ( ps -> th ) ) $.
  syl5com $p |- ( ph -> ( ch -> th ) ) $= ... $.
$}

${
  com12.h1 $e |- ( ph -> ( ps -> ch ) ) $.
  com12 $p |- ( ps -> ( ph -> ch ) ) $= ... $.
$}

${
  syl5.h1 $e |- ( ph -> ps ) $.
  syl5.h2 $e |- ( ch -> ( ps -> th ) ) $.
  syl5 $p |- ( ch -> ( ph -> th ) ) $= ... $.
$}

${
  con2d.h1 $e |- ( ph -> ( ps -> -. ch ) ) $.
  con2d $p |- ( ph -> ( ch -> -. ps ) ) $= ... $.
$}

${
  mt2d.h1 $e |- ( ph -> ch ) $.
  mt2d.h2 $e |- ( ph -> ( ps -> -. ch ) ) $.
  mt2d $p |- ( ph -> -. ps ) $= ... $.
$}

${
  nsyl3.h1 $e |- ( ph -> -. ps ) $.
  nsyl3.h2 $e |- ( ch -> ps ) $.
  nsyl3 $p |- ( ch -> -. ph ) $= ... $.
$}

${
  con4i.h1 $e |- ( -. ph -> -. ps ) $.
  con4i $p |- ( ps -> ph ) $= ... $.
$}

${
  nsyl2.h1 $e |- ( ph -> -. ps ) $.
  nsyl2.h2 $e |- ( -. ch -> ps ) $.
  nsyl2 $p |- ( ph -> ch ) $= ... $.
$}

${
  con1i.h1 $e |- ( -. ph -> ps ) $.
  con1i $p |- ( -. ps -> ph ) $= ... $.
$}

simplim $p |- ( -. ( ph -> ps ) -> ph ) $= ... $.

biimp $p |- ( ( ph <-> ps ) -> ( ph -> ps ) ) $= ... $.

${
  biimpi.h1 $e |- ( ph <-> ps ) $.
  biimpi $p |- ( ph -> ps ) $= ... $.
$}

idd $p |- ( ph -> ( ps -> ps ) ) $= ... $.

${
  con2i.h1 $e |- ( ph -> -. ps ) $.
  con2i $p |- ( ps -> -. ph ) $= ... $.
$}

notnot $p |- ( ph -> -. -. ph ) $= ... $.

${
  syl6.h1 $e |- ( ph -> ( ps -> ch ) ) $.
  syl6.h2 $e |- ( ch -> th ) $.
  syl6 $p |- ( ph -> ( ps -> th ) ) $= ... $.
$}

${
  con1d.h1 $e |- ( ph -> ( -. ps -> ch ) ) $.
  con1d $p |- ( ph -> ( -. ch -> ps ) ) $= ... $.
$}

${
  con3d.h1 $e |- ( ph -> ( ps -> ch ) ) $.
  con3d $p |- ( ph -> ( -. ch -> -. ps ) ) $= ... $.
$}

${
  con3rr3.h1 $e |- ( ph -> ( ps -> ch ) ) $.
  con3rr3 $p |- ( -. ch -> ( ph -> -. ps ) ) $= ... $.
$}

${
  impi.h1 $e |- ( ph -> ( ps -> ch ) ) $.
  impi $p |- ( -. ( ph -> -. ps ) -> ch ) $= ... $.
$}

simprim $p |- ( -. ( ph -> -. ps ) -> ps ) $= ... $.

pm2.27 $p |- ( ph -> ( ( ph -> ps ) -> ps ) ) $= ... $.

pm3.2im $p |- ( ph -> ( ps -> -. ( ph -> -. ps ) ) ) $= ... $.

${
  expi.h1 $e |- ( -. ( ph -> -. ps ) -> ch ) $.
  expi $p |- ( ph -> ( ps -> ch ) ) $= ... $.
$}

impbi $p |- ( ( ph -> ps ) -> ( ( ps -> ph ) -> ( ph <-> ps ) ) ) $= ... $.

${
  imim2i.h1 $e |- ( ph -> ps ) $.
  imim2i $p |- ( ( ch -> ph ) -> ( ch -> ps ) ) $= ... $.
$}

${
  a2d.h1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
  a2d $p |- ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) ) $= ... $.
$}

${
  mpdd.h1 $e |- ( ph -> ( ps -> ch ) ) $.
  mpdd.h2 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
  mpdd $p |- ( ph -> ( ps -> th ) ) $= ... $.
$}

${
  syld.h1 $e |- ( ph -> ( ps -> ch ) ) $.
  syld.h2 $e |- ( ph -> ( ch -> th ) ) $.
  syld $p |- ( ph -> ( ps -> th ) ) $= ... $.
$}

${
  pm2.61d.h1 $e |- ( ph -> ( ps -> ch ) ) $.
  pm2.61d.h2 $e |- ( ph -> ( -. ps -> ch ) ) $.
  pm2.61d $p |- ( ph -> ch ) $= ... $.
$}

${
  pm2.61d1.h1 $e |- ( ph -> ( ps -> ch ) ) $.
  pm2.61d1.h2 $e |- ( -. ps -> ch ) $.
  pm2.61d1 $p |- ( ph -> ch ) $= ... $.
$}

${
  ja.h1 $e |- ( -. ph -> ch ) $.
  ja.h2 $e |- ( ps -> ch ) $.
  ja $p |- ( ( ph -> ps ) -> ch ) $= ... $.
$}

pm2.01 $p |- ( ( ph -> -. ph ) -> -. ph ) $= ... $.

${
  pm2.01i.h1 $e |- ( ph -> -. ph ) $.
  pm2.01i $p |- -. ph $= ... $.
$}

${
  pm2.65i.h1 $e |- ( ph -> ps ) $.
  pm2.65i.h2 $e |- ( ph -> -. ps ) $.
  pm2.65i $p |- -. ph $= ... $.
$}

${
  mto.h1 $e |- -. ps $.
  mto.h2 $e |- ( ph -> ps ) $.
  mto $p |- -. ph $= ... $.
$}

${
  pm2.21i.h1 $e |- -. ph $.
  pm2.21i $p |- ( ph -> ps ) $= ... $.
$}

${
  mt4.h1 $e |- ph $.
  mt4.h2 $e |- ( -. ps -> -. ph ) $.
  mt4 $p |- ps $= ... $.
$}

${
  notnotri.h1 $e |- -. -. ph $.
  notnotri $p |- ph $= ... $.
$}

${
  mt3.h1 $e |- -. ps $.
  mt3.h2 $e |- ( -. ph -> ps ) $.
  mt3 $p |- ph $= ... $.
$}

dfbi1 $p |- ( ( ph <-> ps ) <-> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) $= ... $.

${
  sylbi.h1 $e |- ( ph <-> ps ) $.
  sylbi.h2 $e |- ( ps -> ch ) $.
  sylbi $p |- ( ph -> ch ) $= ... $.
$}

biimpr $p |- ( ( ph <-> ps ) -> ( ps -> ph ) ) $= ... $.

${
  syl2im.h1 $e |- ( ph -> ps ) $.
  syl2im.h2 $e |- ( ch -> th ) $.
  syl2im.h3 $e |- ( ps -> ( th -> ta ) ) $.
  syl2im $p |- ( ph -> ( ch -> ta ) ) $= ... $.
$}

${
  syl2imc.h1 $e |- ( ph -> ps ) $.
  syl2imc.h2 $e |- ( ch -> th ) $.
  syl2imc.h3 $e |- ( ps -> ( th -> ta ) ) $.
  syl2imc $p |- ( ch -> ( ph -> ta ) ) $= ... $.
$}

${
  impbid21d.h1 $e |- ( ps -> ( ch -> th ) ) $.
  impbid21d.h2 $e |- ( ph -> ( th -> ch ) ) $.
  impbid21d $p |- ( ph -> ( ps -> ( ch <-> th ) ) ) $= ... $.
$}

${
  pm2.43i.h1 $e |- ( ph -> ( ph -> ps ) ) $.
  pm2.43i $p |- ( ph -> ps ) $= ... $.
$}

${
  impbid.h1 $e |- ( ph -> ( ps -> ch ) ) $.
  impbid.h2 $e |- ( ph -> ( ch -> ps ) ) $.
  impbid $p |- ( ph -> ( ps <-> ch ) ) $= ... $.
$}

bicom1 $p |- ( ( ph <-> ps ) -> ( ps <-> ph ) ) $= ... $.

${
  bicomi.h1 $e |- ( ph <-> ps ) $.
  bicomi $p |- ( ps <-> ph ) $= ... $.
$}

${
  biimpri.h1 $e |- ( ph <-> ps ) $.
  biimpri $p |- ( ps -> ph ) $= ... $.
$}

${
  mp2.h1 $e |- ph $.
  mp2.h2 $e |- ps $.
  mp2.h3 $e |- ( ph -> ( ps -> ch ) ) $.
  mp2 $p |- ch $= ... $.
$}

${
  impbii.h1 $e |- ( ph -> ps ) $.
  impbii.h2 $e |- ( ps -> ph ) $.
  impbii $p |- ( ph <-> ps ) $= ... $.
$}

notnotb $p |- ( ph <-> -. -. ph ) $= ... $.

${
  imim3i.h1 $e |- ( ph -> ( ps -> ch ) ) $.
  imim3i $p |- ( ( th -> ph ) -> ( ( th -> ps ) -> ( th -> ch ) ) ) $= ... $.
$}

${
  imim2d.h1 $e |- ( ph -> ( ps -> ch ) ) $.
  imim2d $p |- ( ph -> ( ( th -> ps ) -> ( th -> ch ) ) ) $= ... $.
$}

imim2 $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $= ... $.

${
  syl6c.h1 $e |- ( ph -> ( ps -> ch ) ) $.
  syl6c.h2 $e |- ( ph -> ( ps -> th ) ) $.
  syl6c.h3 $e |- ( ch -> ( th -> ta ) ) $.
  syl6c $p |- ( ph -> ( ps -> ta ) ) $= ... $.
$}

${
  syldd.h1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
  syldd.h2 $e |- ( ph -> ( ps -> ( th -> ta ) ) ) $.
  syldd $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $= ... $.
$}

${
  syl5d.h1 $e |- ( ph -> ( ps -> ch ) ) $.
  syl5d.h2 $e |- ( ph -> ( th -> ( ch -> ta ) ) ) $.
  syl5d $p |- ( ph -> ( th -> ( ps -> ta ) ) ) $= ... $.
$}

${
  syl9.h1 $e |- ( ph -> ( ps -> ch ) ) $.
  syl9.h2 $e |- ( th -> ( ch -> ta ) ) $.
  syl9 $p |- ( ph -> ( th -> ( ps -> ta ) ) ) $= ... $.
$}

${
  com23.h1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
  com23 $p |- ( ph -> ( ch -> ( ps -> th ) ) ) $= ... $.
$}

${
  pm2.86d.h1 $e |- ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) ) $.
  pm2.86d $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $= ... $.
$}

${
  impbidd.h1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
  impbidd.h2 $e |- ( ph -> ( ps -> ( th -> ch ) ) ) $.
  impbidd $p |- ( ph -> ( ps -> ( ch <-> th ) ) ) $= ... $.
$}

pm5.74 $p |- ( ( ph -> ( ps <-> ch ) ) <-> ( ( ph -> ps ) <-> ( ph -> ch ) ) ) $= ... $.

${
  mpbi.h1 $e |- ph $.
  mpbi.h2 $e |- ( ph <-> ps ) $.
  mpbi $p |- ps $= ... $.
$}

${
  pm5.74i.h1 $e |- ( ph -> ( ps <-> ch ) ) $.
  pm5.74i $p |- ( ( ph -> ps ) <-> ( ph -> ch ) ) $= ... $.
$}

${
  sylbb.h1 $e |- ( ph <-> ps ) $.
  sylbb.h2 $e |- ( ps <-> ch ) $.
  sylbb $p |- ( ph -> ch ) $= ... $.
$}

${
  sylibr.h1 $e |- ( ph -> ps ) $.
  sylibr.h2 $e |- ( ch <-> ps ) $.
  sylibr $p |- ( ph -> ch ) $= ... $.
$}

${
  sylbbr.h1 $e |- ( ph <-> ps ) $.
  sylbbr.h2 $e |- ( ps <-> ch ) $.
  sylbbr $p |- ( ch -> ph ) $= ... $.
$}

${
  bitri.h1 $e |- ( ph <-> ps ) $.
  bitri.h2 $e |- ( ps <-> ch ) $.
  bitri $p |- ( ph <-> ch ) $= ... $.
$}

${
  mpbir.h1 $e |- ps $.
  mpbir.h2 $e |- ( ph <-> ps ) $.
  mpbir $p |- ph $= ... $.
$}

${
  pm5.74ri.h1 $e |- ( ( ph -> ps ) <-> ( ph -> ch ) ) $.
  pm5.74ri $p |- ( ph -> ( ps <-> ch ) ) $= ... $.
$}

${
  bitrd.h1 $e |- ( ph -> ( ps <-> ch ) ) $.
  bitrd.h2 $e |- ( ph -> ( ch <-> th ) ) $.
  bitrd $p |- ( ph -> ( ps <-> th ) ) $= ... $.
$}

${
  bitrid.h1 $e |- ( ph <-> ps ) $.
  bitrid.h2 $e |- ( ch -> ( ps <-> th ) ) $.
  bitrid $p |- ( ch -> ( ph <-> th ) ) $= ... $.
$}

${
  bitr3id.h1 $e |- ( ps <-> ph ) $.
  bitr3id.h2 $e |- ( ch -> ( ps <-> th ) ) $.
  bitr3id $p |- ( ch -> ( ph <-> th ) ) $= ... $.
$}

${
  bitrdi.h1 $e |- ( ph -> ( ps <-> ch ) ) $.
  bitrdi.h2 $e |- ( ch <-> th ) $.
  bitrdi $p |- ( ph -> ( ps <-> th ) ) $= ... $.
$}

${
  3bitr3g.h1 $e |- ( ph -> ( ps <-> ch ) ) $.
  3bitr3g.h2 $e |- ( ps <-> th ) $.
  3bitr3g.h3 $e |- ( ch <-> ta ) $.
  3bitr3g $p |- ( ph -> ( th <-> ta ) ) $= ... $.
$}

bicom $p |- ( ( ph <-> ps ) <-> ( ps <-> ph ) ) $= ... $.

${
  sylib.h1 $e |- ( ph -> ps ) $.
  sylib.h2 $e |- ( ps <-> ch ) $.
  sylib $p |- ( ph -> ch ) $= ... $.
$}

${
  bicomd.h1 $e |- ( ph -> ( ps <-> ch ) ) $.
  bicomd $p |- ( ph -> ( ch <-> ps ) ) $= ... $.
$}

${
  biimpd.h1 $e |- ( ph -> ( ps <-> ch ) ) $.
  biimpd $p |- ( ph -> ( ps -> ch ) ) $= ... $.
$}

${
  imbitrid.h1 $e |- ( ph -> ps ) $.
  imbitrid.h2 $e |- ( ch -> ( ps <-> th ) ) $.
  imbitrid $p |- ( ch -> ( ph -> th ) ) $= ... $.
$}

${
  imbitrrid.h1 $e |- ( ph -> th ) $.
  imbitrrid.h2 $e |- ( ch -> ( ps <-> th ) ) $.
  imbitrrid $p |- ( ch -> ( ph -> ps ) ) $= ... $.
$}

${
  biimprd.h1 $e |- ( ph -> ( ps <-> ch ) ) $.
  biimprd $p |- ( ph -> ( ch -> ps ) ) $= ... $.
$}

${
  impcon4bid.h1 $e |- ( ph -> ( ps -> ch ) ) $.
  impcon4bid.h2 $e |- ( ph -> ( -. ps -> -. ch ) ) $.
  impcon4bid $p |- ( ph -> ( ps <-> ch ) ) $= ... $.
$}

${
  con4bid.h1 $e |- ( ph -> ( -. ps <-> -. ch ) ) $.
  con4bid $p |- ( ph -> ( ps <-> ch ) ) $= ... $.
$}

${
  notbid.h1 $e |- ( ph -> ( ps <-> ch ) ) $.
  notbid $p |- ( ph -> ( -. ps <-> -. ch ) ) $= ... $.
$}

notbi $p |- ( ( ph <-> ps ) <-> ( -. ph <-> -. ps ) ) $= ... $.

${
  notbii.h1 $e |- ( ph <-> ps ) $.
  notbii $p |- ( -. ph <-> -. ps ) $= ... $.
$}

${
  xchbinx.h1 $e |- ( ph <-> -. ps ) $.
  xchbinx.h2 $e |- ( ps <-> ch ) $.
  xchbinx $p |- ( ph <-> -. ch ) $= ... $.
$}

${
  xchbinxr.h1 $e |- ( ph <-> -. ps ) $.
  xchbinxr.h2 $e |- ( ch <-> ps ) $.
  xchbinxr $p |- ( ph <-> -. ch ) $= ... $.
$}

${
  con2bii.h1 $e |- ( ph <-> -. ps ) $.
  con2bii $p |- ( ps <-> -. ph ) $= ... $.
$}

${
  biimtrrid.h1 $e |- ( ps <-> ph ) $.
  biimtrrid.h2 $e |- ( ch -> ( ps -> th ) ) $.
  biimtrrid $p |- ( ch -> ( ph -> th ) ) $= ... $.
$}

${
  imbitrdi.h1 $e |- ( ph -> ( ps -> ch ) ) $.
  imbitrdi.h2 $e |- ( ch <-> th ) $.
  imbitrdi $p |- ( ph -> ( ps -> th ) ) $= ... $.
$}

${
  3imtr3g.h1 $e |- ( ph -> ( ps -> ch ) ) $.
  3imtr3g.h2 $e |- ( ps <-> th ) $.
  3imtr3g.h3 $e |- ( ch <-> ta ) $.
  3imtr3g $p |- ( ph -> ( th -> ta ) ) $= ... $.
$}

${
  nsyl.h1 $e |- ( ph -> -. ps ) $.
  nsyl.h2 $e |- ( ch -> ps ) $.
  nsyl $p |- ( ph -> -. ch ) $= ... $.
$}

${
  con3i.h1 $e |- ( ph -> ps ) $.
  con3i $p |- ( -. ps -> -. ph ) $= ... $.
$}

wa $a wff ( ph /\ ps ) $.

df-an $a |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) $.

${
  imp.h1 $e |- ( ph -> ( ps -> ch ) ) $.
  imp $p |- ( ( ph /\ ps ) -> ch ) $= ... $.
$}

${
  adantr.h1 $e |- ( ph -> ps ) $.
  adantr $p |- ( ( ph /\ ch ) -> ps ) $= ... $.
$}

simpl $p |- ( ( ph /\ ps ) -> ph ) $= ... $.

${
  sylbir.h1 $e |- ( ps <-> ph ) $.
  sylbir.h2 $e |- ( ps -> ch ) $.
  sylbir $p |- ( ph -> ch ) $= ... $.
$}

${
  ex.h1 $e |- ( ( ph /\ ps ) -> ch ) $.
  ex $p |- ( ph -> ( ps -> ch ) ) $= ... $.
$}

${
  expcom.h1 $e |- ( ( ph /\ ps ) -> ch ) $.
  expcom $p |- ( ps -> ( ph -> ch ) ) $= ... $.
$}

${
  ancoms.h1 $e |- ( ( ph /\ ps ) -> ch ) $.
  ancoms $p |- ( ( ps /\ ph ) -> ch ) $= ... $.
$}

${
  adantl.h1 $e |- ( ph -> ps ) $.
  adantl $p |- ( ( ch /\ ph ) -> ps ) $= ... $.
$}

simpr $p |- ( ( ph /\ ps ) -> ps ) $= ... $.

pm3.2 $p |- ( ph -> ( ps -> ( ph /\ ps ) ) ) $= ... $.

${
  sylc.h1 $e |- ( ph -> ps ) $.
  sylc.h2 $e |- ( ph -> ch ) $.
  sylc.h3 $e |- ( ps -> ( ch -> th ) ) $.
  sylc $p |- ( ph -> th ) $= ... $.
$}

${
  jca.h1 $e |- ( ph -> ps ) $.
  jca.h2 $e |- ( ph -> ch ) $.
  jca $p |- ( ph -> ( ps /\ ch ) ) $= ... $.
$}

${
  imim12d.h1 $e |- ( ph -> ( ps -> ch ) ) $.
  imim12d.h2 $e |- ( ph -> ( th -> ta ) ) $.
  imim12d $p |- ( ph -> ( ( ch -> th ) -> ( ps -> ta ) ) ) $= ... $.
$}

${
  imim1d.h1 $e |- ( ph -> ( ps -> ch ) ) $.
  imim1d $p |- ( ph -> ( ( ch -> th ) -> ( ps -> th ) ) ) $= ... $.
$}

${
  imbi1d.h1 $e |- ( ph -> ( ps <-> ch ) ) $.
  imbi1d $p |- ( ph -> ( ( ps -> th ) <-> ( ch -> th ) ) ) $= ... $.
$}

imbi1 $p |- ( ( ph <-> ps ) -> ( ( ph -> ch ) <-> ( ps -> ch ) ) ) $= ... $.

${
  imbi1i.h1 $e |- ( ph <-> ps ) $.
  imbi1i $p |- ( ( ph -> ch ) <-> ( ps -> ch ) ) $= ... $.
$}

con1 $p |- ( ( -. ph -> ps ) -> ( -. ps -> ph ) ) $= ... $.

con1b $p |- ( ( -. ph -> ps ) <-> ( -. ps -> ph ) ) $= ... $.

${
  imim12i.h1 $e |- ( ph -> ps ) $.
  imim12i.h2 $e |- ( ch -> th ) $.
  imim12i $p |- ( ( ps -> ch ) -> ( ph -> th ) ) $= ... $.
$}

${
  imim1i.h1 $e |- ( ph -> ps ) $.
  imim1i $p |- ( ( ps -> ch ) -> ( ph -> ch ) ) $= ... $.
$}

${
  expdcom.h1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
  expdcom $p |- ( ps -> ( ch -> ( ph -> th ) ) ) $= ... $.
$}

${
  com3r.h1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
  com3r $p |- ( ch -> ( ph -> ( ps -> th ) ) ) $= ... $.
$}

${
  expd.h1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
  expd $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $= ... $.
$}

${
  expcomd.h1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
  expcomd $p |- ( ph -> ( ch -> ( ps -> th ) ) ) $= ... $.
$}

${
  com3l.h1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
  com3l $p |- ( ps -> ( ch -> ( ph -> th ) ) ) $= ... $.
$}

${
  impd.h1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
  impd $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $= ... $.
$}

${
  ancomsd.h1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
  ancomsd $p |- ( ph -> ( ( ch /\ ps ) -> th ) ) $= ... $.
$}

${
  syland.h1 $e |- ( ph -> ( ps -> ch ) ) $.
  syland.h2 $e |- ( ph -> ( ( ch /\ th ) -> ta ) ) $.
  syland $p |- ( ph -> ( ( ps /\ th ) -> ta ) ) $= ... $.
$}

${
  sylan2d.h1 $e |- ( ph -> ( ps -> ch ) ) $.
  sylan2d.h2 $e |- ( ph -> ( ( th /\ ch ) -> ta ) ) $.
  sylan2d $p |- ( ph -> ( ( th /\ ps ) -> ta ) ) $= ... $.
$}

${
  syl2and.h1 $e |- ( ph -> ( ps -> ch ) ) $.
  syl2and.h2 $e |- ( ph -> ( th -> ta ) ) $.
  syl2and.h3 $e |- ( ph -> ( ( ch /\ ta ) -> et ) ) $.
  syl2and $p |- ( ph -> ( ( ps /\ th ) -> et ) ) $= ... $.
$}

${
  mpi.h1 $e |- ps $.
  mpi.h2 $e |- ( ph -> ( ps -> ch ) ) $.
  mpi $p |- ( ph -> ch ) $= ... $.
$}

wo $a wff ( ph \/ ps ) $.

pm2.24 $p |- ( ph -> ( -. ph -> ps ) ) $= ... $.

df-or $a |- ( ( ph \/ ps ) <-> ( -. ph -> ps ) ) $.

pm2.54 $p |- ( ( -. ph -> ps ) -> ( ph \/ ps ) ) $= ... $.

${
  orrd.h1 $e |- ( ph -> ( -. ps -> ch ) ) $.
  orrd $p |- ( ph -> ( ps \/ ch ) ) $= ... $.
$}

orc $p |- ( ph -> ( ph \/ ps ) ) $= ... $.

${
  orcd.h1 $e |- ( ph -> ps ) $.
  orcd $p |- ( ph -> ( ps \/ ch ) ) $= ... $.
$}

olc $p |- ( ph -> ( ps \/ ph ) ) $= ... $.

pm2.53 $p |- ( ( ph \/ ps ) -> ( -. ph -> ps ) ) $= ... $.

${
  pm2.61d2.h1 $e |- ( ph -> ( -. ps -> ch ) ) $.
  pm2.61d2.h2 $e |- ( ps -> ch ) $.
  pm2.61d2 $p |- ( ph -> ch ) $= ... $.
$}

${
  jaoi.h1 $e |- ( ph -> ps ) $.
  jaoi.h2 $e |- ( ch -> ps ) $.
  jaoi $p |- ( ( ph \/ ch ) -> ps ) $= ... $.
$}

pm1.4 $p |- ( ( ph \/ ps ) -> ( ps \/ ph ) ) $= ... $.

orcom $p |- ( ( ph \/ ps ) <-> ( ps \/ ph ) ) $= ... $.

${
  orcomd.h1 $e |- ( ph -> ( ps \/ ch ) ) $.
  orcomd $p |- ( ph -> ( ch \/ ps ) ) $= ... $.
$}

${
  olcd.h1 $e |- ( ph -> ps ) $.
  olcd $p |- ( ph -> ( ch \/ ps ) ) $= ... $.
$}

${
  orim12i.h1 $e |- ( ph -> ps ) $.
  orim12i.h2 $e |- ( ch -> th ) $.
  orim12i $p |- ( ( ph \/ ch ) -> ( ps \/ th ) ) $= ... $.
$}

${
  orim1i.h1 $e |- ( ph -> ps ) $.
  orim1i $p |- ( ( ph \/ ch ) -> ( ps \/ ch ) ) $= ... $.
$}

${
  orim2i.h1 $e |- ( ph -> ps ) $.
  orim2i $p |- ( ( ch \/ ph ) -> ( ch \/ ps ) ) $= ... $.
$}
```

</details>

For example, `impbii` consumes the two directed implications; `biimpi` and
`biimpri` recover them. `jca` consumes two consequences of the same antecedent.
These are derived rules, not extra logical axioms. In the reference file,
`biimp` starts from `df-bi` and the classical negation rules; `impbi` builds
its converse; `impbii` packages both directions. The conjunction rules pass
through `df-an`, while the disjunction rules pass through `df-or` and
contraposition. Their intermediate interfaces are included above so each
proof can be traced back to the three propositional axioms and modus ponens.

To inspect a supplied proof from the repository root:

```sh
metamath 'read "ai/predicate-calculus/predicate-reference.mm"' \
  'show proof impbii /lemmon' exit
make -C ai/predicate-calculus verify
```

### 4.1.7 Carew Meredith's sole axiom for propositional calculus

> [!WARNING]
> This section was generated by AI and hasn't been reviewed yet.

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

#### A first lemma

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

#### Recovering three familiar statements

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

### 4.1.8 Notes and reflections and TODO on these exercises.


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

> [!WARNING]
> I haven't touched this section at all.

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




