---
title: "Metamath Study Notes"
---

Hosted on [mathandcode.com/books/metamath](https://www.mathandcode.com/books/metamath/).
See also: [local version of the metamath book](book/index.html), 
[pdf metamath book on metamath.org](https://us.metamath.org/downloads/metamath.pdf).

# Metamath Study Notes

Independently studying Metamath and its applications while staunchly saying
"if I have to verify it in my head and not in a computer program then it's not math."



I mean seriously, you can't teach me about primitive symbols and then say "oh yeah but these
represent different things so they're totally different." You just taught me to divorce
the symbols from words, then staple words back on! But I'm getting ahead of myself.

## Contents

- [0. Rant about Mathematical Proof](00-rant.html)
- [1. Working through a Metamath Proof by Hand (Megill ch2)](01-megillch2.html)
- [2. Bonus Chapter: Connection with Logic Programming (cf. SICP 4.4)](02-sicp-logic.html)
- [3. Writing a Metamath Interpreter](03-interpreter.html)
- [4. Studying Propositional Calculus with Metamath](04-propmm.html)
- [5. Variables, Binding, and Predicate Calculus](05-predicate-calculus.html)
- [5.5 Bonus chapter: Deigning to write proofs in English (Harper ch1-3)](05-5-practical-foundations.html)

## Intro

This project started from reading through Norm Megill's [public domain Metamath book](https://us.metamath.org/downloads/metamath.pdf), but grew into its own
study project.
My goals are:

1. Build up to making formally verified metamathematical statements, inside Metamath. At the outset, 
it's very difficult to determine how ambitious to be. The best path to this appears to be doing this
through `set.mm`, from which we use set theory tools to make metamathematical statements.
2. Learn logic and metamathematics from a verifier-first perspective. "If it's not formally verified, it's folk knowledge,
it's scattering bones and reading them"--is what I'd like to say, but in fact we still have to touch base
with references. I haven't found any book that goes as far as I would like, perhaps they exist in the
Lean- or Agda-sphere.
3. Learn the history and terminology around important areas, while connecting to and citing literature. 
Thus, if I say a nonsequitur in conversation with logicians, I can at least say "oh, I was using the 
definition in Gaifman's 2002 student notes, what one are you using?" This helps us avoid (but doesn't 
entirely prevent) developing totally wacko ideas while completing independent studies.
4. Deign to learn some of the important English language proofs, where we only our brains as proof checkers.
This is how most of the literature works so it really can't be avoided. Also, sometimes, such as in `peano.mm`, 
the metamath database contains a lot of exposition in the form of prose assertions justifying the 
properties of the axioms.
5. Perhaps learn some type theory (formalized in `.mm`) while we're at it.

The reason for my staunch "if it's not formally verified it doesn't exist" stance is not philosophy-first
nor because I think it's pedagogically good. I simply don't understand the books. I can get an A in the coursework
and repeat the English language proofs, but I am not sure that I'm not getting them wrong. I know that the
verifier consisting of the examiner's brain finds the argument convincing, but I can't be sure that there's
any sense to it at all. So I've been deeply deeply confused for a number of years and only now am I repairing that.

AI usage: I've found AI to be an absolutely horrible teacher, an OK problem set generator, 
and an absolutely amazing reference-finder, so I use it 0% for teaching and terminology, 60% problem set generations
+ human review (in the form of actually doing the problems), and 95% for finding references. For teaching,
I think it gets stuck in a deep "intro to proofs" attractor. Dawg I'm a decade out from intro to proofs.
Doesn't help that there's much less material with a verifier-first perspective. Anyways I also try to put an
AI warning in any section that hasn't been reviewed and thoroughly worked through, like this one:

> [!WARNING]
> Usually there will be a "AI made this and I haven't reviewed it yet" statement here.

I can't bear to read AI writing so I don't expect you to bear it either.

## Stuff I want to do:

- Formalize something regarding Turing machines
- Enumerate the smallest theorems of some theory
- Find the shortest proof of some statement using a SAT solver
- Formalize some theorems in plane geometry from Hilbert's axioms
- Primality certificates (Pratt 1975?)
- Read and create examples from Mario Carneiro "[Models for Metamath](https://arxiv.org/abs/1601.07699)" 2016

## Primary Sources I'm using

- The metamath book. You know it, I know it.
- Harper, [Practical Foundations for Programming Languages](https://www.cs.cmu.edu/~rwh/pfpl.html). I'm using ch1-3. when I saw "alpha equivalence" in `peano.mm` I knew I had to.
- Kleene 1952, [Introduction to Metamathematics](https://shop.elsevier.com/books/introduction-to-metamathematics/kleene/978-0-7204-2103-3).
- Mendelson, [Introduction to Mathematical Logic](https://doi.org/10.1201/b18519).
- Sam Buss [Introduction to Mathematical Logic](https://www.math.ucsd.edu/~sbuss/IntroMathLogic/Fullbook_Draft.pdf) (course notes, 2023).

Papers:

- [How to Believe a Machine-Checked Proof](https://doi.org/10.7146/brics.v4i18.18945). Essential reading.
- [The Challenge of Computer Mathematics](https://doi.org/10.1098/rsta.2005.1650). Essential reading. Barendregt coined the term "de Bruijn criterion" in 1997. 
- [The Impact of the Lambda Calculus in Logic and Computer Science](https://doi.org/10.2307/421013) by Henk Barendregt, Bulletin of Symbolic Logic 3(2), 181–215 (1997) (paper that coined the term, 'cuz I might as well link it).
- Gaifman, [A Hilbert Type Deductive System for Sentential Logic, Completeness and Compactness](https://www.columbia.edu/~hg17/ViewMathLogic/view1-deductive-system.pdf) (2002). This is at the very least the most direct definition of a 
Hilbert-style formal system. It seems to be a bit overly-broad though, I'd argue it says Metamath 
itself is Hilbert-style though we say colloquially that the logics represented in various Metamath
databases need not be Hilbert-style. 
But Norm Megill et al are very careful to never say "Metamath is Hilber-style." So whatever, we call
Metamath Hilbert-inspired and move on, I was a stickler over terminology for way too long.



Other links can be found in [links.html](links.html)
