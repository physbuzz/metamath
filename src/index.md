---
title: "Metamath Study Notes"
---

Hosted on [mathandcode.com/books/metamath](https://www.mathandcode.com/books/metamath/).

[Read in html](book/metamath.html) &nbsp;|&nbsp; [Read in pdf](book/metamath.pdf) | .

# Metamath Study Notes

Independently studying Metamath and its applications while staunchly saying
"if I have to verify it in my head and not in a computer program then it's not math."



I mean seriously, you can't teach me about primitive symbols and then say "oh yeah but these
represent different things so they're totally different." You just taught me to divorce
the symbols from words, then staple words back on! But I'm getting ahead of myself.

## Contents

- [0 Rant about Mathematical Proof (cf. Megill ch1)](00-rant.html)
- [1 Working through a Metamath Proof by Hand (Megill ch2)](01-megillch2.html)
- [2 Bonus chapter: Connection with Logic Programming (cf. SICP 4.4)](02-sicp-logic.html)
- [3 Writing a C++ Metamath Interpreter (Megill ch4)](03-interpreter.html)
- [4 Studying Propositional Calculus with Metamath](04-propmm.html)
- [5 Variables, Binding, and Predicate Calculus](05-predicate-calculus.html)
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
> Usually there's a "AI made this and I haven't reviewed it yet" statement here.

## Other Sources and Links

(TODO links and citations here should be to DOIs and stuff not to the local PDFs. This text should be deleted
after the todo is done).

Prose and notes: 

- (TODO link [DOI?] and correct title) How to Trust a Machine-Checked Proof. Essential reading.
- (TODO link) The Challenge of Computer Mathematics. Essential reading. Barendregt coined the term "de Bruijn criterion" in 1997. 
- (TODO link) The Impact of the Lambda Calculus in Logic and Computer Science by Henk Barendregt, Bulletin of Symbolic Logic 3(2), 181–215 (1997) (paper that coined the term, 'cuz I might as well link it).
- (TODO link to Gaifman's notes). This is at the very least the most direct definition of a 
Hilbert-style formal system. It seems to be a bit overly-broad though, I'd argue it says Metamath 
itself is Hilbert-style though we say colloquially that the logics represented in various Metamath
databases need not be Hilbert-style. 
But Norm Megill et al are very careful to never say "Metamath is Hilber-style." So whatever, we call
Metamath Hilbert-inspired and move on, I was a stickler over terminology for way too long.

Book notes:

- The metamath book. You know it, I know it.
- (TODO link+title) Harper. I'm using ch1-3. when I saw "alpha equivalence" in `peano.mm` I knew I had to.
- (TODO link) Kleene 19xx, Introduction to Metamathematics Kleene.
- (TODO link) Mendelson, introduction to mathematical logic.
- (TODO link) Sam Buss Introduction to Mathematical Logic (course notes, 2023).

## Stuff I want to do:

- Formalize something regarding Turing machines
- Enumerate the smallest theorems of some theory
- Find the shortest proof of some statement using a SAT solver
- Formalize some theorems in plane geometry from Hilbert's axioms
- Primality certificates (Pratt 1975?)
- Read and create examples from Mario Carneiro "Models for Metamath" 2016 (TODO link)

## way more links

... TODO: collate


Papers:

- Generating Theorems by Generating Proof Structures https://link.springer.com/chapter/10.1007/978-3-032-32589-1_3

Books:

- Pierce et al. 2016, [Software Foundations: Logical Foundations](https://softwarefoundations.cis.upenn.edu/lf-current/) (Rocq)
- Wadler 2018, [Programming Language Foundations in Agda (PLFA)](https://plfa.github.io/) 
- Friedman and Eastlund 2015, [The Little Prover](https://the-little-prover.github.io/) (custom language)
- Smolka 2026 (draft), [Modeling and Proving in Computational Type Theory](https://www.ps.uni-saarland.de/~smolka/drafts/mpctt.pdf) (Rocq)
- Harrison 2009, [Handbook of Practical Logic and Automated Reasoning](https://www.cl.cam.ac.uk/~jrh13/atp/) (OCaml)
- Gonczarowski and Nisan 2022, [Mathematical Logic through Python](https://www.logicthrupython.org/)
- Shankar 1994, [Metamathematics, Machines and Gödel's Proof](https://www.csl.sri.com/~shankar/goedel-book.html) (Machine-checked metamathematics)

## tiny proof checkers

> [!WARNING]
> This has been compiled by AI and has not yet been reviewed

Tiny proof checkers:

- Hirrolot, [How to Implement Dependent Types in 80 Lines of Code](https://gist.github.com/hirrolot/27e6b02a051df333811a23b97c375196?utm_source=chatgpt.com) (OCaml, Calculus of Constructions). An exceptionally small implementation of dependent type checking, including dependent function types, lambda abstraction, application, and beta reduction. Uses higher-order abstract syntax (HOAS) to simplify variable binding and substitution. A demonstration of how little code is needed for the mathematical core, although it is not a complete standalone proof-checking environment.

- Andrej Bauer, [How to Implement Dependent Type Theory I](https://math.andrej.com/2012/11/08/how-to-implement-dependent-type-theory-i/?utm_source=chatgpt.com) (OCaml, 92-line core). A particularly approachable tutorial implementing dependent type theory with a hierarchy of universes, dependent functions, substitution, normalization, and type inference. The complete program includes a parser and interactive interface. Parts II and III explore normalization by evaluation, de Bruijn indices, and explicit substitutions. Probably the best pedagogical starting point.

- 45deg, [Proofglyph](https://github.com/45deg/proofglyph) (OCaml, Logical Framework). A small proof checker implementing the dependent lambda calculus underlying LF. Particularly interesting as a comparison with Metamath because different formal systems can be represented by declaring their judgments and inference rules. Uses de Bruijn indices and beta reduction, with a stack-oriented proof format and a separate readable frontend. Also has a [browser-based demonstration](https://45deg.github.io/proofglyph/?utm_source=chatgpt.com).

- John Harrison, [HOL Light](https://github.com/jrh13/hol-light) (OCaml, classical higher-order logic). A mature theorem prover built around a comparatively small kernel implementing primitive inference rules. Unlike the dependent type theory examples, HOL Light uses simple type theory and an LCF-style architecture. Worth examining because its small logical foundation supports a substantial library of formalized mathematics, although the complete system is considerably larger than the other examples.

- Frank Pfenning et al., [Twelf](https://twelf.org/wiki/lf/) (Standard ML, Logical Framework). An established implementation of LF for representing deductive systems using dependent types. Includes proof checking, logic programming, and machinery for verifying metatheorems about encoded systems. Much larger than the minimal implementations above, but useful for seeing what a fully developed LF environment looks like.

Related paper:

- Harper, Honsell, and Plotkin, [A Framework for Defining Logics](https://www.lfcs.inf.ed.ac.uk/reports/87/ECS-LFCS-87-23/). The original presentation of LF, explaining how syntax, inference rules, and proofs of different formal systems can be represented using dependent type theory. Particularly relevant for understanding the mathematical ideas behind Proofglyph and Twelf.

Survey of proof checkers:
- https://www.researchgate.net/publication/337829832_A_Survey_on_Theorem_Provers_in_Formal_Methods
- Freek Wiedijk 2003, [Comparing Mathematical Provers (PDF)](https://www.cs.ru.nl/F.Wiedijk/comparison/diffs.pdf). Section 4.2, page 10, contains a table comparing 15 systems specifically against the de Bruijn criterion. Wiedijk identifies HOL, Coq, Otter/Ivy, Isabelle, Agda, PhoX, Metamath, Lego, and Omega as satisfying it. He also discusses the distinction between having a small kernel and having an independently checkable proof.