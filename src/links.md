---
title: "Metamath Links"
---

<h1 id="links" style="border-bottom: none;">Metamath Links</h1>

<nav class="nav">
    <span class="activenav"><a href="index.html">Up</a></span>
</nav>

## Metamath.org links

- Metamath notes on [definitions](https://us.metamath.org/mpeuni/mmset.html#definitions) and [distinct variables](https://us.metamath.org/mpeuni/mmset.html#distinct).
- [Deduction Form and Natural Deduction in Metamath](https://us.metamath.org/mpeuni/mmnatded.html).
- Metamath databases for [intuitionistic logic and set theory](https://github.com/metamath/set.mm/blob/develop/iset.mm), [quantum logic](https://github.com/metamath/set.mm/blob/develop/ql.mm), and [higher-order logic](https://github.com/metamath/set.mm/blob/develop/hol.mm).
- [Number Theory Game for Metamath](https://github.com/pbrosnan/ntg), including the [peano.mm database used in these notes](https://github.com/pbrosnan/ntg/blob/15332ee0dfe50ada14b6e31e947272232e4dc671/peano.mm).
- The MIU system in [Metamath's miu.mm](https://us.metamath.org/metamath/miu.mm) and [Mathlib's Lean formalization](https://leanprover-community.github.io/mathlib4_docs/Archive/MiuLanguage/Basic.html).
- Alternative propositional axiomatizations: [Meredith's single axiom](https://us.metamath.org/mpeuni/meredith.html) and [Lukasiewicz's axioms](https://us.metamath.org/mpeuni/luk-1.html).
- Tarski geometry in [Metamath](https://us.metamath.org/mpeuni/df-trkg.html) and [GeoCoq](https://geocoq.github.io/GeoCoq/html/GeoCoq.Axioms.tarski_axioms.html).
- Mario Carneiro's [formalization of Metamath formal systems in set.mm](https://us.metamath.org/mpeuni/df-mcls.html).

## tiny proof checkers

> [!WARNING]
> This has been compiled by AI and has not yet been reviewed

Tiny proof checkers:

- [mmverify.py](https://github.com/david-a-wheeler/mmverify.py), a Python Metamath verifier, and [metamath-test](https://github.com/david-a-wheeler/metamath-test), a verifier test suite.

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

## Even more links

Papers:

- John Harrison, [Towards self-verification of HOL Light](https://www.cl.cam.ac.uk/~jrh13/papers/holhol.html) (2006).
- Mario Carneiro, [Metamath Zero: The Cartesian Theorem Prover](https://arxiv.org/abs/1910.10703) (2019), and the [Metamath Zero repository](https://github.com/digama0/mm0).
- Generating Theorems by Generating Proof Structures https://link.springer.com/chapter/10.1007/978-3-032-32589-1_3
- Mladen Pavicic, [A new axiomatization of unified quantum logic](https://doi.org/10.1007/BF00671784) (1992).

Books:

- Holly P. Hirst and Jeffry L. Hirst, [A Primer for Logic and Proof](https://www.appstate.edu/~hirstjl/primer/hirst.pdf) (2015).
- Douglas Hofstadter, [Godel, Escher, Bach, Chapter I: The MU-puzzle](https://www.ratiocination.org/Courses/phil3505/wp-content/uploads/2017/08/Hofstadter__Godel-Escher-Bach-excerpt-on-MU-puzzle.pdf).
- Gonczarowski and Nisan 2022, [Mathematical Logic through Python](https://www.logicthrupython.org/)
- Harrison 2009, [Handbook of Practical Logic and Automated Reasoning](https://www.cl.cam.ac.uk/~jrh13/atp/) (OCaml)
- Friedman and Eastlund 2015, [The Little Prover](https://the-little-prover.github.io/) (custom language)
- Pierce et al. 2016, [Software Foundations: Logical Foundations](https://softwarefoundations.cis.upenn.edu/lf-current/) (Rocq)
- Wadler 2018, [Programming Language Foundations in Agda (PLFA)](https://plfa.github.io/) 
- Smolka 2026 (draft), [Modeling and Proving in Computational Type Theory](https://www.ps.uni-saarland.de/~smolka/drafts/mpctt.pdf) (Rocq)
- Shankar 1994, [Metamathematics, Machines and Gödel's Proof](https://www.csl.sri.com/~shankar/goedel-book.html) (Machine-checked metamathematics)
- Przemyslaw Prusinkiewicz and Aristid Lindenmayer, [The Algorithmic Beauty of Plants, Chapter 1](https://algorithmicbotany.org/papers/abop/abop-ch1.pdf).
