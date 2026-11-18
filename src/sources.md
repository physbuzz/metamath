---
title: "Sources"
---

# Sources

The books and papers in `book/dontshare`, and where we used them.
Page links use PDF page numbers; printed page numbers are given separately.

## Local copies

- [Gaifman 2002, A Hilbert Type Deductive System for Sentential Logic, Completeness and Compactness](book/dontshare/Hilbert%20Type%20Deductive%20System%20Course%20Notes%20Gaifman%202002.pdf#page=1).
  We used p. 1 for the definitions of inference rule and Hilbert-type deductive
  system in [ch04 §4.0.1](04-propmm.html). This also prompted the discussion of
  whether Metamath itself should be called Hilbert-style. We haven't used the
  completeness or compactness proofs.

- [Harper 2012, Practical Foundations for Programming Languages](book/dontshare/Practical%20Foundations%20for%20Programming%20Languages%20Harper%202012.pdf#page=34).
  We used ch2 for judgments, inference rules, and the tree example in
  [ch04 §4.0.1](04-propmm.html): PDF pp. 34–35 (printed pp. 16–17).
  Seeing “alpha-equivalence” in `peano.mm` was what sent us to ch1;
  that discussion is on [PDF pp. 28–30](book/dontshare/Practical%20Foundations%20for%20Programming%20Languages%20Harper%202012.pdf#page=28)
  (printed pp. 10–12). Ch1–3 are also the reading for the planned ch5.5.

- [Buss 2023, Introduction to Mathematical Logic](book/dontshare/Introduction%20to%20Mathematical%20Logic%20Buss%202023.pdf#page=55).
  We used his notation for proofs from hypotheses, `⊢` versus `⊨`, and
  modus ponens in [ch04 §4.0.1](04-propmm.html). PDF pp. 55–56
  (printed pp. 47–48). The historical footnote we quote about Hilbert-style
  systems is footnote 2 on PDF p. 55.

- [Mendelson 2015, Introduction to Mathematical Logic, 6th ed.](book/dontshare/mendelson/Mendelson%20Introduction%20to%20Mathematical%20Logic%206ed%20%282015%29.pdf#page=54).
  Lemma 1.8 is the proof of [`idALT`](https://us.metamath.org/mpeuni/idALT.html),
  mentioned with the `id` exercise in [ch04 §4.1.1](04-propmm.html).
  PDF pp. 54–55 (printed pp. 29–30 in this edition; `set.mm` cites p. 36
  of an older edition).

- [Hirst & Hirst 2015, A Primer for Logic and Proof](book/dontshare/hirst/hirst.pdf#page=23).
  Downloaded because metamath.org recommended it, but we didn't end up using it.
  Mostly a ch04 reference, possibly ch01. “Our first proof,” PDF p. 23
  (printed p. 17), is also [`idALT`](https://us.metamath.org/mpeuni/idALT.html).

- [Hamilton 1988, Logic for Mathematicians](book/dontshare/hamilton/Logic%20for%20Mathematicians%20Hamilton%201988%7B91195154%7Ddjvu).
  A book cited by `set.mm` for propositional calculus. Its Example 2.7(a),
  printed p. 31, is exactly the proof of
  [`idALT`](https://us.metamath.org/mpeuni/idALT.html).
  Hamilton's book is shorter and gentler than Mendelson's.
  No direct use in current notes version. The local copy is DjVu.

- [Tarski 1964, A Simplified Formalization of Predicate Logic with Identity](book/dontshare/tarski1964.pdf#page=15).
  The source of the predicate-calculus axioms we work through in
  [ch05](05-predicate-calculus.html). In particular, our `ax6v` is his
  Axiom B7, with distinct variables `x` and `y`: PDF p. 15 (printed p. 75).
  Also on the ch05 reading list for understanding the treatment of variables.

- [Megill 1995, A Finitely Axiomatized Formalization of Predicate Calculus with Equality](book/dontshare/megill%201995.pdf).
  Put on the ch05 reading list alongside Tarski. No direct use in current
  notes version; the reading notes are still empty.

- [Van Heijenoort, ed., From Frege to Gödel](book/dontshare/Jean%20Van%20Heijenoort%20%28editor%29%20-%20From%20Frege%20to%20Godel_%20A%20Source%20Book%20in%20Mathematical%20Logic%2C%201879-1931%20%281999%2C%20iUniverse%29%20-%20libgen.li.pdf).
  Contains both historical sources we discuss in the
  [ch05 introduction](05-predicate-calculus.html):

  - [Skolem 1923, The foundations of elementary arithmetic established by means
    of the recursive mode of thought, without the use of apparent variables
    ranging over infinite domains](book/dontshare/Jean%20Van%20Heijenoort%20%28editor%29%20-%20From%20Frege%20to%20Godel_%20A%20Source%20Book%20in%20Mathematical%20Logic%2C%201879-1931%20%281999%2C%20iUniverse%29%20-%20libgen.li.pdf#page=313).
    This is the reference for developing arithmetic without quantifiers.
    PDF pp. 313–344 (printed pp. 302–333), starting with the title and
    editorial introduction on p. 313. Skolem's text begins on PDF p. 314.

  - [Frege 1879, Begriffsschrift](book/dontshare/Jean%20Van%20Heijenoort%20%28editor%29%20-%20From%20Frege%20to%20Godel_%20A%20Source%20Book%20in%20Mathematical%20Logic%2C%201879-1931%20%281999%2C%20iUniverse%29%20-%20libgen.li.pdf#page=35).
    §§11–12 discuss generality and its scope: PDF pp. 35–39
    (printed pp. 24–28). [PDF p. 36](book/dontshare/Jean%20Van%20Heijenoort%20%28editor%29%20-%20From%20Frege%20to%20Godel_%20A%20Source%20Book%20in%20Mathematical%20Logic%2C%201879-1931%20%281999%2C%20iUniverse%29%20-%20libgen.li.pdf#page=36)
    (printed p. 25) is the passage closest to our question about why quantifiers
    are needed inside statements. The chapter still marks this reading as a TODO.
    To read from the beginning, the editorial introduction starts at
    [PDF p. 12](book/dontshare/Jean%20Van%20Heijenoort%20%28editor%29%20-%20From%20Frege%20to%20Godel_%20A%20Source%20Book%20in%20Mathematical%20Logic%2C%201879-1931%20%281999%2C%20iUniverse%29%20-%20libgen.li.pdf#page=12), and Frege's preface at PDF p. 16.

- [Farmer 2008, The Seven Virtues of Simple Type Theory (rev. 2019)](book/dontshare/seven-virtues.pdf).
  One of the two readings for the `hol.mm` section in
  [ch04 §4.2.3](04-propmm.html). We don't cite a particular result from it.

- [Church 1940, A Formulation of the Simple Theory of Types](book/dontshare/A%20Formulation%20of%20the%20Simple%20Theory%20of%20Types%20Church%201940.pdf).
  The other reading for [ch04 §4.2.3](04-propmm.html), where we try `hol.mm`.
  We don't cite a particular result from it.

- [Pollack 1997, How to Believe a Machine-Checked Proof](book/dontshare/How%20to%20Believe%20a%20Machine-Checked%20Proof%20Pollack%201997.pdf#page=4).
  On trusting a proof checker and checking proofs independently; especially
  PDF pp. 4–6 (printed pp. 2–4). Listed as essential reading in the
  [introduction](index.html), alongside the discussion of trust in formal proofs.

- [Barendregt & Wiedijk 2005, The Challenge of Computer Mathematics](book/dontshare/The%20Challenge%20of%20Computer%20Mathematics%20Barendregt%20and%20Wiedijk%202005.pdf#page=12).
  Listed in the [introduction](index.html) for the de Bruijn criterion:
  proofs should be checkable by a small independent program. The relevant
  discussion is on PDF p. 12 (also printed p. 12).

- [Kleene, Introduction to Metamathematics (1952; local 1971 copy)](book/dontshare/Introduction%20to%20Metamathematics%20Kleene%201971.djvu).
  Listed among the [primary sources](index.html). No direct use in current
  notes version. The local copy is DjVu.

- [Behnke et al. 1974, Fundamentals of Mathematics, vol. I](book/dontshare/H.%20Behnke%2C%20F.%20Bachmann%2C%20K.%20Fladt%2C%20W.%20S%C3%BCss%20and%20H.%20Kunle%20-%20Fundamentals%20of%20Mathematics_%20Foundations%20of%20Mathematics_%20The%20Real%20Number%20System%20and%20Algebra%201%20%281974%2C%20MIT%20Press%29%20-%20libgen.li.pdf).
  Megill cites printed p. 6 on formalism in his book's
  [§1.4.3](book/index.html#Ch1.S4.SS3), and p. 20 on theorems depending on
  definitions as well as axioms in [§4.5](book/index.html#Ch4.S5).
  No direct use in our notes.

- [Frege, Basic Laws of Arithmetic, vol. I, Ebert–Rossberg translation draft](book/dontshare/frege/Frege-BasicLaws-1.pdf).
  No direct use in current notes version. This is a different work from the
  1879 *Begriffsschrift* above.

- [Benacerraf 1965, What Numbers Could Not Be](book/dontshare/1965-benacerraf.pdf).
  No direct use in current notes version.

- [Ebbinghaus, Flum & Thomas, Mathematical Logic (local 2021 copy)](book/dontshare/ebbinghaus/Mathematical%20Logic%20Ebbinghaus%20Flum%20Thomas%20%282021%29%2893983544%29.pdf).
  No direct use in current notes version.

- [Leary & Kristiansen 2015, A Friendly Introduction to Mathematical Logic, 2nd ed.](book/dontshare/A-Friendly-Introduction-to-Mathematical-Logic.pdf).
  No direct use in current notes version.

## Referenced but missing from `dontshare`

- Peters 2022, *Gödel's Theorem Without Tears*.
  We took the arithmetic axioms in [ch05 §5.0.1](05-predicate-calculus.html)
  from Definition 4.16, [PDF p. 33](https://www.ps.uni-saarland.de/~peters/bachelor/resources/thesis.edited.pdf#page=33)
  (printed p. 23). Our `zos` is his axiom CD.

- Abelson & Sussman with Sussman, *Structure and Interpretation of Computer Programs*.
  §4.4 supplies the query system used in [ch02](02-sicp-logic.html) and
  [ch02.5](02.5-sicp-logic-redo.html): matching, unification, and rule search.
  We modify it to produce Metamath proof certificates.

- Pavičić 1992, *A New Axiomatization of Unified Quantum Logic*.
  Cited when introducing `ql.mm` and ortholattices in
  [ch04 §4.2.2](04-propmm.html).

- Barendregt 1997, *The Impact of the Lambda Calculus in Logic and Computer Science*.
  Cited in the [introduction](index.html) for coining “de Bruijn criterion.”
  This is a separate paper from Barendregt & Wiedijk 2005.

- Wolfram, *A New Kind of Science*.
  In [ch00](00-rant.html), the discussion of Boolean algebra and a single
  NAND axiom inspired the idea of searching over axiom systems.

These also appear in reading lists, but we haven't used them in the chapters:

- [Introduction](index.html): Carneiro, *Models for Metamath* (2016).
  There is also a tentative “Pratt 1975?” about primality certificates.
- [Links](links.html), proof checkers: Harper–Honsell–Plotkin,
  *A Framework for Defining Logics*; Wiedijk, *Comparing Mathematical Provers*
  (2003), §4.2's de Bruijn-criterion comparison; *A Survey on Theorem Provers
  in Formal Methods*.
- [Links](links.html), other papers: Harrison, *Towards Self-Verification of
  HOL Light* (2006); Carneiro, *Metamath Zero* (2019); *Generating Theorems by
  Generating Proof Structures*.
- [Links](links.html), books: Hofstadter's MU-puzzle chapter;
  Gonczarowski–Nisan, *Mathematical Logic through Python*; Harrison, *Handbook of
  Practical Logic and Automated Reasoning*; Friedman–Eastlund, *The Little Prover*;
  *Software Foundations: Logical Foundations*; *Programming Language Foundations
  in Agda*; Smolka, *Modeling and Proving in Computational Type Theory*;
  Shankar, *Metamathematics, Machines and Gödel's Proof*; Prusinkiewicz–Lindenmayer,
  *The Algorithmic Beauty of Plants*, ch1. Some of these are online books.
- [Ch05 scratchwork](05-scratchwork.html): Avigad's `understanding2.pdf`
  and *Concrete Semantics*.

[Megill's Metamath book](book/metamath.pdf) is already beside `dontshare`.
Skolem 1923 and Frege's *Begriffsschrift* are both in van Heijenoort above.
