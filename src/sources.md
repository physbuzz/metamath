---
title: "Sources"
---

# Sources

Inventory of `src/book/dontshare`, matched to actual passages in the study notes.
Chapter numbers below refer to our notes, not Megill's book. “Listed” means a
reading recommendation, not evidence that we used the source. “No use located”
means no identifiable citation or passage; it does not establish that a source
was never consulted. PDF/DjVu copies are counted once, with OCR companions grouped
under the same work. Links are relative to the hosted `sources.html`; PDF page
numbers count from the first page of the file, with printed page numbers noted
separately.

## Local copies and where they came up

- [Gaifman 2002, *A Hilbert Type Deductive System for Sentential Logic, Completeness and
  Compactness*](book/dontshare/Hilbert%20Type%20Deductive%20System%20Course%20Notes%20Gaifman%202002.pdf#page=1).
  [Ch04](04-propmm.html), §4.0.1 and quiz Q2: definitions of **inference rule**,
  premises/conclusion, and **Hilbert-type deductive system**; the discussion of whether Metamath
  itself should be called Hilbert-style. The definitions and modus ponens are on **PDF p. 1**
  (printed p. 1). No use of the completeness/compactness proofs located.

- [Harper 2012, *Practical Foundations for Programming
  Languages*](book/dontshare/Practical%20Foundations%20for%20Programming%20Languages%20Harper%202012.pdf#page=34).
  [Ch04](04-propmm.html), §§4.0.1–2: judgments, inductive definitions by rules, premise-free axioms
  versus proper rules, the tree example, and derived rules. Alpha-equivalence in `peano.mm` prompted
  the ch1–3 reading. [Ch05 scratchwork](05-scratchwork.html), §5.0.2, uses ch1 for binding/capture;
  the ch5.5 reading chapter listed in the contents has no source file yet. Rules and the tree
  example: **PDF pp. 34–35** (printed pp. 16–17); α-equivalence: [PDF pp.
  28–30](book/dontshare/Practical%20Foundations%20for%20Programming%20Languages%20Harper%202012.pdf#page=28)
  (printed pp. 10–12).

- [Buss 2023, *Introduction to Mathematical
  Logic*](book/dontshare/Introduction%20to%20Mathematical%20Logic%20Buss%202023.pdf#page=55).
  [Ch04](04-propmm.html), §4.0.1: PL-proofs, `⊢` versus `⊨`, modus ponens notation, “axiom scheme,”
  and the quoted historical footnote on Hilbert-style systems. **PDF pp. 55–56** (printed pp.
  47–48), especially footnote 2 on p. 55 and Definitions II.1–2 on p. 56.

- [Mendelson, *Introduction to Mathematical Logic*, 6th ed.
  (2015)](book/dontshare/mendelson/Mendelson%20Introduction%20to%20Mathematical%20Logic%206ed%20%282015%29.pdf#page=54).
  [Ch04](04-propmm.html), §4.1.1: the `id` exercise is identified as Lemma 1.8: **PDF pp. 54–55**
  (printed pp. 29–30 in this edition). Also listed among the [primary sources](index.html). Broader
  propositional-calculus reading appears in old drafts, but is not evidence of further use in the
  current chapter.

- [Hirst & Hirst 2015, *A Primer for Logic and Proof*](book/dontshare/hirst/hirst.pdf). **Unused
  reading recommendation**, acquired through metamath.org; primarily ch04, with ch01 as a secondary
  association. Listed in [links](links.html); the [ch04](04-propmm.html) §4.1.1 `id` comment
  mentions “our first proof,” but this inherited cross-reference does not mean we worked from the
  book. `hirst/index.md` and `hirst/images/` are its OCR companions.

- [Tarski 1964, *A Simplified Formalization of Predicate Logic with
  Identity*](book/dontshare/tarski1964.pdf#page=15). [Ch05](05-predicate-calculus.html), §5.1: the
  predicate axioms, especially `ax6v` identified as B7 with distinct `x`, `y`: **PDF p. 15**
  (printed p. 75). Explicitly listed as required reading in [scratchwork](05-scratchwork.html),
  which also connects Tarski's approach to distinct variables; the dedicated reading notes are
  unfinished.

- [Megill 1995, *A Finitely Axiomatized Formalization of Predicate Calculus with
  Equality*](book/dontshare/megill%201995.pdf). [Ch05 scratchwork](05-scratchwork.html), “Required
  reading” / “Notes on Megill 1995”: listed alongside Tarski for the predicate-calculus work. The
  notes heading is empty; no specific result from this paper is cited in the current ch05 prose.

- [Van Heijenoort, ed., *From Frege to
  Gödel*](book/dontshare/Jean%20Van%20Heijenoort%20%28editor%29%20-%20From%20Frege%20to%20Godel_%20A%20Source%20Book%20in%20Mathematical%20Logic%2C%201879-1931%20%281999%2C%20iUniverse%29%20-%20libgen.li.pdf).
  Covers two
  references in the [ch05 introduction](05-predicate-calculus.html):
  - [Skolem 1923, *The foundations of elementary arithmetic established by means
    of the recursive mode of thought, without the use of apparent variables
    ranging over infinite domains*](book/dontshare/Jean%20Van%20Heijenoort%20%28editor%29%20-%20From%20Frege%20to%20Godel_%20A%20Source%20Book%20in%20Mathematical%20Logic%2C%201879-1931%20%281999%2C%20iUniverse%29%20-%20libgen.li.pdf#page=313): **PDF pp. 313–344**
    (printed pp. 302–333). The editorial introduction starts on **PDF p. 313**;
    Skolem's text starts near the bottom of **PDF p. 314**, and his explicit
    quantifier-free program is on [**PDF p. 315**](book/dontshare/Jean%20Van%20Heijenoort%20%28editor%29%20-%20From%20Frege%20to%20Godel_%20A%20Source%20Book%20in%20Mathematical%20Logic%2C%201879-1931%20%281999%2C%20iUniverse%29%20-%20libgen.li.pdf#page=315)
    (printed p. 304).
  - [Frege 1879, *Begriffsschrift*](book/dontshare/Jean%20Van%20Heijenoort%20%28editor%29%20-%20From%20Frege%20to%20Godel_%20A%20Source%20Book%20in%20Mathematical%20Logic%2C%201879-1931%20%281999%2C%20iUniverse%29%20-%20libgen.li.pdf#page=35): **§§11–12, PDF pp. 35–39**
    (printed pp. 24–28), on generality, scope, and combinations with negation.
    The closest passage to ch05's motivation for quantifiers is
    [**PDF p. 36**](book/dontshare/Jean%20Van%20Heijenoort%20%28editor%29%20-%20From%20Frege%20to%20Godel_%20A%20Source%20Book%20in%20Mathematical%20Logic%2C%201879-1931%20%281999%2C%20iUniverse%29%20-%20libgen.li.pdf#page=36) (printed p. 25): why the scope marker is
    necessary when generality occurs inside a judgment. The work's editorial
    introduction starts at [PDF p. 12](book/dontshare/Jean%20Van%20Heijenoort%20%28editor%29%20-%20From%20Frege%20to%20Godel_%20A%20Source%20Book%20in%20Mathematical%20Logic%2C%201879-1931%20%281999%2C%20iUniverse%29%20-%20libgen.li.pdf#page=12), printed p. 1;
    Frege's preface starts at PDF p. 16, printed p. 5. Ch05 still marks this
    reading as a TODO.

  Both works are present in this volume, not missing PDFs.

- [Farmer, *The Seven Virtues of Simple Type Theory* (2008; rev.
  2019)](book/dontshare/seven-virtues.pdf). [Ch04](04-propmm.html), §4.2.3: explicitly assigned
  reading for the `hol.mm` excursion and its distinction between `|=` judgments and object-language
  implication. No individual theorem from the paper is invoked.

- [Church 1940, *A Formulation of the Simple Theory of
  Types*](book/dontshare/A%20Formulation%20of%20the%20Simple%20Theory%20of%20Types%20Church%201940.pdf).
  [Ch04](04-propmm.html), §4.2.3: the other assigned reading for `hol.mm`; no individual result
  cited.

- [Pollack 1997, *How to Believe a Machine-Checked
  Proof*](book/dontshare/How%20to%20Believe%20a%20Machine-Checked%20Proof%20Pollack%201997.pdf).
  Listed as essential reading in the [introduction](index.html). An old draft
  (`ai/05-logicians-rewrite.md`), §5.1.4, explicitly attaches it to trusting the checker and writing
  independent checkers, referring back to ch03. That passage is not in the current chapters.

- [Barendregt & Wiedijk 2005, *The Challenge of Computer
  Mathematics*](book/dontshare/The%20Challenge%20of%20Computer%20Mathematics%20Barendregt%20and%20Wiedijk%202005.pdf).
  [Introduction](index.html), papers list: essential reading in the discussion of the **de Bruijn
  criterion**. Ch00 names the criterion but has an unfinished citation TODO; no more specific use of
  this paper located.

- [Kleene, *Introduction to Metamathematics* (1952; local 1971 copy,
  DjVu)](book/dontshare/Introduction%20to%20Metamathematics%20Kleene%201971.djvu). Listed among the
  [primary sources](index.html). An old AI reading list (`ai/05-logicians.bak.md`), §5.1,
  recommended §§19–23 for rule notation and formal deduction; that list explicitly says its section
  references were unchecked. No specific current-chapter use located.

- [Hamilton 1988, *Logic for Mathematicians*
  (DjVu)](book/dontshare/hamilton/Logic%20for%20Mathematicians%20Hamilton%201988%7B91195154%7Ddjvu).
  The `ax-mp` comment in [the ch03 database](code-03/prop.mm) cites Rule 1, p. 73: an inherited
  Metamath citation. The old reading list (`ai/05-logicians.bak.md`), §5.1, also recommended it for
  the three propositional axioms and `idALT`; no direct use in current chapter prose located.

- [Behnke et al., *Fundamentals of Mathematics*, vol. I
  (1974)](book/dontshare/H.%20Behnke%2C%20F.%20Bachmann%2C%20K.%20Fladt%2C%20W.%20S%C3%BCss%20and%20H.%20Kunle%20-%20Fundamentals%20of%20Mathematics_%20Foundations%20of%20Mathematics_%20The%20Real%20Number%20System%20and%20Algebra%201%20%281974%2C%20MIT%20Press%29%20-%20libgen.li.pdf).
  A traceable connection is **Megill's book**, not a direct citation in our notes:
  [§1.4.3](book/index.html#Ch1.S4.SS3) cites p. 6 on formalism; [§4.5](book/index.html#Ch4.S5) cites
  p. 20 on theorems depending on definitions as well as axioms. Acquisition reason otherwise
  unconfirmed.

- [Frege, *Basic Laws of Arithmetic*, vol. I, Ebert–Rossberg translation
  draft](book/dontshare/frege/Frege-BasicLaws-1.pdf). No direct use located. This is **not** the
  1879 *Begriffsschrift* named in ch05; that work is in van Heijenoort above. `frege/index.md` and
  `frege/images/` accompany this *Basic Laws* translation.

- [Benacerraf 1965, *What Numbers Could Not Be*](book/dontshare/1965-benacerraf.pdf). No citation or
  identifiable use located; acquisition reason unknown.

- [Ebbinghaus, Flum & Thomas, *Mathematical Logic* (local 2021
  copy)](book/dontshare/ebbinghaus/Mathematical%20Logic%20Ebbinghaus%20Flum%20Thomas%20%282021%29%2893983544%29.pdf).
  No citation or identifiable use located; acquisition reason unknown.

- [Leary & Kristiansen 2015, *A Friendly Introduction to Mathematical Logic*, 2nd
  ed.](book/dontshare/A-Friendly-Introduction-to-Mathematical-Logic.pdf). No citation or
  identifiable use located; acquisition reason unknown.

## Referenced works without a copy in `dontshare`

These are gaps relative to the study notes, not an inventory of every reference
inside the bundled Metamath book or downloaded `.mm` databases.

- Peters 2022, *Gödel's Theorem Without Tears*. **Directly used:**
  [ch05](05-predicate-calculus.html), §5.0.1, takes the arithmetic axioms from Definition 4.16, [PDF
  p. 33](https://www.ps.uni-saarland.de/~peters/bachelor/resources/thesis.edited.pdf#page=33)
  (printed p. 23); `zos` is Peters' CD.

- Abelson & Sussman with Sussman, *Structure and Interpretation of Computer Programs*. **Directly
  used:** [ch02](02-sicp-logic.html) and [ch02.5](02.5-sicp-logic-redo.html), §4.4's query system:
  frames, matching/unification, rule search, and modifications to emit proof certificates.

- Pavičić 1992, *A New Axiomatization of Unified Quantum Logic*. [Ch04](04-propmm.html), §4.2.2,
  explicitly cites it when introducing `ql.mm` and ortholattices.

- Barendregt 1997, *The Impact of the Lambda Calculus in Logic and Computer Science*.
  [Introduction](index.html), papers list: cited specifically for coining “de Bruijn criterion.”
  Separate from the 2005 Barendregt–Wiedijk paper already present.

- Wolfram, *A New Kind of Science*. [Ch00](00-rant.html), “An Undergraduate's Quest for Truth”: the
  Boolean-algebra/single-NAND-axiom discussion inspired the search over axiom systems. An
  autobiographical source, not a chapter exercise reference.

Lower-priority gaps, with their limited status preserved:

- [Introduction](index.html), future-work list: Carneiro, *Models for Metamath*
  (2016); Pratt 1975 on primality certificates is only a tentative “Pratt 1975?”
  mention, with no title established.
- [Links](links.html), tiny-checker comparisons: Harper–Honsell–Plotkin,
  *A Framework for Defining Logics*; Wiedijk, *Comparing Mathematical Provers*
  (2003), specifically its §4.2 de Bruijn-criterion table; *A Survey on Theorem
  Provers in Formal Methods*. These are reading-list entries, not worked sources.
- [Links](links.html), other papers: Harrison, *Towards Self-Verification of
  HOL Light* (2006); Carneiro, *Metamath Zero* (2019); *Generating Theorems by
  Generating Proof Structures*. Listed only.
- [Links](links.html), books/excerpts: Hofstadter's MU-puzzle chapter;
  Gonczarowski–Nisan, *Mathematical Logic through Python*; Harrison, *Handbook of
  Practical Logic and Automated Reasoning*; Friedman–Eastlund, *The Little Prover*;
  *Software Foundations: Logical Foundations*; *Programming Language Foundations
  in Agda*; Smolka, *Modeling and Proving in Computational Type Theory*;
  Shankar, *Metamathematics, Machines and Gödel's Proof*; Prusinkiewicz–Lindenmayer,
  *The Algorithmic Beauty of Plants*, ch1. Listed only; some are online books
  rather than missing PDF dependencies.
- [Ch05 scratchwork](05-scratchwork.html), “Old article”: an Avigad PDF
  (`understanding2.pdf`) and *Concrete Semantics* are bare reading links, with no
  developed use there.

Not counted as missing: [Megill's Metamath book](book/metamath.pdf) is already
stored beside `dontshare`. Velleman and Rudin are autobiographical mentions in
ch00; Hilbert–Ackermann and *Principia Mathematica* occur in Buss's quoted history
in ch04, rather than as sources used directly. Ch05's first-epsilon-theorem and
hyperdoctrine remarks cite web articles, not identified PDFs.
