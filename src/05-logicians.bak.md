---
title: "05 Talking to Logicians: Reading List"
---

<h1 id="05-logicians" style="border-bottom: none;">05 Talking to Logicians: Reading List</h1>

<nav class="nav">
    <span class="activenav"><a href="04-propmm.html">← Previous</a></span>
    <span class="activenav"><a href="index.html">↑ Up</a></span>
    <span class="inactivenav" aria-disabled="true">Next →</span>
</nav>

---

> [!WARNING]
> These notes have a lot of AI-suggested problems in them that have not yet
> been reviewed. I put a warning at the start of each section that has not been human-reviewed.
> I tend to rewrite all the AI stuff I read.

> [!WARNING]
> This whole page is an AI-compiled citation list. Page numbers marked *(set.mm)* are
> copied from `set.mm` comments or the Metamath book's bibliography. Everything else,
> including section numbers, is from memory and not yet checked against the source.

@toc

# 5 Reading list

## 5.1 Read first

- **Mendelson, *Introduction to Mathematical Logic*, chapter 1, "The Propositional
  Calculus".** (6th ed., CRC Press, 2015; the Metamath book cites the 2nd ed., 1979.)
  The chapter everyone points to. The section "An axiom system for the propositional
  calculus" defines formal theory, proof, and `Γ ⊢ B`, gives a three-axiom system L
  with modus ponens, proves `B ⇒ B` (Lemma 1.8, p. 36 *(set.mm)*; this is `idALT`),
  then the deduction theorem and completeness. The next two sections cover
  independence via many-valued tables and other axiomatizations, including
  Łukasiewicz's and Meredith's. Two differences from `set.mm`: implication is written
  `⇒`, and the third axiom is `(¬C ⇒ ¬B) ⇒ ((¬C ⇒ B) ⇒ C)` rather than `ax-3`.
- **Hamilton, *Logic for Mathematicians*, chapter 2, "Formal statement calculus".**
  (Revised ed., Cambridge University Press, 1988.) The book `set.mm` and the Metamath
  book cite for propositional calculus. Its system L has exactly `ax-1`, `ax-2`,
  `ax-3` (Definition 2.1, p. 28 *(set.mm)*), and its proof of `A → A` (Example 2.7(a),
  p. 31 *(set.mm)*) is `idALT` step for step. Shorter and gentler than Mendelson.
- **Kleene, *Introduction to Metamathematics*, §19–§23.** (North-Holland, 1952.)
  The source for rule notation. §19 lists the postulates, with each rule of inference
  drawn as premises above a line and the conclusion below. §20 defines formal
  deduction and `Γ ⊢ E`. §21–§22 prove the deduction theorem. §23 collects derived
  rules, each stated as "if `Γ ⊢ ...` then `Γ ⊢ ...`". This is the closest thing to a
  definition of the rule figures that other books use without comment.

## 5.2 Rule notation and the turnstile

- **Harper, *Practical Foundations for Programming Languages*, chapter 2, "Inductive
  definitions".** (2nd ed., Cambridge University Press, 2016.) Defines judgments and
  *inference rules*: premises above a line, conclusion below, and a derivation as a
  tree of rules. This is the rule figure, defined rather than assumed.
- **Megill and Wheeler, *Metamath*, Appendix C, "Metamath's formal system".**
  ([html](book/metamath.html), [pdf](book/metamath.pdf).) Defines what a statement
  with `$e` hypotheses is, with no appeal to a logic textbook. The figure with `⊢` on
  every line, premises and conclusion alike, is this object.
- **`ax-mp` comment in `set.mm`.** Says that the `&` and `⇒` in Proof Explorer
  displays abbreviate "and" and "implies" and are not part of the formal language.
  Cites Rule 1 of Hamilton p. 73 *(set.mm)*.
- **Metamath Proof Explorer, ["Deduction form and natural deduction"](https://us.metamath.org/mpeuni/mmnatded.html)
  and ["The weak deduction theorem"](https://us.metamath.org/mpeuni/mmdeduction.html).**
  How `set.mm` stands in for `Γ ⊢ φ` (inference, deduction, and closed forms; the
  `i`/`d` suffixes).
- **Troelstra and Schwichtenberg, *Basic Proof Theory*, chapters 1–3.** (2nd ed.,
  Cambridge University Press, 2000.) Hilbert systems, natural deduction, and sequent
  calculi in one notation, with rule figures defined carefully.
- **Enderton, *A Mathematical Introduction to Logic*, §2.4, "A deductive calculus".**
  (2nd ed., Academic Press, 2001.) Source of the `Γ; α` notation. Takes every
  tautology as an axiom, so its propositional proofs look nothing like chapter 04.
  Useful for `⊨` versus `⊢`.
- **Frege, *Begriffsschrift* (1879).** Origin of the turnstile (the judgment stroke
  joined to the content stroke). Notation only; not needed as reading.

## 5.3 The axioms in `set.mm`

- **Margaris, *First Order Mathematical Logic*.** (Blaisdell, 1967; Dover reprint.)
  `ax-1`, `ax-2`, `ax-3` are axioms A1–A3, p. 49 *(set.mm)*; Theorem 1, p. 51
  *(set.mm)* is `idALT`. The Metamath book cites it for the standard deduction
  theorem.
- **Hirst and Hirst, *A Primer for Logic and Proof*.** ([pdf](http://www.appstate.edu/~hirstjl/primer/hirst.pdf).)
  Free. "Our first proof", p. 17 *(set.mm)*, is `idALT`.
- **Church, *Introduction to Mathematical Logic* (Princeton University Press, 1956).**
  System P₂ is the `set.mm` system. Heavy on history and attribution.
- **Whitehead and Russell, *Principia Mathematica* (1910–13).** Source of the
  `pm2.43`-style labels: `pm2.43` is theorem ∗2.43. Reference only.
- **Łukasiewicz and Tarski, "Untersuchungen über den Aussagenkalkül" (1930).**
  English in Tarski, *Logic, Semantics, Metamathematics*. The three-axiom
  implication–negation systems, including `luk-1`–`luk-3`.
- **Meredith, "Single axioms for the systems (C,N), (C,O) and (A,N) of the two-valued
  propositional calculus", *Journal of Computing Systems* (1953), 155–164.** The
  single axiom `meredith`.
- **Tarski, "A simplified formalization of predicate logic with identity", *Archiv
  für Mathematische Logik und Grundlagenforschung* 7 (1965), 61–79**, and **Megill,
  "A finitely axiomatized formalization of predicate calculus with equality", *Notre
  Dame Journal of Formal Logic* 36 (1995), 435–453.** Predicate calculus without
  free-variable side conditions. Not needed until `$d`.

## 5.4 Metatheorems

- **Deduction theorem.** Herbrand (1930 thesis) and Tarski (1930), independently.
  Read the proof in Mendelson chapter 1 or Kleene §21.
- **Completeness of propositional calculus.** Post, "Introduction to a general theory
  of elementary propositions", *American Journal of Mathematics* 43 (1921), 163–185.
  Read the proof in Mendelson chapter 1 or Hamilton chapter 2 (the "adequacy theorem").
- **Admissible rules.** Lorenzen, *Einführung in die operative Logik und Mathematik*
  (1955). Source of the admissible/derivable distinction.
- **MIU.** Hofstadter, *Gödel, Escher, Bach* (1979), chapter 1; *Metamath* Appendix D;
  [`miu.mm`](https://us.metamath.org/metamath/miu.mm). The
  [Mathlib archive](https://leanprover-community.github.io/mathlib4_docs/Archive/MiuLanguage/Basic.html)
  has a machine-checked proof that MU is not derivable.

## 5.5 Sequent calculus

- **Gentzen, "Untersuchungen über das logische Schließen", *Mathematische
  Zeitschrift* 39 (1934–35).** English in Szabo (ed.), *The Collected Papers of
  Gerhard Gentzen* (1969). Natural deduction, sequent calculus, and cut elimination.
  Readable.
- **Negri and von Plato, *Structural Proof Theory*.** (Cambridge University Press,
  2001.) Textbook treatment of sequent calculus and cut elimination.
- **Jaśkowski, "On the rules of suppositions in formal logic" (1934).** Natural
  deduction, independently of Gentzen.

## 5.6 History

- **Frege, *Begriffsschrift* (1879).** First formal system in the modern sense.
  `ax-1` is its Proposition 1, p. 26 *(set.mm)*.
- **Hilbert and Ackermann, *Grundzüge der theoretischen Logik* (1928).** The textbook
  behind the name "Hilbert system".
- **Gödel (1930, 1931).** Completeness of predicate calculus; incompleteness.
- **Tarski, "The concept of truth in formalized languages" (1933).** Object language
  and metalanguage.
- **Church (1936), Turing (1936).** Definitions of "mechanical procedure".
- **Kleene (1952).** Fixed much of the notation still in use.

## 5.7 Proof checkers

- **de Bruijn, Automath (1967 onward).** Van Benthem Jutting checked Landau's
  *Grundlagen der Analysis* in it (thesis, 1977).
- **Pollack, "How to believe a machine-checked proof" (1998).** In *Twenty-Five Years
  of Constructive Type Theory*. The de Bruijn criterion, argued carefully.
- **Shankar, *Metamathematics, Machines, and Gödel's Proof*.** (Cambridge University
  Press, 1994; thesis 1986.) Incompleteness checked in the Boyer–Moore prover.
- **Harrison, "Towards self-verification of HOL Light" (IJCAR 2006).**
- **Carneiro, "Models for Metamath" (2016, arXiv:1601.07699)** and **"Metamath Zero"
  (2019, arXiv:1910.10703).** Metamath's formal system stated set-theoretically; a
  verifier designed to be proved correct.



### TMP scratchwork delete/save

- **The de Bruijn criterion.** [pls-lab.org wiki](https://www.pls-lab.org/de-bruijn-criterion),
which cites [The Challenge of Computer Mathematics](https://www.cs.ru.nl/~freek/notes/RSpaper.pdf) (Barendregt and Wiedijk, 2005). 


 represent some type theoretic construction or 

o
So from Gaifman's definition, it's fair to call Metamath a Hilbert-style system carte blanche--I don't know,
this seems to be contentious, but surely we can translate one-to-one to `$a` and `$p` statements, there seems
to be some crazy informal hair-splitting going on here. 
In `set.mm`, Hilbert. 
In other databases, and using others' definitions and not Gaifman's? Logicians seem to say "no." 
My understanding is that even if we made a database to perform sequent calculus, where in some representation
of formulas we had cut elimination and such, then we may say that our individual rules of Metamath substitutions
are Hilbert-style, but that the type of reasoning we're doing in the database is not. 


Then perhaps to say "this database is 
not Hilbert-style" means that as we apply complicated transformation rules to our proof expressions

If our Metamath rules represent things other than theorems,
with complicated transformation rules in order to get to some 



such as transformations of proofs, a Gentzen-style sequent calculus, 


 From a more nuanced take, 
we could take a look at what terms represent, and when Metamath 
I read this to mean, very intentionally, that while it's fair enough to call Metamath a Hilbert-type system, 
this is more directly the case
when the terms (typecode and sequence of math symbols) refer to wffs and theorems or metatheorems, rather than
to more abstract things, for example, `$a metamath-formula proof a = a | id $.` But we don't want to split
hair endlessly about what is or isn't a widget.




Question: How can we formalize Gaifman's notes? Do we naturally have to use a large portion of set.mm?

Question: From our perspective, what is "rule induction" specified in Harper 2012, section 2.4? "If P(J) holds 
whenever P(J1), P(J2), .. P(Jk) of a rule $\frac{J_1\cdots J_k}{J},$ we say $P(J)$ is the inductive conclusion
of the inference." Probably if I ask an LLM, it's just going to say, "oh this is a different type of reasoning not
supported by Metamath," completely missing the point.



The definition of a **Hilbert-style system** is best studied on the 
[wikipedia page](https://en.wikipedia.org/wiki/Hilbert_system), which cites some course notes 
[A Hilbert Type Deductive System for Sentential Logic, Completeness and Compactness](https://www.columbia.edu/~hg17/ViewMathLogic/view1-deductive-system.pdf) (Gaifman 2002). 
Not-so thorough sources: the [Metamath book sections 1.4.3](https://www.mathandcode.com/books/metamath/book/metamath.html#1.4.3-metamath-and-its-philosophy) 
and . 
I also quite like , ch. 2, as well as 

I also take the definition of an 

(TODO: Define a 



a formalization of all of set theory and a formalization of Metamath from inside Metamath

we are [I am] also battling 
fundamental notions of proof, which 

- the de Bruijn critetion. The Challenge of Computer Mathematics (2005), describe the de Bruijn criterion

Things I want to define now: 

- Hilbert proof system
- Inference rule (Harper)


I found the book 