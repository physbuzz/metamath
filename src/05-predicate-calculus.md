---
title: "05 Variables, Binding, and Predicate Calculus"
---

<h1 id="05-predicate-calculus" style="border-bottom: none;">05 Variables, Binding, and Predicate Calculus</h1>

<nav class="nav">
    <span class="activenav"><a href="04-propmm.html">← Previous</a></span>
    <span class="activenav"><a href="index.html">↑ Up</a></span>
    <span class="activenav"><a href="06-setmm.html">Next →</a></span>
</nav>

---

> [!NOTE]
> This is written by AI and has not been reviewed or checked. 
> Working draft. The linked theorems have proofs in `set.mm`; the exercise
> fragments below still need a prepared starting database and checked solutions.
> TODOs mark that work. These fragments are not a standalone `.mm` file.

@toc

# 5 Variables, Binding, and Predicate Calculus

Okay, now for the disjoint variables. In chapter 4 I wanted to get a feel for
classical logic by actually proving things in Metamath. Here I want to do the
same thing with quantifiers, while finally dealing with the variable restrictions
that I could mostly ignore in the propositional exercises. There is some new
terminology to learn, but the plan is to keep bringing it back to particular
strings, particular substitutions, and particular proofs.

One question from chapter 4 is especially useful here: how do we change a
formula deep inside another formula? With quantifiers this becomes a very
concrete question. If I've proved an implication or an equivalence, what theorem
lets me put a universal quantifier around it? And if I want to change the name
of a bound variable, what actually authorizes that change? I want to get far
enough that these are proof steps I can carry out.

I'm also going to use conjunction and equivalence from now on. We could spend
another section constructing their elementary rules, but I think I've got the
flavor of that exercise. The definitions and their supporting proofs are there
to inspect when needed. This chapter will concentrate its exercises on the new
quantifier machinery.

## 5.0 Important Notations, Terminology, and Citations

### 5.0.1 Variables in which language?

There is an easy way to get confused before we've even started: the word
"variable" is doing several jobs. In an ordinary first-order formula, a variable
can occur as an argument of a predicate or be bound by a quantifier. In a
textbook's discussion of those formulas, a metavariable can stand for a whole
formula. Metamath then has its own declared variables and type hypotheses. I
want to keep track of which of these we're discussing, instead of relying on
the typography to tell us.

**Source 1.** The [Metamath book](https://us.metamath.org/downloads/metamath.pdf),
especially §1.4.5, "Metamath and First-Order Logic," and §4.2.4, "The `$d`
Statement." The latter starts on printed page 120. The important point for our
purposes is that the verifier does not have a primitive free-variable or
bound-variable test. Its substitution mechanism and `$d` conditions are used
by an axiom system to control the substitutions that are permitted.

For example, `ph` has type `wff` in our familiar database, while `x` has type
`setvar` in the predicate-calculus portion of `set.mm`. Both are Metamath
variables. An instance of `ph` may be a large formula containing several
`setvar` variables; an instance of `x` must satisfy its own syntax hypothesis.
The declaration `vx $f setvar x $.` belongs to the syntax machinery. It is not
itself a quantified assertion about a mathematical set.

This also explains why a condition involving `x` and `ph` can make sense. We are
restricting which replacements for two Metamath variables can be used together.
The [Proof Explorer's discussion of axioms, schemes, and distinct
metavariables](https://us.metamath.org/mpeuni/mmset.html#distinct) is useful to
read alongside the book here.

### 5.0.2 Free occurrences, bound occurrences, and capture

**Source 2.** Harper's [Practical Foundations for Programming
Languages](https://www.cs.cmu.edu/~rwh/pfpl/), Chapter 1. His treatment of abstract
syntax and binding gives us terminology for talking about these problems
outside a particular Metamath database. The sustained reading of Harper is
going in the separate O5.5 notebook; here I just want enough vocabulary to
describe the examples in front of us.

Consider the familiar formula

$$x=y\ \to\ \forall x\,(x=y).$$

The occurrence of `x` on the left is free, while the occurrence of `x` inside
the quantified equality is bound. The quantifier does not reach back across
the implication. This is why it is useful to talk about *occurrences*: one
written variable name can have different roles in different parts of a formula.

A substitution can change these roles if we're careless. For example, consider
replacing the free `x` in

$$\forall y\,(x=y)$$

by `y`. Simply changing the printed letter gives

$$\forall y\,(y=y).$$

The newly inserted occurrence is now inside the scope of the `y` quantifier.
This is the sort of phenomenon called variable capture. A treatment of
capture-avoiding substitution must say how it handles this situation; in a
named-variable presentation, renaming a bound variable is one way to make the
required room.

Two expressions that differ only by a suitable change of bound-variable names
are called alpha-equivalent in the usual binding terminology. I'll use that
name when discussing the syntax. For the actual predicate-calculus exercises,
we will prove particular logical equivalences using named `set.mm` theorems.
Those are concrete things to check, and they give us something to compare with
the general discussion in Harper.

### 5.0.3 Tarski and the distinct-variable approach

**Source 3.** The Proof Explorer's [history of distinct
variables](https://us.metamath.org/mpeuni/mmset.html#distinct). It credits Tarski
with stating the approach in 1951, with proofs published in 1965. The historical
point I want to remember is the possibility of organizing predicate calculus
around comparatively elementary distinct-variable restrictions, while deriving
the more elaborate behavior within the system.

The comment on [`ax-5`](https://us.metamath.org/mpeuni/ax-5.html) gives a direct
connection to Tarski's system. It asserts

$$\vdash\bigl(\varphi\to\forall x\,\varphi\bigr),$$

with the condition that `x` does not occur in the substituted formula. In
Metamath source, that restriction is written `$d x ph $.`. This is a good
historical example to keep attached to an actual axiom we will use, instead of
remembering only that Tarski did something clever with variables.

There is a tradeoff to notice: making the verifier's primitive operation small
does not make every familiar logical manipulation a primitive operation.
Changing bound variables, specializing a quantified formula, or transporting
an equivalence still needs the relevant assertions and their proofs. That is
the machinery we will borrow and practice using in this chapter.

### 5.0.4 What `$d` asks the checker to do

The exact rule in §4.2.4 of the [book](https://us.metamath.org/downloads/metamath.pdf)
has two parts. When applying an assertion with a required disjoint pair, the
two replacement expressions must have no Metamath variables in common. Also,
every pair consisting of one variable from each replacement must be covered
by the active disjoint conditions in the proof. The second part is how the
restriction is inherited.

For a small example, suppose an assertion requires `$d ph ps $.`, and consider
the replacements `ph` by `x = y` and `ps` by `z = w`. The variables occurring
in the two replacements are disjoint as written. The proof still needs the
cross-pairs `x,z`, `x,w`, `y,z`, and `y,w`. It does not acquire a requirement
that `x` and `y` be distinct from each other from this particular `$d` pair.
We're checking pairs across the two replacements.

If instead both replacements contain `y`, there is an immediate conflict.
Declaring extra pairs cannot repair that overlap. On the other hand, identical
replacements containing only constants do not conflict with this particular
test, because they contain no variables. Their syntax hypotheses still have
to be satisfied, of course. These are checks on substitution data, so we can
practice them before making a large predicate-calculus proof.

The [discussion attached to `19.21v`](https://us.metamath.org/mpeuni/19.21v.html)
also gives a useful terminology distinction: "does not occur" is stronger
than "is not free in." For instance, `x` is not free in `A. x x = x`, but it
certainly occurs there. That formula therefore cannot be used as the
replacement for `ph` in a direct application of `ax-5` with `x` as the bound
variable. There are other theorems for less restrictive situations.

## 5.1 Predicate Calculus in `set.mm`

### 5.1.1 The starting machinery

We'll keep the useful propositional theorems from chapter 4 and borrow the
remaining propositional helpers as needed. The syntax declarations for
equivalence and conjunction are [`wb`](https://us.metamath.org/mpeuni/wb.html)
and [`wa`](https://us.metamath.org/mpeuni/wa.html); their definitions are
[`df-bi`](https://us.metamath.org/mpeuni/df-bi.html) and
[`df-an`](https://us.metamath.org/mpeuni/df-an.html). The syntax and defining
assertions are `$a` statements. Supporting rules such as
[`impbii`](https://us.metamath.org/mpeuni/impbii.html), which assembles an
equivalence from its two directions, retain their `$p` proofs.

The other starting material includes quantifier syntax, the predicate-calculus
axioms needed by the supplied lemmas, and the definition of the existential
quantifier. In particular, [`df-ex`](https://us.metamath.org/mpeuni/df-ex.html)
relates existential quantification to negation and universal quantification.
We can inspect that definition when we reach the existential exercises.

Three assertions worth writing out immediately are
[`ax-gen`](https://us.metamath.org/mpeuni/ax-gen.html),
[`ax-4`](https://us.metamath.org/mpeuni/ax-4.html), and
[`ax-5`](https://us.metamath.org/mpeuni/ax-5.html):

```metamath
$( Fragments: syntax declarations and the rest of the starting database
   are omitted here. $)
${
  ax-gen.1 $e |- ph $.
  ax-gen $a |- A. x ph $.
$}

ax-4 $a |- ( A. x ( ph -> ps ) ->
             ( A. x ph -> A. x ps ) ) $.

${
  $d x ph $.
  ax-5 $a |- ( ph -> A. x ph ) $.
$}
```

Notice that `ax-gen` and `ax-5` have different forms. Generalization is a rule
taking an established assertion to its universally quantified form. The
unrestricted closed formula `ph -> A. x ph` is not thereby available; `ax-5`
provides it with a restriction. This is one place where the distinctions from
chapter 4 are going to matter. When reasoning under a condition, keeping that
condition as an explicit antecedent will make the relevant restrictions visible.

**TODO: prepare the exercise database.** Include the proved helpers needed by
the selected exercises, including specialization and bound-variable change.
The three displayed axioms are a preview of some tools, not the complete
axiom list for everything below. Each target should have a checked solution
using the supplied material before it becomes an assigned exercise.

### 5.1.2 A first proof with disjoint variables

Start with an instance of `ax-5` whose restriction we can inspect without much
other proof work:

```metamath
${
  $d x z $.
  $d y z $.
  ax5-example $p |- ( x = y -> A. z x = y ) $= ? $.
$}
```

Here `ax5-example` is a local exercise label. The intended proof is simply an
application of the existing axiom, together with the syntax proof for its
formula. Write down what replaces `ph` and what replaces the axiom's `x`.
Then write down the variables in each replacement and check both required
cross-pairs.

After completing the proof, temporarily remove one of the two `$d` declarations
and ask the checker to verify it again. Read the diagnostic. Restore the
declaration, and then consider what would happen if the quantifier bound `x`
instead of `z`. These two failures have different causes: one lacks an inherited
pair; the other introduces a variable shared by the replacements. The
[Proof Explorer](https://us.metamath.org/mpeuni/mmset.html#distinct) discusses
this inheritance issue with an analogous instance of `ax-5`.

#### Hints and my answers

Assign `ax-5` to the target. The remaining work should be syntax construction.
For the disjointness check, the formula replacement contains `x` and `y`, while
the bound-variable replacement contains `z`. There is no need to add `$d x y $.`
for this application.

TODO: add the completed proof and the actual checker messages after working
through the exercise. It would be useful to keep both failure messages here.

### 5.1.3 Putting a quantifier around an implication or equivalence

Now for the question about manipulating something inside a formula. The rules
[`alimi`](https://us.metamath.org/mpeuni/alimi.html) and
[`albii`](https://us.metamath.org/mpeuni/albii.html) let us carry an established
implication or equivalence under a universal quantifier:

$$\frac{\vdash(\varphi\to\psi)}
        {\vdash(\forall x\,\varphi\to\forall x\,\psi)}
  \quad\texttt{alimi},$$

$$\frac{\vdash(\varphi\leftrightarrow\psi)}
        {\vdash(\forall x\,\varphi\leftrightarrow\forall x\,\psi)}
  \quad\texttt{albii}.$$

As in chapter 4, the displayed rules omit their syntax hypotheses. Neither
rule requires a `$d x ph $.` condition. Their premises are established
implications or equivalences; this is different from treating an arbitrary
formula as true only for some temporarily chosen value of `x`.

```metamath
${
  alimi.1 $e |- ( ph -> ps ) $.
  alimi $p |- ( A. x ph -> A. x ps ) $= ? $.
$}

${
  albii.1 $e |- ( ph <-> ps ) $.
  albii $p |- ( A. x ph <-> A. x ps ) $= ? $.
$}
```

The first proof should be a small exercise with `ax-gen` and `ax-4`. The second
can use the supplied equivalence machinery. I want to recognize this pattern
well enough to use it later: prove the relation between the inner formulas,
then apply the theorem that transports it through the surrounding construction.

#### Hints and my answers

For `alimi`, start with modus ponens and use `ax-4` as the implication. Its
antecedent asks for a universally quantified version of the given hypothesis.
For `albii`, one route is to obtain the two implications, use `alimi` on each,
and put the resulting implications together with `impbii`. Supply the helpers
for extracting the two directions of an equivalence.

TODO: add my solutions and, if useful, compare them with the Proof Explorer's
shorter proof using its existing equivalence lemmas.

### 5.1.4 Keeping an antecedent while quantifying

The next target is [`alrimiv`](https://us.metamath.org/mpeuni/alrimiv.html):

```metamath
${
  $d x ph $.
  alrimiv.1 $e |- ( ph -> ps ) $.
  alrimiv $p |- ( ph -> A. x ps ) $= ? $.
$}
```

This is a useful step towards reasoning under a shared antecedent. The
antecedent remains `ph`, while the conclusion gets quantified. The restriction
is on `ph` and `x`; `ps` is allowed to contain `x`. Compare the conclusion with
that of `alimi`, and identify exactly where the quantifier has disappeared.

The suffix `v` is worth remembering. The database sometimes uses it for a
version of a theorem with a distinct-variable condition, as explained in the
comment on [`19.21v`](https://us.metamath.org/mpeuni/19.21v.html). Later we will
encounter versions with explicit nonfreeness hypotheses. For now, the stronger
syntactic condition gives us a manageable starting point.

#### Hints and my answers

Use `syl`, with `A. x ph` as the intermediate formula. One branch should use
`ax-5`; the other should use `alimi`. Before looking at any proof details,
identify which branch needs `$d x ph $.`.

TODO: add the completed proof. Also record an example of a proposed
substitution that would violate its restriction.

### 5.1.5 Vacuous quantifiers and existential quantification

A quantifier whose variable does not occur in the formula gives us two more
useful targets, [`19.3v`](https://us.metamath.org/mpeuni/19.3v.html) and
[`19.9v`](https://us.metamath.org/mpeuni/19.9v.html):

```metamath
${
  $d x ph $.
  19.3v $p |- ( A. x ph <-> ph ) $= ? $.
  19.9v $p |- ( E. x ph <-> ph ) $= ? $.
$}
```

For the universal case, the two directions have different justifications.
`ax-5` introduces the quantifier under the stated restriction. A supplied
specialization theorem removes it. We'll use the existing specialization
machinery here; deriving all of it from the primitive predicate-calculus
axioms can be a separate exercise if I decide I want one.

The existential definition in `set.mm` is

$$\vdash\bigl(\exists x\,\varphi\leftrightarrow
                     \neg\forall x\,\neg\varphi\bigr)
\quad\texttt{df-ex}.$$

This gives us a connection to the negation rules from chapter 4. Another
natural target is [`eximi`](https://us.metamath.org/mpeuni/eximi.html):

```metamath
${
  eximi.1 $e |- ( ph -> ps ) $.
  eximi $p |- ( E. x ph -> E. x ps ) $= ? $.
$}
```

The statement has the same overall pattern as `alimi`. As a small application,
use it with a conjunction-elimination theorem to obtain an existentially
quantified implication from `ph /\ ps` to `ph`. The useful point is seeing
the old propositional result become an input to the new quantifier rule.

#### Hints and my answers

For `19.3v`, use `impbii` and identify the two directions before doing any
substitutions. For `eximi`, a route through the definition uses contraposition,
`alimi`, and contraposition again; the supplied existential helpers may package
some of those steps. For `19.9v`, compare the existential definition with the
vacuous universal quantifier applied to a negated formula.

TODO: choose the exact helper list before assigning the existential proofs.
The application of `eximi` can remain a short independent exercise even if
its general proof is supplied.

### 5.1.6 Rearranging quantified formulas

Two slightly larger targets are
[`19.26`](https://us.metamath.org/mpeuni/19.26.html) and
[`19.21v`](https://us.metamath.org/mpeuni/19.21v.html):

```metamath
19.26 $p |- ( A. x ( ph /\ ps ) <->
              ( A. x ph /\ A. x ps ) ) $= ? $.

${
  $d x ph $.
  19.21v $p |- ( A. x ( ph -> ps ) <->
                 ( ph -> A. x ps ) ) $= ? $.
$}
```

For `19.26`, the first direction should look like two applications of the
earlier implication-lifting rule, followed by conjunction machinery. Its
converse requires a suitable supplied quantifier/conjunction helper. This is
a good place to use the propositional library without making its elementary
conjunction rules into another long assignment.

For `19.21v`, look at the antecedent that stays outside the quantifier. The
restriction resembles the one in `alrimiv`, and we should be able to explain
why it belongs there. Notice that `19.26` has no corresponding distinctness
condition on `x` and either formula.

#### Hints and my answers

For `19.26`, work backwards with `impbii`. In the forward direction, get the
two conjuncts separately using `alimi` with `simpl` and `simpr`. A supplied
rule such as `alanimi` handles the other direction from the appropriate
propositional implication.

**Placeholder: `19.21v`.** Prepare a short guided proof using the existing
helpers, then write hints for that particular starting file. For now, read its
statement, its `$d` condition, and the proof page. It is a target for this
chapter, not a request to reconstruct every theorem that its proof references.

### 5.1.7 Changing the bound variable

Finally, let's do an actual bound-variable change. A small concrete target is

$$\vdash\bigl(\forall x\,(x=z)\leftrightarrow
              \forall y\,(y=z)\bigr),$$

with `x`, `y`, and `z` pairwise disjoint. We'll use the supplied theorem
[`cbvalvw`](https://us.metamath.org/mpeuni/cbvalvw.html), which has premise

$$\vdash\bigl(x=y\to(\varphi\leftrightarrow\psi)\bigr)$$

and conclusion

$$\vdash\bigl(\forall x\,\varphi\leftrightarrow
              \forall y\,\psi\bigr),$$

subject to `$d x y $.`, `$d x ps $.`, and `$d y ph $.`.

The equality theorem [`equequ1`](https://us.metamath.org/mpeuni/equequ1.html)
supplies the particular premise we need:

$$\vdash\bigl(x=y\to(x=z\leftrightarrow y=z)\bigr).$$

**Placeholder: equality preparation.** Inspect `equequ1` and either supply its
proof or make it a short preliminary exercise with the relevant equality
lemmas already available. The main exercise is the application of the
bound-variable theorem:

```metamath
${
  $d x y z $.
  rename-equality $p |- ( A. x x = z <-> A. y y = z ) $= ? $.
$}
```

The name `rename-equality` is another local exercise label. This should be a
small proof once the two supporting theorems are available. What I want to
understand is how their conditions fit together, including the restriction
that protects `z` while the bound name changes.

#### Hints and my answers

Assign `cbvalvw` to the target. Its formula variables become `x = z` and
`y = z`. Write out the inherited pairs from each of its three `$d` conditions;
after removing repetitions, they are exactly the three pairs declared by
`$d x y z $.`. The remaining logical premise is supplied by `equequ1`.

TODO: add the proof. Then write down what has been proved: this particular
equivalence, under these particular substitution restrictions. A general
statement about an alpha-renaming procedure would need a representation of
formulas and of that procedure. That is a later project.

## 5.2 A Small Visit to `peano.mm`

This can be the chapter's side excursion, in the spirit of the other databases
in chapter 4. The source is
[`peano.mm`](https://github.com/metamath/set.mm/blob/develop/peano.mm). I want to
look at its syntax and arithmetic axioms, compare its handling of variables
with what we've just used, and eventually do a couple of small arithmetic
proofs. The opening comments are also something to return to alongside
Harper's discussion of binding.

**Placeholder: a small arithmetic exercise file.** Choose two or three targets
and supply the logical and equality helpers they require. If an induction
exercise such as `0 + x = x` is included, its base case, successor step, and
application of the induction machinery should all be made explicit. The
statement alone does not tell us how much supporting work the exercise needs.

There are several different projects nearby: proving arithmetic theorems in
this database, working with natural numbers in `set.mm`, and representing an
arithmetic deductive system in order to prove statements about its derivations.
For this excursion I mean the first one. The others can stay on the list
without becoming prerequisites for finishing this chapter.

TODO: decide whether this visit belongs in the first pass through O5. If the
prepared exercises turn out to be a substantial detour, keep the source and
questions here and return to them after the set-theory chapter.

## 5.3 Notes, Reflections, and TODO

The main question I want to come back to is the one about changing a formula
inside another formula. We now have examples where an implication or
equivalence can be transported through a quantifier. I'd like to recognize
when this is the right approach, instead of trying to manipulate a substring
as though the verifier had a general rewrite command built into its logic.

There is a related distinction between carrying out a proof step and proving
something about a general proof transformation. In this chapter I can write a
particular bound-variable change and have the checker accept it. In the later
metamathematics chapter I want formulas, substitutions, and derivability to be
mathematical objects we can quantify over. That will let us formulate a much
wider claim precisely. For now, I can keep an explicit list of the claims I
would eventually like to state.

TODO: add personal notes after the exercises. Which `$d` failures were
surprising? Which helper made an apparently complicated proof easy? Did it
help to write the intended intermediate formula before asking the proof
assistant to fill in the details? These should be observations from actually
working the problems; there is no need to manufacture conclusions in advance.

The separate O5.5 reading notebook can hold the longer work through Harper's
first three chapters and Gaifman's notes. It should be useful to compare
Harper's language with the operations we've just performed, while keeping a
record of the parts that still need formalization.

## 5.4 Quiz Questions

These questions are meant to test the terminology and the mechanics that the
proof exercises use. The answers below are short sketches to revise after
working through the chapter.

### Question 1

In `( x = y -> A. x x = y )`, which occurrences of `x` and `y` are free, and which
are bound? Why is it more precise to ask about occurrences than simply to
classify each variable name as free or bound?

#### Answer sketch

The `x` in the left equality is free, and the `x` in the right equality is
bound by `A. x`; the `x` written immediately after `A.` names the binder.
Both equality occurrences of `y` are free. A single name can
occur in different scopes; the binding depends on the occurrence's location.

### Question 2

An assertion requires `$d ph ps $.`. We replace `ph` by `x = y` and `ps` by
`z = w`. Which inherited pairs are needed? Why isn't the fact that these are
four differently written letters enough?

#### Answer sketch

The cross-pairs are `x,z`, `x,w`, `y,z`, and `y,w`. The checker needs the
corresponding active restrictions. The distinct spellings by themselves do
not record which later substitutions the assertion permits.

### Question 3

Explain why `$d x y $.` is different from `|- -. x = y`. Also explain why
`$d x ph $.` is stronger than saying that `x` is not free in the formula.

#### Answer sketch

The first is a restriction on substitutions for Metamath variables; the second
is a mathematical assertion of inequality. For the formula case, nonoccurrence
excludes bound occurrences too. `A. x x = x` is a concrete example in which
`x` occurs but is not free.

### Question 4

What is variable capture? Describe what goes wrong with the naive replacement
of free `x` by `y` in `A. y x = y`, and explain the role that changing the bound
name can play in avoiding it.

#### Answer sketch

The inserted `y` falls within the scope of the existing `A. y` binder and
becomes bound. A suitable change to a fresh bound name can preserve the role
of the inserted occurrence. The admissibility of the change must be handled
by the chosen syntax rules or, in our exercises, by an appropriate theorem.

### Question 5

What is the historical connection between Tarski's work and Metamath's
distinct-variable approach? Name the source used for the dates.

#### Answer sketch

The Proof Explorer's history credits Tarski with stating the approach in
1951 and publishing proofs in 1965. The relevant idea is organizing an
axiomatization using distinct-variable conditions rather than requiring the
usual free-variable and proper-substitution machinery as primitive notions.

### Question 6

Compare `ax-gen` with `ax-5`. Why can't we simply turn the former into an
unrestricted theorem `|- ( ph -> A. x ph )`?

#### Answer sketch

`ax-gen` takes an established assertion as a premise and universally quantifies
it. The closed implication has a different logical claim. `ax-5` supplies that
implication under a disjoint-variable restriction, and the `ax-gen` commentary
explicitly warns that its unrestricted closed form need not hold.

### Question 7

Which tool would you look for if you had proved `ph <-> ps` and wanted
`A. x ph <-> A. x ps`? What changes if you instead have `ph -> ps` and want
`ph -> A. x ps`?

#### Answer sketch

The first is the pattern of `albii`. The second is the pattern of `alrimiv`,
whose disjointness condition constrains `ph` and `x`. In the first case both
sides are quantified; in the second the antecedent remains outside.

### Question 8

In the `rename-equality` exercise, why do we need to protect `z` as well as
distinguish `x` and `y`? What would a general theorem about alpha-renaming say
beyond this particular checked equivalence?

#### Answer sketch

Substituting the two equality formulas into `cbvalvw` produces the additional
pairs `x,z` and `y,z`. A general theorem about a specified renaming procedure
would quantify over represented expressions and the procedure's inputs or
outputs. This exercise supplies one checked instance using an existing rule.
