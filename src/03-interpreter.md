---
title: "03 Writing a Metamath Interpreter (Megill ch4)"
---

<h1 id="03-interpreter" style="border-bottom: none;">03 Writing a Metamath Interpreter (Megill ch4)</h1>

<nav class="nav">
    <span class="activenav"><a href="02-sicp-logic.html">← Previous</a></span>
    <span class="activenav"><a href="index.html">↑ Up</a></span>
    <span class="activenav"><a href="04-propmm.html">Next →</a></span>
</nav>

[Read in html](book/metamath.html#the-metamath-language) &nbsp;|&nbsp; [Read in pdf](book/metamath.pdf#page=129)

# Stuff I Learned from Writing an Interpreter

On the first pass, I ignored disjoint variables and compressed proofs. The 
first task is to fill in the proof database, and second to actually check
the proofs and perform the substitutions. Third and fourth, we add back
disjoint variables and compressed proofs.

I generally have had nothing but bad luck trying to be clever with interpreters,
so I wrote it in a boring, stateful, verbose way. Lots of switch statements
that I can make clever later -- which I won't, because it's a learning project
and I'm going to use the actualy metamath project for a real application.

## Misc stuff I was confused about (SCRATCHWORK / TODO):

"Symbol" or "math symbol" refers to constants defined with `$c ... $.` 
or variables defined with `$v ... $.`

`$a` and `$p` statements are **assertions**, which means that they may have
mandatory hypotheses which, when checking a proof, must be satisfied by expressions
popped from the proof stack.

`$f` and `$e` statements are **hypotheses**, when checking a proof they do not 
have any mandatory hypotheses that must be satisfied.

However, importantly, when an assertion has a essential hypothesis that must be
satisfied, we also must look at all the variables referenced by that essential 
hypothesis and require that they're satisfied by floating hypotheses. 

For example, in the very silly example below where I prove turnstile in a silly system,
the axiom `remove_variable` has two mandatory hypotheses: One for the essential hypothesis,
and one to satisfy the variable `b` inside `stmnt_b2`. Also note: how do we know that 
`b` will only be satisfied by something (a list of math symbols) on the proof stack of the 
form `term $1`? It's because `b` is only allowed to be inside one floating hypothesis definition.

```metamath
$v a b c $.
$c term |- V $.

term_a $f term a $.
term_b $f term b $.
term_c $f term c $.

${
    stmnt_b2 $e |- b $.
    remove_variable $a |- $.
$}

chaos_axiom $a |- c $. 

proof_of_turnstile $p |- $= term_a term_a chaos_axiom remove_variable $.
```

from atomfighter10101: 
$f stuff much better. Its more a computer science thing than a logic thing. It's for assigning types to the variables as guards to prevent incorrect substitution. It's fair to call it a hyp. For example, in Men(x)-> Mortal(x). The Men(x) acts as a type guard. The thing that replaces x must be a Man


Note: My parser has exploded in complexity, while [David Wheeler's Python implementation](https://github.com/david-a-wheeler/mmverify.py/blob/master/mmverify.py).

"Each label token must be unique, and no label token may match any math symbol token." -- I explicitly ignore this. We can have a variable v and a label v. This is silly, but like, it's just
something to be discouraged in real proof databases and ignoring it makes it easier to parse.


## Pass 1

First it's natural to write a parser and proof checker with no support for disjoint variables
or compression. This is just to get the lay of the land, write stupid inefficient algorithms,
and show that we know what's going on. The output of my program in  `#define SUPER_ULTRA_VERBOSE` mode is shown in [this github file](https://github.com/physbuzz/metamath/blob/master/cpp/ch2_theorem_parsing.txt), which is nice to let us know we're doing correct things and using terms correctly, even if the parser and checker certainly have some bugs in them, given how sloppy my coding style was.

Pass 1 was completed on Nov 6, 2026. 

### Writing the parser

When writing the parser, I found it easiest to distinguish between the following enum classes and structs. If you're 
writing your own parser, starting from these terms isn't the worst idea. 
There are a few things I had to jump around the Metamath book to figure out, and I found the categories to distinguish between given in the book
weren't exactly the same as the categories that were useful in the code.

First, an enum class corresponds to the various important
token types we have, among `$( $) $[ $] ${ $} $c $v $f $e $d $a $p $. $=`. So `TokenType::AXIOM` corresponds to `$a`. 
Errors are `TokenType::SNULL` and anything that falls through
is `TokenType::TOKEN`. It was tempting to call these "Statements" at first. 

Next, a `Symbol` is a constant or a variable, ie. a "math symbol" in the Metamath book. Easy enough:
```cpp
struct Symbol {
    string label;
    SymbolType symbolType;
};
```

Next, `StatementType` and the `Statement` struct actually
correspond only to *labeled* statements: floating or 
essential hypotheses, and axioms or proofs. 
`SymbolID` and `StatementID` are just `size_t`s that point into the proof database.

```cpp
struct Statement {
    string label;
    StatementType statementType;
    SymbolID typecode;
    vector<SymbolID> symbols;
    vector<StatementID> statements;
    vector<StatementID> mandatory;
};
```
The label and typecode are always filled; and generally
`symbols` fills anything before the `$=` and `statements`
stores anything after it. And of course while parsing we have
to enforce other requirements: a floating hypothesis can only have one symbol stored, and that symbol must be a variable. A floating, essential, or axiom must not have any statements. And a few other constraints, like the symbols
and statements being active.

The mandatory hypothesis list also takes care to construct. 
I used a `std::set<StatementID>` to test membership and was lazy and used
a whole bunch of expensive lookups: 
for every variable in `symbols`, and every variable in every active
essential hypothesis, we traverse the whole list of active statements to find a floating hypothesis defining that symbol, and add it to the set. After that's finished, we traverse the list of 
active statements again, test membership in the set, and if so
push it to the list of mandatory statements. This ensures the correct order.

The proof database is then simple:

```cpp
struct ProofDatabase {
    vector<Symbol> symbols;
    vector<Statement> statements;
};
```

Note that just given the info of the proof database, you cannot, at proof-check time, determine which statements
and symbols are active. This was a bit disappointing for
me, I tried to figure out a Lisp style stack of frames at 
first, but I couldn't get it to work and ended up figuring out
a lot of the validity at parse time. 

My super-stateful parser therefore ended up with this structure:

```cpp
struct ParserState {
    bool errorState;
    bool commentSkip;
    string currentLabel;
    Statement currentStatement;

    vector<SymbolID> symbolStack;
    vector<int> symbolStackLevels;
    vector<StatementID> statementStack;
    vector<int> statementStackLevels;

    //NONE, VARIABLES, CONSTANTS, STATEMENT
    CurrentParserState parserState;

    // FLOATING, ESSENTIAL, AXIOM, PROOF, 
    StatementType currentStatementType;

    //TYPECODE, SYMBOLS, PROOF
    ParserStatementState currentStatementState;
};
```

The stacks are the things that keep track of the active symbol ids, and when we leave a scope we pop an element from `fooStackLevels` then `std::vector::resize` the `fooStack` array to the new length. I could add more state to make the mandatory hypothesis testing faster.

Uhh yeah that's pretty much it. I didn't find it to be 
obvious if this would work; you know, there are always 
questions about what datatypes to use, whether to store each
data type in its own array, and so on. This works well enough and it
took me a few passes to wind up at these data structures.

### Writing the proof checker

TODO: 

- List out the structs that I found useful.
- List out the unification
- List out things I'd change (one place I needed StatementType::FLOATING? To me this signifies that my struct definitions could be better). Separating out into more files is a given.

##  Future work

Disjoint variables, and proof compression are the next big things to implement. However it doesn't really make sense to implement them before we're doing proofs that need them. So let's 
study propositional calculus proofs a little bit before getting to
disjoint variables. 





## suggested questions

### Question

In Metamath, what is the difference between a math symbol and a statement label? Can a label have the same name as a
math symbol? If a hypothesis is in a block, can we reuse the label of a hypothesis after its block has closed?

#### Answer

"Math symbol" refers to either a constant or variable, which must be declared with `$c` and `$v`.

Labels name the statements `$f $e $a $p` so we can refer to them in proofs.

Labels must be unique throughout the database, even when the statements they label are no longer active. 
Closing a block does not let us reuse its hypothesis labels. A label also can't share a name with any constant
or variable.

### Question

In Metamath, what does it mean for a math symbol to be active? Can symbols be declared again?

#### Answer

Math symbols are only constants or variables, and constants can only be declared at the topmost level of the proof
database, so constants are simple: they are active and can be used from the point they're declared to the end of the file.

A variable is active from the point it's declared to the end of its block. Inactive variables may be redeclared (see
[megill ch4](book/metamath.html#redeclaration-of-math-symbols)). Variables are also special because if they're used in
any statement, they must have a floating hypothesis associated with them defining the typecode, and the typecode of
the variable may not change upon redeclaration.

### Question

In the following database, which statements go inactive at the end of the block `$}`? 
What are `pass`'s essential hypotheses, and what does applying it in a proof outside of the block do?

```mm
$c term |- $.
$v t $.
ft $f term t $.
${
    $v x $.
    fx $f term x $.
    h $e |- x $.
    pass $a |- x $.
$}
```

#### Answer

Hypotheses `$f` and `$e` are active from their declaration until the end of the block. Assertions `$a` and `$p`
never go inactive.

There is no hitch to applying the axiom `pass`. It requires two mandatory hypotheses to be satisfied, so for example
if the proof stack contains the following:

```mm
term foo
|- foo
``` 

This would satisfy the two mandatory hypotheses of `pass` without issue.

### Question

In Metamath, can a variable have two active floating hypotheses? Can blocks shadow variables?

#### Answer

No on both counts. An active variable must have a single active floating hypothesis by the time it's used in a later
statement. We might think we could shadow a definition like this:

```mm
$v x $. $c term wff $.
tx $f term x $.
$( statement using x as a term here $)
${
    $v x $.
    wffx $f wff x $.
    $( statement using x as a wff here $)
$}
```

but this is not allowed. So scoping follows special semantics in Metamath that might not be familiar from other languages.

### Question

How do we determing a Metamath assertion's mandatory variables, and mandatory hypotheses and their order? 

How do we determine its 
optional hypotheses, and what are optional hypotheses? 

#### Answer

The mandatory variables of an assertion are any variables that occur in its list of math symbols or in any active
essential hypotheses. In the case of a proof, this *does not* include variables merely because they are referenced by
the statements after the `$=` sign. "Mandatory variable" is a term not introduced 'til
[Megill 4.1.3](book/metamath.html#4.1.3-basic-syntax).

The mandatory hypotheses of an assertion are all active essential hypotheses, and all the floating hypotheses
that define the typecode of each mandatory variable. They are ordered in the order that they appear in the database.

Optional hypotheses are remaining active floating hypotheses.
A theorem's proof may use them, but they do not need to be referred to later.
Every active essential hypothesis is mandatory; there are no optional essential hypotheses.

In this example, `th` has mandatory variable `P`, mandatory hypotheses `wp h` (in that order), and optional
hypothesis `wq`.

```mm
$c wff |- $. $v P Q $.
wp $f wff P $.
${
    wq $f wff Q $.
    h $e |- P $.
    th $p |- P $= h $.
$}
```

### Question

In the following Metamath database, what are the mandatory hypotheses of `rule`, in order? Give the
hypotheses in the order they must be satisfied on the proof stack, from bottom to top.

```mm
$c wff |- ( ) -> $.
$v x y z $.
wx $f wff x $.
hx $e |- x $.
wy $f wff y $.
wz $f wff z $.
hy $e |- y $.
rule $a |- ( x -> x ) $.
```

#### Answer

The mandatory hypotheses are, in order, `wx hx wy hy`. This means that the proof stack needs to have the following 
form at the time `rule` is applied:

```mm
wff x
|- x
wff y
|- y
```

### Question

In Metamath, does an active essential hypothesis still become mandatory if it doesn't occur in a `$p`
statement's proof? What about if it doesn't share any math symbols with an `$a` statement?

#### Answer

Yes, in both cases. Active essential hypotheses are always mandatory hypotheses, even if the proof doesn't use them.
We still apply the same procedure when checking the proof, and such cases might be especially trivial but 
we still pop symbols off the proof stack and compare the symbols in the proof stack with the symbols in the 
mandatory hypothesis for consistency.

### Question

*Note:* This question was AI generated and has not been reviewed.

In the following Metamath database, how many mandatory hypotheses does `remove_variable` have? Trace the proof of
`proof_of_turnstile`. How many mandatory hypotheses does that theorem have, even though its proof uses `term_a`?

```mm
$c term |- $.
$v a b c $.
term_a $f term a $.
term_b $f term b $.
term_c $f term c $.
${
    stmnt_b2 $e |- b $.
    remove_variable $a |- $.
$}
chaos_axiom $a |- c $.
proof_of_turnstile $p |- $= term_a term_a chaos_axiom remove_variable $.
```

#### Hint

Work out the mandatory hypotheses of `remove_variable` and `proof_of_turnstile` separately. In the proof, keep track
of which copy of `term a` is consumed by `chaos_axiom`.

#### Answer

`remove_variable` has two mandatory hypotheses, `term_b stmnt_b2`. The variable `b` occurs in its essential hypothesis,
so we need `term_b` even though `b` does not occur in the conclusion. An expression consisting only of a typecode,
such as `|-`, is allowed.

The proof proceeds as follows:

1. The two `term_a` steps push two copies of `term a`.
2. `chaos_axiom` consumes the top `term a`, replacing `c` by `a`, and pushes `|- a`.
3. The stack now contains `term a` followed by `|- a`.
4. `remove_variable` consumes these two entries. The first gives the replacement `b := a`, and the second matches
   `|- b` after that substitution. We push the conclusion, `|-`.

`proof_of_turnstile` has no mandatory hypotheses. Its expression contains no variables, and no essential hypotheses
are active at its declaration. Its active floating hypotheses are optional, and the proof uses `term_a`. A later proof
can apply `proof_of_turnstile` without supplying any inputs for these internal steps.

### Question

*Note:* This question was AI generated and has not been reviewed.

In Metamath, which statement labels may occur in an uncompressed proof? Can a theorem refer to itself, to a statement
later in the file, or to a hypothesis whose block has closed? If we parse the entire database before checking proofs,
is finding the label in the database enough?

#### Answer

A proof may refer to hypotheses active at the theorem's declaration, including optional floating hypotheses, and to
earlier assertions. It cannot refer to the theorem itself, to later statements, or to inactive hypotheses. An earlier
assertion remains available even if its block has closed.

Finding the label is not enough. If parsing and proof checking are separate passes, we must either check these
restrictions while parsing or retain the information needed to check them later. The theorem's position and scope
matter; a statement's existence somewhere in the database does not make it available to that proof.

### Question

*Note:* This question was AI generated and has not been reviewed.

In Metamath, what does the verifier do when a proof step applies an axiom or a previously proved theorem with $n$
mandatory hypotheses? Describe how to obtain the replacement rules and check the hypotheses, including what happens
when $n=0$.

Note: Ignore disjoint-variable restrictions for this question.

#### Answer

First, there must be at least $n$ entries on the proof stack. The last mandatory hypothesis corresponds to the top
entry, the second-to-last to the entry below that, and so on. We cannot search farther down the stack for a match.

For each floating hypothesis, the corresponding entry must begin with the same typecode. Everything after that
typecode is the replacement for the hypothesis's variable. The typecode itself is not part of the replacement.

Next, apply these replacement rules to the essential hypotheses. Each resulting expression must match its
corresponding stack entry exactly. We do not obtain new replacement rules from the essential hypotheses.

We pop the $n$ entries, apply the same replacements to the assertion's expression, and push the result. Entries below
those $n$ inputs stay on the stack. If we pop entries before doing the checks, we must keep their contents available
for computing and checking the substitutions.

When $n=0$, we pop nothing and push the assertion's expression unchanged. Applying a proved theorem uses its mandatory
hypotheses and conclusion in the same way as applying an axiom; we do not rerun its proof on the current proof stack.

### Question

*Note:* This question was AI generated and has not been reviewed.

In Metamath, suppose an assertion application gives us the following replacement rules. What does `wff ( P -> Q )`
become? Do we also replace the `P` and `Q` inside the expression that replaces `P`?

```text
P := ( Q -> P )
Q := R
```

If the next proof step is the active floating hypothesis `wp $f wff P $.`, what does it push?

Note: Assume the required floating hypotheses have been satisfied and there are no disjoint-variable restrictions.

#### Answer

The result is `wff ( ( Q -> P ) -> R )`. Substitution is simultaneous: we replace each variable in the original
expression, without repeating the substitution inside the expressions we insert. The `Q` and `P` inside the
replacement for `P` stay as written. It is fine for a replacement to contain the variable being replaced.

The next `wp` step pushes `wff P`, unchanged. The replacement rules belong to one application of an assertion; they do
not change the stored hypotheses or assign permanent values to variables. A later assertion application gets its own
replacement rules from the inputs supplied for that application.

### Question

*Note:* This question was AI generated and has not been reviewed.

In Metamath, suppose an assertion has the following mandatory hypotheses and conclusion:

```mm
wp $f wff P $.
h $e |- ( P -> P ) $.
rule $a |- P $.
```

We try to apply `rule` to the following proof stack, listed from bottom to top. Does it work? If we change `B` to `A`,
does it work then? What if we also change the first entry's typecode from `wff` to `term`?

```text
wff A
|- ( A -> B )
```

Note: `A` and `B` are distinct constants. Assume all symbols are declared and the displayed entries have been
constructed by earlier steps in a larger database. Only the two hypotheses shown are mandatory for `rule`.

#### Answer

The original application fails. The floating hypothesis gives `P := A`, so the essential hypothesis requires
`|- ( A -> A )`. That does not match `|- ( A -> B )`. We cannot choose a different replacement for the second
occurrence of `P` to make it work.

Changing `B` to `A` makes the application succeed, leaving `|- A` on the stack.

Changing the first typecode to `term` makes it fail again. That entry must match the typecode `wff` of `wp`. The
verifier does not convert it to a `wff`, even if a proof of `wff A` is available elsewhere in the database.

### Question

*Note:* This question was AI generated and has not been reviewed.

In Metamath, an axiom has expression `wff ( P -> Q )` and mandatory hypotheses `wp $f wff P $.` followed by
`wq $f wff Q $.`. We apply it with `wff A` followed by `wff B` on the proof stack. What happens if we swap the
hypothesis declarations in the database without changing the proof?

Note: `A` and `B` stand for distinct symbol sequences whose required constructions have already been supplied.

#### Answer

Originally, we get `P := A` and `Q := B`, so the result is `wff ( A -> B )`.

After swapping the declarations, the mandatory order is `wq wp`. The same stack now gives `Q := A` and `P := B`, so the
result is `wff ( B -> A )`. Both typecodes still match, so this application can succeed while producing the wrong
expression for the rest of the proof. A later hypothesis check or the final theorem check may then fail.

The order comes from the hypothesis declarations, not from the order of variables in the axiom's expression.

### Question

*Note:* This question was AI generated and has not been reviewed.

In Metamath, can we replace a variable with an empty sequence of math symbols? Is the following proof valid, and what
replaces `x` when we apply `wrap`?

```mm
$c term ( ) $.
$v x $.
fx $f term x $.
empty $a term $.
wrap $a term ( x ) $.
th $p term ( ) $= empty wrap $.
```

#### Answer

Yes. `empty` has no mandatory hypotheses, so it pushes the one-symbol expression `term`. When applying `wrap`, we
compare this with the floating hypothesis `term x`. The typecodes match, and there is nothing after the typecode, so
`x` is replaced by the empty sequence.

The result is `term ( )`, exactly what `th` claims. The proof is valid. The expression on the stack is not empty;
it is the replacement for `x` that is empty.

### Question

*Note:* This question was AI generated and has not been reviewed.

In Metamath, what conditions must the proof stack satisfy when a proof is finished? Suppose `a $a |- A $.` and
`b $a |- B $.` have no mandatory hypotheses. Which of the proof sequences `a`, `a b`, and `b` proves `|- B`?

Note: Assume all symbols are declared, `A` and `B` are distinct constants, and each proof starts with an empty stack.

#### Answer

The stack must contain exactly one expression, and that expression must match the theorem's expression, including its
typecode. Only `b` succeeds.

- `a` leaves one entry, but it is `|- A`, which does not match the theorem.
- `a b` leaves two entries. The top entry matches, but the extra entry makes the proof invalid.
- `b` leaves exactly one entry, `|- B`.

It is not enough that the desired expression occurred somewhere during the proof, or that it is the top entry at the
end. We must finish with just that expression on the stack.

### Question

*Note:* This question was AI generated and has not been reviewed.

In Metamath, is the following a legal axiom? Does the verifier require a separate construction showing that the
expression after `|-` is a well-formed formula?

```mm
$c |- ( ) -> $.
odd $a |- ( -> ) $.
```

#### Answer

It is a legal axiom. Its expression starts with a declared constant, and all its math symbols are active. There are no
variables requiring floating hypotheses. Metamath does not require a separate `wff` construction when declaring an
axiom, and does not check that these symbols make sense as ordinary propositional logic.

We decide which axioms to put in the database. The verifier checks applications of those axioms according to their
mandatory hypotheses; it does not establish that our chosen axioms express the mathematics we intended.

### Question

*Note:* This question was AI generated and has not been reviewed.

In Metamath, suppose we have proved `|- a = b`, where `a` and `b` are distinct constants. An assertion requires the
essential hypothesis `|- F a`, but we have `|- F b` on the proof stack. Does the equality let these match? What if
`|- a = b` was introduced as a definition?

Note: Assume all symbols are declared. The expressions shown contain only constants.

#### Answer

No. Satisfying the essential hypothesis requires an exact match after substitution, and substitution does not replace
constants. The verifier will not use the equality automatically.

We would need to apply suitable equality rules from the database to obtain `|- F a` explicitly. Calling an assertion
a definition does not give it any special rewriting behavior in the verifier.

### Question

*Note:* This question was AI generated and has not been reviewed.

In Metamath, a theorem `lemma` has an unfinished proof containing `?`. A later theorem uses `lemma`, satisfies its
mandatory hypotheses correctly, and ends with the right expression on the proof stack. Have we now proved the later
theorem from the axioms?

#### Answer

No. The application of `lemma` can pass the stack and substitution checks, but its conclusion has not yet been
established by a complete proof. The later theorem still depends on that unfinished proof.

To claim a complete proof from the axioms and the theorem's hypotheses, we also need complete proofs of the earlier
theorems it uses, including their dependencies. A locally correct application of a theorem does not by itself verify
that theorem's proof.
