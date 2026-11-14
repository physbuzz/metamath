---
title: "3. Writing a Metamath Interpreter"
---


<nav class="nav">
    <span class="activenav"><a href="02-sicp-logic.html">← Previous</a></span>
    <span class="activenav"><a href="index.html">↑ Up</a></span>
    <span class="activenav"><a href="04-propmm.html">Next →</a></span>
</nav>

<h1 id="03-interpreter" style="border-bottom: none;">3. Writing a Metamath Interpreter</h1>

Since it's such a simple language, I decided that the best way to understand things is to write an interpreter myself.
Depending on how much coding experience you have, this may or may not be the best organization for you. 
The best reference for this is, no surprise, Megill ch 4. Even if you don't write an interpreter yourself,
the quiz questions at the bottom of the page might be useful!
Links: [Chapter html](book/index.html#the-metamath-language), [pdf on metamath.org](https://us.metamath.org/downloads/metamath.pdf#page=129).

@toc

## Introduction

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


2. Read ch4 and write a C++ metamath interpreter, and try it on David Wheeler's [set of mm test cases](https://github.com/david-a-wheeler/metamath-test). (Appendices B, E may be relevant but not needed). Study/implement appendix D, the MIU system.




## Quiz Questions

### Question 1

In Metamath, what is the difference between a math symbol and a statement label? Can a label have the same name as a
math symbol? If a hypothesis is in a block, can we reuse the label of a hypothesis after its block has closed?

#### Answer

"Math symbol" refers to either a constant or variable, which must be declared with `$c` and `$v`.

Labels name the statements `$f $e $a $p` so we can refer to them in proofs.

Labels must be unique throughout the database, even when the statements they label are no longer active. 
Closing a block does not let us reuse its hypothesis labels. A label also can't share a name with any constant
or variable.

### Question 2

In Metamath, what does it mean for a math symbol to be active? Can symbols be declared again?

#### Answer

Math symbols are only constants or variables, and constants can only be declared at the topmost level of the proof
database, so constants are simple: they are active and can be used from the point they're declared to the end of the file.

A variable is active from the point it's declared to the end of its block. Inactive variables may be redeclared (see
[megill ch4](book/index.html#redeclaration-of-math-symbols)). Variables are also special because if they're used in
any statement, they must have a floating hypothesis associated with them defining the typecode, and the typecode of
the variable may not change upon redeclaration.

### Question 3

In the following database, which statements go inactive at the end of the block `$}`? 
What are `pass`'s mandatory hypotheses, and what does applying it in a proof outside of the block do?

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

### Question 4

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

### Question 5

How do we determing a Metamath assertion's mandatory variables, and mandatory hypotheses and their order? 

How do we determine its 
optional hypotheses, and what are optional hypotheses? 

#### Answer

The mandatory variables of an assertion are any variables that occur in its list of math symbols or in any active
essential hypotheses. In the case of a proof, this *does not* include variables merely because they are referenced by
the statements after the `$=` sign. "Mandatory variable" is a term not introduced 'til
[Megill 4.1.3](book/index.html#4.1.3-basic-syntax).

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

### Question 6

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

(convention w/ stack growing downwards)

### Question 7

In Metamath, does an active essential hypothesis still become mandatory if it doesn't occur in a `$p`
statement's proof? What about if it doesn't share any math symbols with an `$a` statement?

#### Answer

Yes, in both cases. Active essential hypotheses are always mandatory hypotheses, even if the proof doesn't use them.
We still apply the same procedure when checking the proof, and such cases might be especially trivial but 
we still pop symbols off the proof stack and compare the symbols in the proof stack with the symbols in the 
mandatory hypothesis for consistency.

### Question 8

In Metamath, describe how the verifier processes the statement labels in a proof (ignoring disjoint variable restrictions).

#### Answer

First we initialize the proof stack to be empty, then we start reading the proof labels from left to right.

If we encounter a hypothesis, we push the expression onto the stack unchanged.

If we encounter an assertion, we must use the top entries on the proof stack to satisfy its mandatory hypotheses
in order, with the last mandatory hypothesis matching the most recent entry on the proof stack.

We then have to unify the mandatory hypotheses with the proof stack, which means finding a consistent replacement rule 
that replaces the variables in the mandatory hypothesis list with other lists of math symbols, such that we get the 
exact expressions on the proof stack in order with matching typecodes. In other languages "unification" can be 
complicated, but in this context unification is particularly simple, so we always either succeed or find that the 
statements can't be unified (in which case the proof is invalid).

Once a valid replacement is found, we make sure those elements we used are removed from the proof stack, then
we push the result of applying our replacement rule to the assertion's expression.

The proof succeeds if every step is valid and the final stack contains only the theorem's expression.

### Question 9

In Metamath, suppose we're in a database, in the middle of verifying a proof.
We have the following database: 

```mm
$c wff |- ( ) -> A B $.
$v P $.
wp $f wff P $.
${
    h $e |- ( P -> P ) $.
    rule $a |- P $.
$}
```

The proof stack looks like the following:

```text
wff A
|- ( A -> B )
```

Does applying `rule` to the stack succeed? If so, what gets pushed? If not, what could we change
on the stack to make it succeed?

#### Answer

The application fails. The floating hypothesis gives `P := A`, so the essential hypothesis requires `|- ( A -> A )`.
That cannot be unified with `|- ( A -> B )` because both occurrences of `P` must receive the same replacement.

If the second stack entry were `|- ( A -> A )`, the application would succeed. It would consume both entries and push
`|- A`.
