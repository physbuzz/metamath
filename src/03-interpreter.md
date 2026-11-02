---
title: "03 Writing a Metamath Interpreter (Megill ch4)"
---

<h1 id="03-interpreter" style="border-bottom: none;">03 Writing a Metamath Interpreter (Megill ch4)</h1>

<nav class="nav">
    <span class="activenav"><a href="02-sicp-logic.html">← Previous</a></span>
    <span class="activenav"><a href="index.html">↑ Up</a></span>
    <span class="activenav"><a href="04-setmm.html">Next →</a></span>
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


## Writing the parser

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

## Writing the proof checker







