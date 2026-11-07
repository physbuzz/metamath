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

In Metamath, are `( P -> Q )` and `(P->Q)` the same sequence of math symbols? What about `P Q` and `PQ`? Can a parser split tokens by recognizing familiar logical punctuation?

#### Answer

Tokens are separated by whitespace. `( P -> Q )` contains five tokens, whereas `(P->Q)` is one token. Likewise, `P Q` contains two tokens and `PQ` contains one. The single tokens could be separately declared math symbols, but declarations of their apparent pieces do not declare them.

The parser must not split tokens using logical punctuation. The database defines its symbols; parentheses and arrows do not have built-in lexical roles within math expressions.

### Question

In Metamath, assume the following declarations. Consider each proposed floating hypothesis independently. Which are legal, and why? After adding `fx $f term x $.`, could another `$f` for `x` be added inside a nested block?

```metamath
$c term wff 0 $.
$v x y $.
```

1. `h $f term x $.`
2. `h $f term 0 $.`
3. `h $f term x y $.`
4. `h $f x y $.`

#### Answer

Only the first is legal. A `$f` must contain exactly two math symbols: an active constant, then an active variable. The second uses a constant in the variable position; the third has too many symbols; the fourth uses a variable in the typecode position.

There cannot be two active `$f` statements for the same variable, even if they give the same typecode. A nested block does not hide an outer floating hypothesis, so adding another `$f` for `x` while `fx` is active is invalid.

### Question

In Metamath, what are the requirements for declaring an essential hypothesis with `$e`? Explain its expression shape, required variable typing, scope, and effect on later assertions. Distinguish using its label directly in a proof from satisfying it when applying an assertion.

#### Answer

An essential hypothesis has the form `label $e typecode symbols $.`. The label must be unique and must not also be a math symbol. The typecode must be an active constant; it is followed by zero or more active math symbols. Every variable used must already have an active `$f` hypothesis. The typecode need not be `|-`.

The hypothesis is active from its declaration to the end of its enclosing block, or to the end of the database if declared outside all blocks. It is mandatory for every subsequent assertion declared while it is active, even if its expression appears irrelevant to the conclusion.

Referencing an active `$e` label in a proof pushes its expression unchanged. Applying an assertion that has this `$e` as a mandatory hypothesis instead consumes a stack entry that must match the hypothesis after the assertion's substitution. The hypothesis is an assumption while proving within its scope and an obligation when applying the resulting assertion elsewhere.

### Question

In this Metamath database, what are the mandatory variables and the ordered mandatory hypotheses of `rule`? Which active floating hypothesis is omitted? Would collecting all mandatory `$f` statements first and all `$e` statements second give the right order?

```metamath
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

The mandatory variables are `x` and `y`: take the variables in the assertion together with those in all active essential hypotheses. Thus `y` is mandatory even though it is absent from the conclusion.

The ordered mandatory hypotheses are `wx hx wy hy`, preserving database order. `wz` is omitted because `z` occurs in neither the assertion nor an active essential hypothesis. Both essential hypotheses are included. Grouping by statement kind would incorrectly produce `wx wy hx hy`.

### Question

In this Metamath database, is the proof of `th` valid? Does `th` have a mandatory hypothesis even though its proof never references `h`? After the block closes, can a later proof obtain `|- B` by using `th` with an empty stack?

```metamath
$c |- A B $.
b $a |- B $.
${
    h $e |- A $.
    th $p |- B $= b $.
$}
```

#### Answer

The proof is valid: `b` has no hypotheses and leaves exactly `|- B` on the stack.

Nevertheless, `h` is a mandatory hypothesis of `th` because it was active when `th` was declared. Mandatory hypotheses are determined from the declaration's context, not by analyzing which assumptions its proof uses. A later application of `th` must consume an entry `|- A`; applying it to an empty stack fails. The caller could instead use `b` directly.

### Question

In this Metamath database, what happens to `x`, `fx`, `h`, and `pass` after `$}`? Can a later proof use `h` directly? What must it supply to apply `pass` with `t` substituted for `x`?

```metamath
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

The declaration of `x` and the hypotheses `fx` and `h` become inactive. A later expression cannot use `x` on the strength of this expired declaration, and a later proof cannot reference `fx` or `h` directly.

The assertion `pass` remains available with its original mandatory hypotheses `fx h`. To apply it with `x` replaced by `t`, a proof supplies `term t` followed by `|- t`; `pass` consumes both and pushes `|- t`.

The parser must therefore retain `pass`'s expression and ordered mandatory hypotheses after leaving the block. Removing hypotheses from the active context must not destroy the assertion's stored requirements.

### Question

In this Metamath database, trace the proof of `th`. Why does `drop` require a floating hypothesis for `b`, although `b` is absent from its conclusion? What are the mandatory hypotheses of `th` itself, and must a later caller supply the floating hypotheses used inside its proof?

```metamath
$c term |- $.
$v a b $.
fa $f term a $.
fb $f term b $.
${
    hb $e |- b $.
    drop $a |- $.
$}
seed $a |- a $.
th $p |- $= fa fa seed drop $.
```

#### Hint

Compute `drop`'s and `th`'s mandatory hypotheses separately. Then track which of the two copies of `term a` is consumed by `seed`.

#### Answer

`drop` has mandatory hypotheses `fb hb`: the variable `b` occurs in its essential hypothesis. Its conclusion consists only of the constant `|-`, which is a legal expression.

The proof proceeds as follows, with stacks listed from bottom to top:

1. `fa`: `term a`.
2. `fa`: `term a`, `term a`.
3. `seed`: consumes the top `term a` and pushes `|- a`, leaving `term a`, `|- a`.
4. `drop`: uses `a` as the replacement for `b`, checks `|- a` against its substituted essential hypothesis, consumes both entries, and pushes `|-`.

`th` has no mandatory hypotheses: its conclusion has no variables, and no essential hypotheses are active at its declaration. The active floating hypotheses `fa` and `fb` are optional hypotheses of `th`; its proof uses `fa`. A later caller of `th` supplies no stack entries. A theorem's internal proof can use optional hypotheses without adding them to the theorem's mandatory inputs.

### Question

A Metamath implementation parses the whole database before checking proofs. Is it enough to accept any proof label found in its final global statement table? Which references are legal in a theorem's uncompressed proof, and what context must the implementation preserve?

#### Answer

A proof may reference hypotheses active at the theorem's declaration and assertions appearing earlier in the database. It may not reference the theorem itself, a later assertion, or a hypothesis whose scope has already ended. An earlier assertion remains available even if its declaring block has closed.

A final global table alone does not establish these conditions. The implementation must enforce them while parsing or retain enough declaration order and scope information to check them later. It must also allow active optional floating hypotheses, not just the theorem's mandatory hypotheses.

### Question

While verifying a Metamath proof, an assertion application substitutes `0` for a variable `t`. The next proof label is the active hypothesis `tt $f term t $.`. Does `tt` now push `term 0` or `term t`? Does that earlier substitution modify future uses of the assertion?

#### Answer

`tt` pushes `term t`, unchanged. Each assertion application constructs its own substitution; it does not assign a persistent value to a database variable or modify a stored statement. A later use of the same assertion obtains its substitutions from the stack entries supplied for that later use.

### Question

In a Metamath database with no disjoint-variable restrictions, describe the complete stack operation for applying an `$a` or an already verified `$p` with (n) mandatory hypotheses. How are the inputs paired with hypotheses, how is the substitution determined, and what happens when (n=0)?

#### Answer

1. Require at least (n) entries. Use the top (n), pairing them from bottom to top with the mandatory hypotheses in database order. If physically popping, the first popped entry corresponds to the last hypothesis.
2. For every mandatory `$f`, check that the paired entry starts with the required typecode. Map its variable to the remaining symbol sequence, excluding that typecode.
3. Apply this substitution to each mandatory `$e` and require exact equality with its paired stack entry.
4. Remove the (n) input entries and push the assertion's expression with the same substitution applied. Entries below these inputs remain untouched.

The substitution is simultaneous and replaces variables only. Hypothesis order may interleave `$f` and `$e`; collecting the `$f` mappings before checking `$e` expressions avoids dependence on the direction in which the stack is traversed.

For (n=0), consume nothing and push the assertion's expression unchanged. Applying a `$p` uses its stored hypotheses and conclusion; it does not splice its internal proof into the caller's stack.

### Question

In a Metamath assertion application, suppose the floating-hypothesis inputs establish these substitutions:

```text
P := ( Q -> P )
Q := R
```

What does `wff ( P -> Q )` become? Should the verifier keep replacing `P` and `Q` inside the inserted expression? Assume all required typing evidence has been supplied and there are no disjoint-variable restrictions.

#### Answer

The result is:

```text
wff ( ( Q -> P ) -> R )
```

Substitution is simultaneous: replace occurrences in the original expression, without recursively substituting into the sequences inserted. The `P` and `Q` inside the replacement for `P` remain as written. A replacement may contain the very variable being replaced; this does not create an infinite substitution process.

### Question

In this Metamath database, why does the proof fragment `ft wp wi` fail? Would it help if the symbol sequence `t` could also be proved to be a `wff` elsewhere in the database?

```metamath
$c term wff ( ) -> $.
$v t P Q $.
ft $f term t $.
wp $f wff P $.
wq $f wff Q $.
wi $a wff ( P -> Q ) $.
```

#### Answer

`wi` has mandatory hypotheses `wp wq`. The fragment supplies `term t` and `wff P`, in that order. Its first input must start with `wff`, but starts with `term`, so the application fails before essential-hypothesis checking is relevant.

The verifier does not search the database for alternative typing evidence or convert an existing stack entry automatically. A proof of `wff t` would have to be explicitly placed on the stack in the required position.

### Question

In Metamath, a rule has these mandatory hypotheses, in order:

```text
wp: wff P
h:  |- ( P -> P )
```

Its conclusion is `|- P`. Assume `A` and `B` are distinct constant tokens and the following two entries have been legitimately obtained. Can the rule consume them? Could it infer different replacements from the essential hypothesis to make the application succeed?

```text
wff A
|- ( A -> B )
```

#### Answer

No. The floating input fixes `P := A`, so the essential input must be exactly `|- ( A -> A )`. The actual entry is `|- ( A -> B )`.

The verifier cannot choose a new replacement for the second occurrence of `P`, nor can it change the substitution inferred from the floating input. All hypotheses and the conclusion use one consistent substitution.

### Question

In Metamath, an axiom has conclusion `wff ( P -> Q )` and mandatory hypotheses `wp $f wff P $.` followed by `wq $f wff Q $.`. A proof supplies `wff A` followed by `wff B`, where `A` and `B` are distinct symbol sequences. What happens if the declarations of `wp` and `wq` are swapped without changing the proof?

#### Answer

Originally the application uses `P := A` and `Q := B`, producing `wff ( A -> B )`.

After the declarations are swapped, the mandatory order is `wq wp`. The same inputs now give `Q := A` and `P := B`, producing `wff ( B -> A )`. Both inputs have the right typecode, so the application itself can succeed while producing a different expression. A later hypothesis check or the final theorem check may then fail.

Mandatory order comes from hypothesis declarations, not from variable order in the conclusion or alphabetical order of labels.

### Question

Is this Metamath proof valid? What gets substituted for `x`, and what error would a verifier make if it required at least one symbol after every stack entry's typecode?

```metamath
$c term ( ) $.
$v x $.
fx $f term x $.
empty $a term $.
wrap $a term ( x ) $.
th $p term ( ) $= empty wrap $.
```

#### Answer

The proof is valid. `empty` pushes the one-symbol expression `term`. When `wrap` consumes it for `fx`, the typecode matches and the remainder is the empty sequence. Thus `x` is replaced by no symbols, and `wrap` pushes `term ( )`, exactly the theorem's expression.

Metamath permits empty replacements. Requiring a nonempty remainder would reject this valid proof. The typecode itself is still present; it is the variable's replacement that is empty.

### Question

In Metamath, assume `a $a |- A $.` and `b $a |- B $.` have no mandatory hypotheses. For a theorem with target expression `|- B`, which of the proof sequences `a`, `a b`, and `b` succeeds? Assume all symbols are properly declared. Why is checking only the top stack entry insufficient?

#### Answer

Only `b` succeeds.

- `a` leaves a single entry, but it is `|- A`, not the target.
- `a b` leaves `|- A` and `|- B`. The top entry matches, but the stack has an extra entry.
- `b` leaves exactly one entry, `|- B`.

After processing the whole proof, the stack must contain exactly one expression, identical token for token to the theorem's expression, including its typecode. The verifier cannot discard leftover entries or accept merely equivalent formulas.

### Question

Is the following a legal Metamath database, even though `( -> )` would not be a formula in ordinary propositional notation? Must an `$a` with typecode `|-` have a separate proof that its remaining expression is a `wff`?

```metamath
$c |- ( ) -> $.
odd $a |- ( -> ) $.
```

#### Answer

Yes, it is legal. The assertion begins with an active constant and contains only declared math symbols. There are no variables needing floating hypotheses. Metamath does not impose a built-in propositional grammar or demand a separate well-formedness proof when an axiom is declared.

A database's syntax axioms and floating hypotheses control which replacements can be supplied in its proofs. They do not make the verifier independently parse every axiom as an intended logical formula. Legality as Metamath source does not establish that an axiom expresses sensible mathematics.

### Question

In Metamath, a database has a proved equality `|- a = b`, where `a` and `b` are distinct constants. A rule requires the essential hypothesis `|- F a`, but the supplied stack entry is `|- F b`. Does the equality make these match automatically? Would calling the equality a definition change the verifier's behavior?

#### Answer

No. Essential hypotheses must match exactly after the rule's variable substitution. Constants are not substitution placeholders, so the verifier cannot replace `a` by `b` during this check.

The proof must explicitly use suitable assertions from the database to derive the required expression. Calling a statement a definition does not give it automatic unfolding or rewriting behavior in the core verifier.

### Question

A Metamath database contains an unfinished theorem whose proof is `?`. A later theorem applies it with correctly matched mandatory hypotheses and reaches its own target expression. Is that enough to claim that the later theorem has a fully verified proof from the axioms? What must a checker distinguish?

#### Answer

No. The later application can satisfy the local stack and substitution checks while relying on a theorem whose proof is unfinished. `?` marks an unknown proof step; it does not establish the claimed assertion.

A checker must distinguish an incomplete proof, a locally correct application of an assertion, and a complete verification of the required dependency chain. It should report incompleteness rather than present a proof that depends on an unresolved theorem as fully verified from the axioms.
