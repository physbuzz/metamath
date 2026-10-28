Everything important here has been moved to ch2.md pretty sure.


th1 $p |- t = t $=
    tt tze tpl tt weq tt tt weq tt a2 tt tze tpl
    tt weq tt tze tpl tt weq tt tt weq wim tt a2
    tt tze tpl tt tt a1 mp mp
$.

$( tt tze tpl tt weq tt tt weq $)
x f term t 
x a term 0 
x a term ( t + 0 )
x f term t
??? a wff ( t + 0 ) = t
x f term t
x f term t
??? a wff t = t
$( tt a2 tt tze tpl $)
x f term t
x a |- ( t + 0 ) = t 
x f term t
x a term 0
x a term ( t + 0 )
$( tt weq tt tze tpl tt weq $)
x f term t
??? a wff ( t + 0 ) = t
x f term t
x a term 0
x a term ( t + 0 )
x f term t
x a wff ( t + 0 ) = t
$( tt tt weq wim tt a2 $)
x f term t
x f term t
x a wff t = t 
??? a wff ( ( t + 0 ) = t -> t = t ) 
x f term t
x a |- ( t + 0 ) = t 
$( tt tze tpl tt tt a1 mp mp $)
x f term t
x a term 0
x a term ( t + 0 )
x f term t
x f term t
x a |- ( ( t + 0 ) = t -> ( ( t + 0 ) = t -> t = t ) ) 
$( I think this our first nontrivial example of unification. because in essential hypothesis maj
we fill in P := ( t + 0 ) = t, and Q := ( ( t + 0 ) = t -> t = t ) $)
x a |- ( ( t + 0 ) = t -> t = t )
$( unification again, P := ( t + 0 ) = t, 
Q := t = t $)
a |- t = t











A1. ( #1 = #2  -> ( #1 = #3  ->  #2 = #3 ))
A2. ( #1 +0)= #1 

Looking at the first t=t theorem

We substitute #1a := #1 + 0
We substitute #2a := #1
We substitute #3a := #1
substitute into axiom:
( #1a = #2a  -> ( #1a = #3a  ->  #2a = #3a ))
To get:
( #1 + 0 = #1  -> ( #1 + 0 = #1  ->  #1 = #1 ))

I'm confused at the moment, but I don't have enough information to go through steps 4 and 5. "Modus ponens" is not a primitive of the language, so I don't know how that's implemented with substitution rules / whatever stack stuff is going on. 


## Metamath Program 1
$( Declare the constant symbols we will use $)
    $c 0 + = -> ( ) term wff |- $.
$( Declare the metavariables we will use $)
    $v t r s P Q $.
$( Specify properties of the metavariables $)
    tt $f term t $.
    tr $f term r $.
    ts $f term s $.
    wp $f wff P $.
    wq $f wff Q $.
$( Define "term" and "wff" $)
    tze $a term 0 $.
    tpl $a term ( t + r ) $.
    weq $a wff t = r $.
    wim $a wff ( P -> Q ) $.
$( State the axioms $)
    a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.
    a2 $a |- ( t + 0 ) = t $.
$( Define the modus ponens inference rule $)
    ${
        min $e |- P $.
        maj $e |- ( P -> Q ) $.
        mp $a |- Q $.
    $}
$( Prove a theorem $)
    th1 $p |- t = t $=
    $( Here is its proof: $)
        tt tze tpl tt weq tt tt weq tt a2 tt tze tpl
        tt weq tt tze tpl tt weq tt tt weq wim tt a2
        tt tze tpl tt tt a1 mp mp
    $.

$c -- constants. User-defined, "meaningless"
$v -- Variables. "Metavariables" or "placeholders"
$e -- Essential hypothesis. ("logical hypothesis")
$f -- Floating Hypothesis. ("variable type hypothesis") Must contain a constant followed by a variable.
$a -- Axiomatic assertion. Constant followed by arbitrarily many math symbols.
$p -- Provable assertion. Constant followed by arbitrarily many math symbols.

Things I think about this proof:
 - `tze $a term 0 $.` This is an axiomatic hypothesis, as opposed to the floating hypotheses earlier. The floating hypotheses were not "axioms" because they refer to metavariables. But 0 is an actual term of the language (?) so we need an actual axiom.
- `tpl $a term ( t + r ) $.` Here the parentheses "mean nothing", but I think they serve to simplify the ways in which pattern matching can occur, (note: "pattern matching" might be the wrong statement here. 
- "$a is a constant followed by arbitrary seq of math symbols" -- The definition is this simple, no tricks. But it's not devoid of structure. ***MAYBE***: what's going on is that subseqs of the axiom can match with other terms ($f $a) with metavariables being substituted **via unification.** (Q: is "simple term-rewriting unification scheme" a misnomer?)


"In the statement `tpl $a term ( t + r ) $.` constants `( + )` don't need any hypotheses. `t` and `r` need hypotheses because they are metavariables. This is satisfied by the mandatory hypotheses `$f term t $.` and `$f term r $.`"

Metamath's show statement command can show you a statement's mandatory hypotheses.

Things I don't think about this proof:
- "Wow what a beautiful language."









