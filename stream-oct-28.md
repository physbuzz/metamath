

### Deciding what to do
Could do:
1. Write more ch2 notes. (The authors could in some universe perhaps allow more chapter 2 notes to be written. )
2. Could do but WON'T do: SICP / connection with logic programming.
3. Writing a Metamath Interpreter

Will do:
1. Skim ch2 again.
2. Start C++ project / metamath interpreter
3. NOT set.mm, instead either look at...
 - The chapter 2 example
 - Hofstadter's MIU 
 - David A. Wheeler's torture test (tests for correctness of a Metamath interpreter) 

### Skimming ch2 again:

- I forgot the emphasis on "theorem scheme" and "proof scheme". 
But it's an important technical point that `0 = 0` and `(0 + 0) = (0 + 0)` are the "actual" theorems. But it should be obvious to us why we emphasize theorem schemes.
- "stating the trivial and obvious is a goal to strive for in any axiomatic system."
- Mendelson's book might be worth skimming. [43] Elliott Mendelson. Introduction to Mathematical Logic. D. Van Nostrand Company, Inc., New York, second edition, 1979. [QA9.M537 1979]. 
- 

***Question:***

In the following statement, axiom `mp` has four mandatory 
hypotheses
```metamath
    $c wff ...$.
    $v P Q ... $.
    ...
    wp $f wff P $.
    wq $f wff Q $.
    ...
    ${
        min $e |- P $.
        maj $e |- ( P -> Q ) $.
        mp $a |- Q $.
    $}
```

Is the rule: "Any variable that appears in a essential hypothesis
is added to the list of mandatory hypotheses"?

#### Answer: 
erm.

TODO

### Question
Is it true that each variable can only have one typecode (such 
as `wff P`, I guess then declaring `tp $f term P $.` would be an error)?

#### Answer:
Yes! Trying to do `wp $f wff P $.` followed by `tp $f term P $.`
gives an error! 

```
?Error on line 12 of file "demo0.mm" at statement 8, label "tp", type "$f":
    tp $f term P $.
The variable "P" already appears in the earlier active "$f" statement "wp" on
```

### Question:
In going through the book's interactive proof constructor, we wind up with the following series of commands:
```
MM-PA> delete all
The entire proof was deleted.
1    th1=? $? |- t = t
MM-PA> assign 1 mp
3 -1   min=?  $? |- $2
4      maj=?  $? |- ( $2 -> t = t )
MM-PA> assign 4 mp
3 -2   min=?  $? |- $2
6 -1     min=?  $? |- $4
7        maj=?  $? |- ( $4 -> ( $2 -> t = t ) )
MM-PA> show new_proof/lemmon/all
1 ?              $? wff $2
2 ?              $? wff t = t
3 ?              $? |- $2
4 ?              $? wff $4
5 ?              $? wff ( $2 -> t = t )
6 ?              $? |- $4
7 ?              $? |- ( $4 -> ( $2 -> t = t ) )
8 4,5,6,7 mp     $a |- ( $2 -> t = t )
9 1,2,3,8 mp     $a |- t = t
```

For lines 6, and 7, these are eventually filled by axioms, 
why can we not figure out they're axioms right now? Why
do we have to write `$?`

#### Answer:

For line 6, for example, we could have imagined defining a floating
hypothesis `foo $f |- arg $.` which would satisfy it. For 
line 7, it's a bit more confusing because a floating hypothesis
only allows for one variable, so there's no way it can be a
floating hypothesis. But I suppose there's the possibility of it
being filled with another syntax feature that we don't use in 
this particular proof.



### Question
In the Metamath interactive terminal, 
we can type things like `show new_proof/lemmon/all` or 
`show new_proof /lemmon /all`. Do the spaces make a difference?

#### Answer
TODO

### Question
TODO come up with an example with `minimize_with */brief` like
the book mentions

#### Answer

### Question
What are some things to watch out for when editing a large proof
database (`.mm` file)?

#### Answer
You cannot change the order of the mandatory hypotheses of 
any statement referenced in a later proof.

Swapping the names of two variables in a theorem will change
the order of its mandatory hypotheses.

### Question:
What is the sentence in the metamath book that contains the word
'meta' the most times?

















