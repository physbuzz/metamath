---
title: "04 Suggestions: Small Formal Systems"
---

# 04 Suggestions: Small formal systems

Five possible additions to [04-propmm.md](04-propmm.md). Each section starts a
separate database; none uses `$d` or compressed proofs. Empty strings are allowed.

Replace each `?` with the corresponding proof after `$=` in the solutions.
Solution excerpts omit enclosing scopes and hypotheses; retain those from the
exercise. Earlier solutions may be used in later proofs.

To check a completed database:

```sh
metamath 'read "example.mm"' 'verify proof *' 'exit'
```

@toc

## 1. A proof as a machine run

A unary incrementer, starting with tape `1 1 B`. In `[ L ; q ; a ; R ]`,
`a` is under the head and both tape strings read left to right. State `q`
scans right over `1`; on reaching `B`, it writes `1` and halts in state `h`.
The explicit trailing blank suffices for this run.

`config` means well-formed; `|-` means reachable from `start`. Prove the
syntax judgments, then the three machine steps.

```metamath
$c tape config |- 1 B q h [ ] ; $.
$v L R $.
tl $f tape L $.
tr $f tape R $.
empty $a tape $.
one $a tape 1 R $.
blank $a tape B R $.
c-one $a config [ L ; q ; 1 ; R ] $.
c-blank $a config [ L ; q ; B ; R ] $.
c-halt $a config [ L ; h ; 1 ; R ] $.

start $a |- [ ; q ; 1 ; 1 B ] $.
${
  right-one.1 $e |- [ L ; q ; 1 ; 1 R ] $.
  right-one $a |- [ L 1 ; q ; 1 ; R ] $.
$}
${
  right-blank.1 $e |- [ L ; q ; 1 ; B R ] $.
  right-blank $a |- [ L 1 ; q ; B ; R ] $.
$}
${
  write.1 $e |- [ L ; q ; B ; R ] $.
  write $a |- [ L ; h ; 1 ; R ] $.
$}

shape $p config [ ; q ; 1 ; 1 B ] $= ? $.
unreached-shape $p config [ ; h ; 1 ; ] $= ? $.
scan $p |- [ 1 ; q ; 1 ; B ] $= ? $.
end $p |- [ 1 1 ; q ; B ; ] $= ? $.
halt $p |- [ 1 1 ; h ; 1 ; ] $= ? $.
```

### Hints

- `shape`: construct the two tape strings, then use `c-one`.
- `unreached-shape`: both tape strings are empty. Why is the corresponding
  `|-` statement nevertheless unprovable?
- `scan`: use `right-one` with empty `L` and `R = B`.
- `end`: use `right-blank` with `L = 1` and empty `R`.
- `halt`: use `write`.

### Solutions

```mm
shape $p config [ ; q ; 1 ; 1 B ] $=
  empty empty blank one c-one $.

unreached-shape $p config [ ; h ; 1 ; ] $=
  empty empty c-halt $.

scan $p |- [ 1 ; q ; 1 ; B ] $=
  empty empty blank start right-one $.

end $p |- [ 1 1 ; q ; B ; ] $=
  empty one empty scan right-blank $.

halt $p |- [ 1 1 ; h ; 1 ; ] $=
  empty one one empty end write $.
```

The only reachable configurations are `start`, `scan`, `end`, and `halt`.
`unreached-shape` is syntax, not another possible run.

Further exercises:

- Justify: a ground `|-` statement is provable iff it is reachable. Inspect
  the last rule of a proof; in the other direction, translate each machine step.
- Add leftward moves and rules for extending the represented tape with blanks.
- Add a `history` judgment recording configurations in the statement itself.
  The existing proof already witnesses a run, with extra tape-syntax steps.

## 2. Dragon curves and simultaneous substitution

Use the productions `X -> X+YF+`, `Y -> -FX-Y`, with seed `FX`.
`F`, `+`, and `-` reproduce themselves. All five letters are Metamath constants.

`step u => v` means one complete generation, assembled using `join`.
`dragon u` means a finite generation string. Prove an extension rule and the
first two generations. Simultaneous replacement is the essential distinction
from ordinary sequential rewriting; see [The Algorithmic Beauty of Plants,
chapter 1](https://algorithmicbotany.org/papers/abop/abop-ch1.pdf).

```metamath
$c word step dragon X Y F + - => $.
$v u v x y $.
wu $f word u $.
wv $f word v $.
wx $f word x $.
wy $f word y $.
we $a word $.
wX $a word X $.
wY $a word Y $.
wF $a word F $.
wp $a word + $.
wm $a word - $.
wc $a word u v $.

se $a step => $.
sX $a step X => X + Y F + $.
sY $a step Y => - F X - Y $.
sF $a step F => F $.
sp $a step + => + $.
sm $a step - => - $.
${
  join.1 $e step u => v $.
  join.2 $e step x => y $.
  join $a step u x => v y $.
$}
seed $a dragon F X $.
${
  grow.1 $e dragon u $.
  grow.2 $e step u => v $.
  grow $a dragon v $.
$}

${
  extend.1 $e step u => v $.
  extend $p step u X => v X + Y F + $= ? $.
$}
first-step $p step F X => F X + Y F + $= ? $.
first $p dragon F X + Y F + $= ? $.

second-step $p step F X + Y F + => F X + Y F + + - F X - Y F + $= ? $.

second $p dragon F X + Y F + + - F X - Y F + $= ? $.
```

### Hints

- `extend`: use `join` with the given step and `sX`.
- `first-step`: instantiate `extend` with `u = v = F`.
- `first`: apply `grow` to `seed` and `first-step`.
- `second-step`: combine `sF`, `sX`, `sp`, `sY`, `sF`, `sp`, in that order.
  `wc` supplies the word hypotheses needed by `join`.
- `second`: use `grow` again.

### Solutions

```mm
extend $p step u X => v X + Y F + $=
  wu wv wX wX wp wc wY wc wF wc wp wc extend.1 sX join $.

first-step $p step F X => F X + Y F + $=
  wF wF sF extend $.

first $p dragon F X + Y F + $=
  wF wX wc wF wX wc wp wc wY wc wF wc wp wc seed first-step grow $.

second-step $p step F X + Y F + => F X + Y F + + - F X - Y F + $=
  wF wX wc wp wc wY wc wF wc wF wX wc wp wc wY wc wF wc wp wc wp wc wm wc wF
  wc wX wc wm wc wY wc wF wc wp wp wF wX wc wp wc wY wc wF wX wc wp wc wY wc
  wF wc wp wc wp wc wm wc wF wc wX wc wm wc wY wc wF wF wF wX wc wp wc wF wX
  wc wp wc wY wc wF wc wp wc wp wc wY wm wF wc wX wc wm wc wY wc wF wX wc wF
  wX wc wp wc wY wc wF wc wp wc wp wp wF wF wX wX wp wc wY wc wF wc wp wc sF
  sX join sp join sY join sF join sp join $.

second $p dragon F X + Y F + + - F X - Y F + $=
  wF wX wc wp wc wY wc wF wc wp wc wF wX wc wp wc wY wc wF wc wp wc wp wc wm
  wc wF wc wX wc wm wc wY wc wF wc wp wc first second-step grow $.
```

Two follow-ups:

1. Replace individual occurrences instead of whole generations. Find a string
   this incorrectly accepts. Hint: count `F`s.
2. Render `second`: `F` advances one unit, `+` turns left 90 degrees, `-` turns
   right 90 degrees, and `X`, `Y` do nothing. Repeat with later generations.

For (1), rewriting only `X` in `F X + Y F +` gives
`F X + Y F + + Y F +`. This has three `F`s. Genuine generation `n` has
`2^n` of them: the number of `X`/`Y` symbols doubles each generation and equals
the number of `F`s. Thus the mixed-generation string cannot be a `dragon` theorem.

The geometric curve is an interpretation of the proved string; the rules above
only certify the string's generation.

## 3. Implication proofs as programs

The types of `K` and `S` have exactly the shapes of `ax-1` and `ax-2`.
`apply` is modus ponens with a program attached. Application is fully
parenthesized: `( x y )` means apply `x` to `y`.

Prove that `((S K) K)` has identity type and reduces to its argument.
Here `~>` allows a nonempty sequence of root reductions; reduction inside
subterms is not needed for these exercises.

```metamath
$c type term |- -> ( ) : K S ~> $.
$v A B C x y z $.
ta $f type A $.
tb $f type B $.
tc $f type C $.
tx $f term x $.
ty $f term y $.
tz $f term z $.
arr $a type ( A -> B ) $.
k $a term K $.
s $a term S $.
app $a term ( x y ) $.

kt $a |- K : ( A -> ( B -> A ) ) $.
st $a |- S : ( ( A -> ( B -> C ) ) ->
              ( ( A -> B ) -> ( A -> C ) ) ) $.
${
  apply.1 $e |- x : ( A -> B ) $.
  apply.2 $e |- y : A $.
  apply $a |- ( x y ) : B $.
$}
kr $a |- ( ( K x ) y ) ~> x $.
sr $a |- ( ( ( S x ) y ) z ) ~> ( ( x z ) ( y z ) ) $.
${
  chain.1 $e |- x ~> y $.
  chain.2 $e |- y ~> z $.
  chain $a |- x ~> z $.
$}

sk $p |- ( S K ) : ( ( A -> B ) -> ( A -> A ) ) $= ? $.
identity $p |- ( ( S K ) K ) : ( A -> A ) $= ? $.
expand $p |- ( ( ( S K ) K ) x ) ~> ( ( K x ) ( K x ) ) $= ? $.
run $p |- ( ( ( S K ) K ) x ) ~> x $= ? $.
```

### Hints

- `sk`: use `apply`. Instantiate `st` with `C = A`; its input type is the
  type of `K` from `kt`.
- `identity`: apply `sk` with `B = ( A -> A )` to `kt` with `B = A`.
- `expand`: instantiate `sr` with its first two arguments both `K`.
- `run`: chain `expand` with `kr`. The discarded argument is `( K x )`.

### Solutions

```mm
sk $p |- ( S K ) : ( ( A -> B ) -> ( A -> A ) ) $=
  ta tb ta arr arr ta tb arr ta ta arr arr s k ta tb ta st ta tb kt apply $.

identity $p |- ( ( S K ) K ) : ( A -> A ) $=
  ta ta ta arr arr ta ta arr s k app k ta ta ta arr sk ta ta kt apply $.

expand $p |- ( ( ( S K ) K ) x ) ~> ( ( K x ) ( K x ) ) $=
  k k tx sr $.

run $p |- ( ( ( S K ) K ) x ) ~> x $=
  s k app k app tx app k tx app k tx app app tx
  tx expand tx k tx app kr chain $.
```

For a further exercise, annotate a proof of `id` from section 4.1:
`ax-1` contributes `K`, `ax-2` contributes `S`, and `ax-mp` applies the
program for the implication to the program for its antecedent. Expand any
derived rules first. Different proofs can produce different identity programs.

## 4. Arithmetic without quantifiers

`( S n )` is successor. The judgments `|- add m n k` and `|- mul m n k`
express addition and multiplication. This is a small arithmetic relation
system, not the whole of Peano arithmetic.

Prove `2 + n = S(S(n))`, `2 + 1 = 3`, `1 * n = n`, and `2 * 2 = 4`.

```metamath
$c nat |- 0 S ( ) add mul $.
$v m n k r $.
nm $f nat m $.
nn $f nat n $.
nk $f nat k $.
nr $f nat r $.
nz $a nat 0 $.
ns $a nat ( S n ) $.
az $a |- add 0 n n $.
${
  as.1 $e |- add m n k $.
  as $a |- add ( S m ) n ( S k ) $.
$}
mz $a |- mul 0 n 0 $.
${
  ms.1 $e |- mul m n k $.
  ms.2 $e |- add k n r $.
  ms $a |- mul ( S m ) n r $.
$}

add-two $p |- add ( S ( S 0 ) ) n ( S ( S n ) ) $= ? $.
two-plus-one $p |- add ( S ( S 0 ) ) ( S 0 ) ( S ( S ( S 0 ) ) ) $= ? $.
mul-one $p |- mul ( S 0 ) n n $= ? $.
two-times-two $p |- mul ( S ( S 0 ) ) ( S ( S 0 ) )
    ( S ( S ( S ( S 0 ) ) ) ) $= ? $.
```

### Hints

- `add-two`: begin with `az` and use `as` twice. Keep the second input `n`
  unchanged.
- `two-plus-one`: substitute `( S 0 )` for `n` in `add-two`.
- `mul-one`: use `ms` with `m = k = 0` and `r = n`.
- `two-times-two`: use `ms` with `m = 1`, `n = k = 2`, and `r = 4`.
  The premises are instances of `mul-one` and `add-two`.

### Solutions

```mm
add-two $p |- add ( S ( S 0 ) ) n ( S ( S n ) ) $=
  nz ns nn nn ns nz nn nn nn az as as $.

two-plus-one $p |- add ( S ( S 0 ) ) ( S 0 ) ( S ( S ( S 0 ) ) ) $=
  nz ns add-two $.

mul-one $p |- mul ( S 0 ) n n $=
  nz nn nz nn nn mz nn az ms $.

two-times-two $p |- mul ( S ( S 0 ) ) ( S ( S 0 ) )
    ( S ( S ( S ( S 0 ) ) ) ) $=
  nz ns nz ns ns nz ns ns nz ns ns ns ns
  nz ns ns mul-one nz ns ns add-two ms $.
```

Try proof search backwards: which numeral can fill `m` in `|- mul m 2 4`?
Here numerals abbreviate successor expressions. The last proof supplies `m = 2`.

General laws need more care. `add-two` is a finite schematic derivation;
proving every concrete numeral instance of another law does not automatically
give an induction principle for that law.

## 5. A proof as a puzzle solution

One-dimensional peg solitaire: `1` is a peg and `0` is an empty hole.
A jump replaces `110` by `001`, or `011` by `100`.
Start at `1101` and finish at `0100`.

Prove the two moves, then a rule that finishes the same pattern after any
prefix `u`. Each move removes exactly one peg and preserves board length.

```metamath
$c row |- 0 1 $.
$v u v $.
ru $f row u $.
rv $f row v $.
re $a row $.
r0 $a row 0 v $.
r1 $a row 1 v $.
rc $a row u v $.
start $a |- 1 1 0 1 $.
${
  right.1 $e |- u 1 1 0 v $.
  right $a |- u 0 0 1 v $.
$}
${
  left.1 $e |- u 0 1 1 v $.
  left $a |- u 1 0 0 v $.
$}

first $p |- 0 0 1 1 $= ? $.
solved $p |- 0 1 0 0 $= ? $.
${
  finish.1 $e |- u 0 0 1 1 $.
  finish $p |- u 0 1 0 0 $= ? $.
$}
```

### Hints

- `first`: use `right` with empty prefix and suffix `1`.
- `solved`: use `left` with prefix `0` and empty suffix.
- `finish`: use `left` with prefix `u 0` and empty suffix; construct `u 0`
  with `rc`.

### Solutions

```mm
first $p |- 0 0 1 1 $=
  re re r1 start right $.

solved $p |- 0 1 0 0 $=
  re r0 re first left $.

finish $p |- u 0 1 0 0 $=
  ru re r0 rc re finish.1 left $.
```

### A faulty move rule

In a separate copy, append this proposed rule. Prove `teleport`, then identify
what went wrong with the rule.

```metamath
${
  bad.1 $e |- u 1 0 0 v $.
  bad $a |- u 0 0 1 v $.
$}
teleport $p |- 0 0 0 1 $= ? $.
```

Hint: apply it to `solved`, with prefix `0` and empty suffix.

```mm
teleport $p |- 0 0 0 1 $=
  re r0 re solved bad $.
```

`bad` jumps over an empty hole. The proof verifies, but the move is illegal.
With the original rules, `0100` has no successor: neither `110` nor `011`
occurs in it. The only reachable boards are `1101`, `0011`, and `0100`.
