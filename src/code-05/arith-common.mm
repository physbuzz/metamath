$[ prop.mm $]

$c num = + * 0 S $.
$v t u v w $.
nt $f num t $.  nu $f num u $.  nv $f num v $.  nw $f num w $.
weq $a wff t = u $.
n0 $a num 0 $.
nS $a num S t $.
nadd $a num ( t + u ) $.
nmul $a num ( t * u ) $.

$( Peters' label, meaning, our label. $)
$( ER, equality reflexivity, eq-refl $)
eq-refl $a |- t = t $.
$( ES, equality symmetry, eq-sym $)
eq-sym $a |- ( t = u -> u = t ) $.
$( ET, equality transitivity, eq-tr $)
eq-tr $a |- ( t = u -> ( u = v -> t = v ) ) $.
$( CS, congruence of successor, eq-s $)
eq-s $a |- ( t = u -> S t = S u ) $.
$( CA, congruence of addition, eq-add $)
eq-add $a |- ( t = u -> ( v = w -> ( t + v ) = ( u + w ) ) ) $.
$( CM, congruence of multiplication, eq-mul $)
eq-mul $a |- ( t = u -> ( v = w -> ( t * v ) = ( u * w ) ) ) $.
$( AZ, add zero from the left, add-0l $)
add-0l $a |- ( 0 + t ) = t $.
$( AR, addition recursion from the left, add-sl $)
add-sl $a |- ( S t + u ) = S ( t + u ) $.
$( MZ, multiplication by zero from the left, mul-0l $)
mul-0l $a |- ( 0 * t ) = 0 $.
$( MR, multiplication recursion from the left, mul-sl $)
mul-sl $a |- ( S t * u ) = ( u + ( t * u ) ) $.
$( ZS, zero is not a successor, zns $)
zns $a |- -. 0 = S t $.
$( CD, case distinction, zos. Inactive: this is the axiom we set aside.
${
  $d u t $.
  zos $a |- ( t = 0 \/ E. u t = S u ) $.
$}
$)
$( SI, successor injectivity, s-inj $)
s-inj $a |- ( S t = S u -> t = u ) $.

$( Strange arabic glyphs $)
$c 1 2 3 4 5 6 $.
n1 $a num 1 $. df-1 $a |- 1 = S 0 $.
n2 $a num 2 $. df-2 $a |- 2 = S 1 $.
n3 $a num 3 $. df-3 $a |- 3 = S 2 $.
n4 $a num 4 $. df-4 $a |- 4 = S 3 $.
n5 $a num 5 $. df-5 $a |- 5 = S 4 $.
n6 $a num 6 $. df-6 $a |- 6 = S 5 $.

$( Equality: symmetry and transitivity. $)

${
  eqcomi.1 $e |- t = u $.
  $( Equality is symmetric; inference form of eq-sym
     set.mm analogue: https://us.metamath.org/mpeuni/eqcomi.html $)
  eqcomi $p |- u = t $=
    nt nu weq nu nt weq eqcomi.1 nt nu eq-sym ax-mp $.
$}

$( Equality is symmetric, as a biconditional.
   set.mm analogue: https://us.metamath.org/mpeuni/eqcom.html $)
eqcom $p |- ( t = u <-> u = t ) $=
  nt nu weq nu nt weq nt nu eq-sym nu nt eq-sym impbii $.

${
  eqcomd.1 $e |- ( ph -> t = u ) $.
  $( Deduction form of eq-sym
     set.mm analogue: https://us.metamath.org/mpeuni/eqcomd.html $)
  eqcomd $p |- ( ph -> u = t ) $=
    wph nt nu weq nu nt weq eqcomd.1 nt nu eq-sym syl $.
$}

${
  eqtri.1 $e |- t = u $.
  eqtri.2 $e |- u = v $.
  $( Chain two equalities; inference form of eq-tr
     set.mm analogue: https://us.metamath.org/mpeuni/eqtri.html $)
  eqtri $p |- t = v $=
    nt nu weq nu nv weq nt nv weq eqtri.1 eqtri.2 nt nu nv eq-tr mp2 $.
$}

${
  eqtr3i.1 $e |- t = u $.
  eqtr3i.2 $e |- t = v $.
  $( Two terms equal to a common left side are equal.
     set.mm analogue: https://us.metamath.org/mpeuni/eqtr3i.html $)
  eqtr3i $p |- u = v $=
    nu nt nv nt nu eqtr3i.1 eqcomi eqtr3i.2 eqtri $.
$}

${
  eqtr4i.1 $e |- t = u $.
  eqtr4i.2 $e |- v = u $.
  $( Two terms equal to a common right side are equal.
     set.mm analogue: https://us.metamath.org/mpeuni/eqtr4i.html $)
  eqtr4i $p |- t = v $=
    nt nu nv eqtr4i.1 nv nu eqtr4i.2 eqcomi eqtri $.
$}

${
  3eqtri.1 $e |- t = u $.
  3eqtri.2 $e |- u = v $.
  3eqtri.3 $e |- v = w $.
  $( Chain three equalities.
     set.mm analogue: https://us.metamath.org/mpeuni/3eqtri.html $)
  3eqtri $p |- t = w $=
    nt nu nw 3eqtri.1 nu nv nw 3eqtri.2 3eqtri.3 eqtri eqtri $.
$}

${
  eqtrd.1 $e |- ( ph -> t = u ) $.
  eqtrd.2 $e |- ( ph -> u = v ) $.
  $( Deduction form of eq-tr
     set.mm analogue: https://us.metamath.org/mpeuni/eqtrd.html $)
  eqtrd $p |- ( ph -> t = v ) $=
    wph nu nv weq nt nv weq eqtrd.2 wph nt nu weq nu nv weq nt nv weq wi
    eqtrd.1 nt nu nv eq-tr syl mpd $.
$}

$( Equality: replacing either side of an equation. $)

$( Replace the left side of an equation.
   set.mm analogue: https://us.metamath.org/mpeuni/eqeq1.html $)
eqeq1 $p |- ( t = u -> ( t = v <-> u = v ) ) $=
  nt nu weq nt nv weq nu nv weq nt nu weq nu nt weq nt nv weq nu nv weq wi nt
  nu eq-sym nu nt nv eq-tr syl nt nu nv eq-tr impbid $.

$( Replace the right side of an equation.
   set.mm analogue: https://us.metamath.org/mpeuni/eqeq2.html $)
eqeq2 $p |- ( t = u -> ( v = t <-> v = u ) ) $=
  nt nu weq nv nt weq nv nu weq nv nt weq nt nu weq nv nu weq nv nt nu eq-tr
  com12 nt nu weq nu nt weq nv nu weq nv nt weq wi nt nu eq-sym nv nu weq nu nt
  weq nv nt weq nv nu nt eq-tr com12 syl impbid $.

${
  eqeq12i.1 $e |- t = u $.
  eqeq12i.2 $e |- v = w $.
  $( Replace both sides of an equation.
     set.mm analogue: https://us.metamath.org/mpeuni/eqeq12i.html $)
  eqeq12i $p |- ( t = v <-> u = w ) $=
    nt nv weq nu nv weq nu nw weq nt nu weq nt nv weq nu nv weq wb eqeq12i.1 nt
    nu nv eqeq1 ax-mp nv nw weq nu nv weq nu nw weq wb eqeq12i.2 nv nw nu eqeq2
    ax-mp bitri $.
$}

${
  eqeq12d.1 $e |- ( ph -> t = u ) $.
  eqeq12d.2 $e |- ( ph -> v = w ) $.
  $( Replace both sides of an equation, under a common antecedent.
     set.mm analogue: https://us.metamath.org/mpeuni/eqeq12d.html $)
  eqeq12d $p |- ( ph -> ( t = v <-> u = w ) ) $=
    wph nt nv weq nu nv weq nu nw weq wph nt nu weq nt nv weq nu nv weq wb
    eqeq12d.1 nt nu nv eqeq1 syl wph nv nw weq nu nv weq nu nw weq wb eqeq12d.2
    nv nw nu eqeq2 syl bitrd $.
$}

$( Congruence for S, + and *. set.mm states these once for a general
   operation F (oveq1, oveq2, oveq12 and their i/d forms);
   we have fixed operations, so add/mul replace ov in the labels. $)

${
  suceqi.1 $e |- t = u $.
  $( Inference form of eq-s
     cf. set.mm: https://us.metamath.org/mpeuni/suceq.html $)
  suceqi $p |- S t = S u $=
    nt nu weq nt nS nu nS weq suceqi.1 nt nu eq-s ax-mp $.
$}

${
  suceqd.1 $e |- ( ph -> t = u ) $.
  $( Deduction form of eq-s
     set.mm analogue: https://us.metamath.org/mpeuni/suceqd.html $)
  suceqd $p |- ( ph -> S t = S u ) $=
    wph nt nu weq nt nS nu nS weq suceqd.1 nt nu eq-s syl $.
$}

$( Rewrite the left argument of +
   cf. set.mm: https://us.metamath.org/mpeuni/oveq1.html $)
addeq1 $p |- ( t = u -> ( t + v ) = ( u + v ) ) $=
  nt nu weq nv nv weq nt nv nadd nu nv nadd weq nv eq-refl nt nu nv nv eq-add
  mpi $.

$( Rewrite the right argument of +
   cf. set.mm: https://us.metamath.org/mpeuni/oveq2.html $)
addeq2 $p |- ( t = u -> ( v + t ) = ( v + u ) ) $=
  nv nv weq nt nu weq nv nt nadd nv nu nadd weq wi nv eq-refl nv nv nt nu
  eq-add ax-mp $.

$( Rewrite the left argument of *
   cf. set.mm: https://us.metamath.org/mpeuni/oveq1.html $)
muleq1 $p |- ( t = u -> ( t * v ) = ( u * v ) ) $=
  nt nu weq nv nv weq nt nv nmul nu nv nmul weq nv eq-refl nt nu nv nv eq-mul
  mpi $.

$( Rewrite the right argument of *
   cf. set.mm: https://us.metamath.org/mpeuni/oveq2.html $)
muleq2 $p |- ( t = u -> ( v * t ) = ( v * u ) ) $=
  nv nv weq nt nu weq nv nt nmul nv nu nmul weq wi nv eq-refl nv nv nt nu
  eq-mul ax-mp $.

${
  addeq1i.1 $e |- t = u $.
  $( Inference form of addeq1
     cf. set.mm: https://us.metamath.org/mpeuni/oveq1i.html $)
  addeq1i $p |- ( t + v ) = ( u + v ) $=
    nt nu weq nt nv nadd nu nv nadd weq addeq1i.1 nt nu nv addeq1 ax-mp $.
$}

${
  addeq1d.1 $e |- ( ph -> t = u ) $.
  $( Deduction form of addeq1
     cf. set.mm: https://us.metamath.org/mpeuni/oveq1d.html $)
  addeq1d $p |- ( ph -> ( t + v ) = ( u + v ) ) $=
    wph nt nu weq nt nv nadd nu nv nadd weq addeq1d.1 nt nu nv addeq1 syl $.
$}

${
  addeq2i.1 $e |- t = u $.
  $( Inference form of addeq2
     cf. set.mm: https://us.metamath.org/mpeuni/oveq2i.html $)
  addeq2i $p |- ( v + t ) = ( v + u ) $=
    nt nu weq nv nt nadd nv nu nadd weq addeq2i.1 nt nu nv addeq2 ax-mp $.
$}

${
  addeq2d.1 $e |- ( ph -> t = u ) $.
  $( Deduction form of addeq2
     cf. set.mm: https://us.metamath.org/mpeuni/oveq2d.html $)
  addeq2d $p |- ( ph -> ( v + t ) = ( v + u ) ) $=
    wph nt nu weq nv nt nadd nv nu nadd weq addeq2d.1 nt nu nv addeq2 syl $.
$}

${
  muleq1i.1 $e |- t = u $.
  $( Inference form of muleq1
     cf. set.mm: https://us.metamath.org/mpeuni/oveq1i.html $)
  muleq1i $p |- ( t * v ) = ( u * v ) $=
    nt nu weq nt nv nmul nu nv nmul weq muleq1i.1 nt nu nv muleq1 ax-mp $.
$}

${
  muleq1d.1 $e |- ( ph -> t = u ) $.
  $( Deduction form of muleq1
     cf. set.mm: https://us.metamath.org/mpeuni/oveq1d.html $)
  muleq1d $p |- ( ph -> ( t * v ) = ( u * v ) ) $=
    wph nt nu weq nt nv nmul nu nv nmul weq muleq1d.1 nt nu nv muleq1 syl $.
$}

${
  muleq2i.1 $e |- t = u $.
  $( Inference form of muleq2
     cf. set.mm: https://us.metamath.org/mpeuni/oveq2i.html $)
  muleq2i $p |- ( v * t ) = ( v * u ) $=
    nt nu weq nv nt nmul nv nu nmul weq muleq2i.1 nt nu nv muleq2 ax-mp $.
$}

${
  muleq2d.1 $e |- ( ph -> t = u ) $.
  $( Deduction form of muleq2
     cf. set.mm: https://us.metamath.org/mpeuni/oveq2d.html $)
  muleq2d $p |- ( ph -> ( v * t ) = ( v * u ) ) $=
    wph nt nu weq nv nt nmul nv nu nmul weq muleq2d.1 nt nu nv muleq2 syl $.
$}

${
  addeq12i.1 $e |- t = u $.
  addeq12i.2 $e |- v = w $.
  $( Rewrite both arguments of +; inference form of eq-add
     cf. set.mm: https://us.metamath.org/mpeuni/oveq12i.html $)
  addeq12i $p |- ( t + v ) = ( u + w ) $=
    nt nu weq nv nw weq nt nv nadd nu nw nadd weq addeq12i.1 addeq12i.2 nt nu
    nv nw eq-add mp2 $.
$}

${
  addeq12d.1 $e |- ( ph -> t = u ) $.
  addeq12d.2 $e |- ( ph -> v = w ) $.
  $( Rewrite both arguments of +, under a common antecedent.
     cf. set.mm: https://us.metamath.org/mpeuni/oveq12d.html $)
  addeq12d $p |- ( ph -> ( t + v ) = ( u + w ) ) $=
    wph nt nv nadd nu nv nadd nu nw nadd wph nt nu nv addeq12d.1 addeq1d wph nv
    nw nu addeq12d.2 addeq2d eqtrd $.
$}

${
  muleq12i.1 $e |- t = u $.
  muleq12i.2 $e |- v = w $.
  $( Rewrite both arguments of *; inference form of eq-mul
     cf. set.mm: https://us.metamath.org/mpeuni/oveq12i.html $)
  muleq12i $p |- ( t * v ) = ( u * w ) $=
    nt nu weq nv nw weq nt nv nmul nu nw nmul weq muleq12i.1 muleq12i.2 nt nu
    nv nw eq-mul mp2 $.
$}

${
  muleq12d.1 $e |- ( ph -> t = u ) $.
  muleq12d.2 $e |- ( ph -> v = w ) $.
  $( Rewrite both arguments of *, under a common antecedent.
     cf. set.mm: https://us.metamath.org/mpeuni/oveq12d.html $)
  muleq12d $p |- ( ph -> ( t * v ) = ( u * w ) ) $=
    wph nt nv nmul nu nv nmul nu nw nmul wph nt nu nv muleq12d.1 muleq1d wph nv
    nw nu muleq12d.2 muleq2d eqtrd $.
$}

$( Successor: zero, injectivity, and distinguishing numerals. $)

$( A successor is not zero; zns with the sides exchanged.
   set.mm analogue: https://us.metamath.org/mpeuni/nsuceq0.html $)
nsuceq0 $p |- -. S t = 0 $=
  nt nS n0 weq n0 nt nS weq nt zns nt nS n0 eq-sym mto $.

$( Successor preserves and reflects equality.
   set.mm analogue: https://us.metamath.org/mpeuni/suc11reg.html $)
suc11reg $p |- ( S t = S u <-> t = u ) $=
  nt nS nu nS weq nt nu weq nt nu s-inj nt nu eq-s impbii $.

${
  eqnetri.1 $e |- t = u $.
  eqnetri.2 $e |- -. u = v $.
  $( Carry a disequation along an equation.
     set.mm analogue: https://us.metamath.org/mpeuni/eqnetri.html $)
  eqnetri $p |- -. t = v $=
    nt nv weq nu nv weq eqnetri.2 nu nt weq nt nv weq nu nv weq wi nt nu
    eqnetri.1 eqcomi nu nt nv eq-tr ax-mp mto $.
$}

$( Numerals.  Each numeral is defined as the successor of the previous
   one.  Addition and multiplication recurse on the left argument
   (add-sl, mul-sl), so a sum or product is computed by unfolding the
   left numeral's definition and using one with a smaller left argument. $)



$( One is not zero.
   cf. set.mm: https://us.metamath.org/mpeuni/ax-1ne0.html $)
1ne0 $p |- -. 1 = 0 $=
  n1 n0 nS n0 df-1 n0 nsuceq0 eqnetri $.

$( Two is not one: by s-inj, one would equal zero.
   cf. set.mm: https://us.metamath.org/mpeuni/1ne2.html $)
2ne1 $p |- -. 2 = 1 $=
  n2 n1 weq n1 n0 weq 1ne0 n2 n1 weq n1 nS n0 nS weq n1 n0 weq n2 n1 weq n1 nS
  n0 nS weq n2 n1 nS n1 n0 nS df-2 df-1 eqeq12i biimpi n1 n0 s-inj syl mto $.

$( Zero plus zero; an instance of add-0l
   set.mm analogue: https://us.metamath.org/mpeuni/00id.html $)
00id $p |- ( 0 + 0 ) = 0 $=
  n0 add-0l $.

$( If t is the successor of u and ( u + 0 ) = u, then ( t + 0 ) = t.
   Used once per numeral below; the general law addrid needs induction. $)
${
  successor-lemma.1 $e |- t = S u $.
  successor-lemma.2 $e |- ( u + 0 ) = u $.
  successor-lemma $p |- ( t + 0 ) = t $=
    nt n0 nadd nu nS nt nt n0 nadd nu nS n0 nadd nu n0 nadd nS nu nS nt nu nS n0
    successor-lemma.1 addeq1i nu n0 add-sl nu n0 nadd nu successor-lemma.2 suceqi
    3eqtri successor-lemma.1 eqtr4i $.
$}

$( 1 + 0 = 1
   set.mm analogue: https://us.metamath.org/mpeuni/1p0e1.html $)
1p0e1 $p |- ( 1 + 0 ) = 1 $=
  n1 n0 df-1 00id successor-lemma $.

$( 2 + 0 = 2. Hmm, it's starting to look strangely like induction, huh? $)
2p0e2 $p |- ( 2 + 0 ) = 2 $=
  n2 n1 df-2 1p0e1 successor-lemma $.

$( 3 + 0 = 3 $)
3p0e3 $p |- ( 3 + 0 ) = 3 $=
  n3 n2 df-3 2p0e2 successor-lemma $.

$( 1 + 1 = 2
   set.mm analogue: https://us.metamath.org/mpeuni/1p1e2.html $)
1p1e2 $p |- ( 1 + 1 ) = 2 $=
  n1 n1 nadd n1 nS n2 n1 n1 nadd n0 nS n1 nadd n0 n1 nadd nS n1 nS n1 n0 nS n1
  df-1 addeq1i n0 n1 add-sl n0 n1 nadd n1 n1 add-0l suceqi 3eqtri df-2 eqtr4i $.

$( 1 + 2 = 3
   set.mm analogue: https://us.metamath.org/mpeuni/1p2e3.html $)
1p2e3 $p |- ( 1 + 2 ) = 3 $=
  n1 n2 nadd n2 nS n3 n1 n2 nadd n0 nS n2 nadd n0 n2 nadd nS n2 nS n1 n0 nS n2
  df-1 addeq1i n0 n2 add-sl n0 n2 nadd n2 n2 add-0l suceqi 3eqtri df-3 eqtr4i $.

$( 2 + 2 = 4
   set.mm analogue: https://us.metamath.org/mpeuni/2p2e4.html $)
2p2e4 $p |- ( 2 + 2 ) = 4 $=
  n2 n2 nadd n3 nS n4 n2 n2 nadd n1 nS n2 nadd n1 n2 nadd nS n3 nS n2 n1 nS n2
  df-2 addeq1i n1 n2 add-sl n1 n2 nadd n3 1p2e3 suceqi 3eqtri df-4 eqtr4i $.

$( 3 + 2 = 5
   set.mm analogue: https://us.metamath.org/mpeuni/3p2e5.html $)
3p2e5 $p |- ( 3 + 2 ) = 5 $=
  n3 n2 nadd n4 nS n5 n3 n2 nadd n2 nS n2 nadd n2 n2 nadd nS n4 nS n3 n2 nS n2
  df-3 addeq1i n2 n2 add-sl n2 n2 nadd n4 2p2e4 suceqi 3eqtri df-5 eqtr4i $.

$( 1 + 3 = 4
   set.mm analogue: https://us.metamath.org/mpeuni/1p3e4.html $)
1p3e4 $p |- ( 1 + 3 ) = 4 $=
  n1 n3 nadd n3 nS n4 n1 n3 nadd n0 nS n3 nadd n0 n3 nadd nS n3 nS n1 n0 nS n3
  df-1 addeq1i n0 n3 add-sl n0 n3 nadd n3 n3 add-0l suceqi 3eqtri df-4 eqtr4i $.

$( 2 + 3 = 5
   set.mm analogue: https://us.metamath.org/mpeuni/2p3e5.html $)
2p3e5 $p |- ( 2 + 3 ) = 5 $=
  n2 n3 nadd n4 nS n5 n2 n3 nadd n1 nS n3 nadd n1 n3 nadd nS n4 nS n2 n1 nS n3
  df-2 addeq1i n1 n3 add-sl n1 n3 nadd n4 1p3e4 suceqi 3eqtri df-5 eqtr4i $.

$( 3 + 3 = 6
   set.mm analogue: https://us.metamath.org/mpeuni/3p3e6.html $)
3p3e6 $p |- ( 3 + 3 ) = 6 $=
  n3 n3 nadd n5 nS n6 n3 n3 nadd n2 nS n3 nadd n2 n3 nadd nS n5 nS n3 n2 nS n3
  df-3 addeq1i n2 n3 add-sl n2 n3 nadd n5 2p3e5 suceqi 3eqtri df-6 eqtr4i $.

$( 1 + 4 = 5
   set.mm analogue: https://us.metamath.org/mpeuni/1p4e5.html $)
1p4e5 $p |- ( 1 + 4 ) = 5 $=
  n1 n4 nadd n4 nS n5 n1 n4 nadd n0 nS n4 nadd n0 n4 nadd nS n4 nS n1 n0 nS n4
  df-1 addeq1i n0 n4 add-sl n0 n4 nadd n4 n4 add-0l suceqi 3eqtri df-5 eqtr4i $.

$( 2 + 4 = 6
   set.mm analogue: https://us.metamath.org/mpeuni/2p4e6.html $)
2p4e6 $p |- ( 2 + 4 ) = 6 $=
  n2 n4 nadd n5 nS n6 n2 n4 nadd n1 nS n4 nadd n1 n4 nadd nS n5 nS n2 n1 nS n4
  df-2 addeq1i n1 n4 add-sl n1 n4 nadd n5 1p4e5 suceqi 3eqtri df-6 eqtr4i $.

$( A commutativity instance: both sides have the same value.  The general
   law needs induction. $)
3p2e2p3 $p |- ( 3 + 2 ) = ( 2 + 3 ) $=
  n3 n2 nadd n5 n2 n3 nadd 3p2e5 2p3e5 eqtr4i $.

$( 1 * 2 = 2 $)
1t2e2 $p |- ( 1 * 2 ) = 2 $=
  n1 n2 nmul n2 n0 nadd n2 n1 n2 nmul n0 nS n2 nmul n2 n0 n2 nmul nadd n2 n0
  nadd n1 n0 nS n2 df-1 muleq1i n0 n2 mul-sl n0 n2 nmul n0 n2 n2 mul-0l addeq2i
  3eqtri 2p0e2 eqtri $.

$( 2 * 2 = 4
   set.mm analogue: https://us.metamath.org/mpeuni/2t2e4.html $)
2t2e4 $p |- ( 2 * 2 ) = 4 $=
  n2 n2 nmul n2 n2 nadd n4 n2 n2 nmul n1 nS n2 nmul n2 n1 n2 nmul nadd n2 n2
  nadd n2 n1 nS n2 df-2 muleq1i n1 n2 mul-sl n1 n2 nmul n2 n2 1t2e2 addeq2i
  3eqtri 2p2e4 eqtri $.

$( 3 * 2 = 6
   set.mm analogue: https://us.metamath.org/mpeuni/3t2e6.html $)
3t2e6 $p |- ( 3 * 2 ) = 6 $=
  n3 n2 nmul n2 n4 nadd n6 n3 n2 nmul n2 nS n2 nmul n2 n2 n2 nmul nadd n2 n4
  nadd n3 n2 nS n2 df-3 muleq1i n2 n2 mul-sl n2 n2 nmul n4 n2 2t2e4 addeq2i
  3eqtri 2p4e6 eqtri $.

$( 1 * 3 = 3 $)
1t3e3 $p |- ( 1 * 3 ) = 3 $=
  n1 n3 nmul n3 n0 nadd n3 n1 n3 nmul n0 nS n3 nmul n3 n0 n3 nmul nadd n3 n0
  nadd n1 n0 nS n3 df-1 muleq1i n0 n3 mul-sl n0 n3 nmul n0 n3 n3 mul-0l addeq2i
  3eqtri 3p0e3 eqtri $.

$( 2 * 3 = 6
   set.mm analogue: https://us.metamath.org/mpeuni/2t3e6.html $)
2t3e6 $p |- ( 2 * 3 ) = 6 $=
  n2 n3 nmul n3 n3 nadd n6 n2 n3 nmul n1 nS n3 nmul n3 n1 n3 nmul nadd n3 n3
  nadd n2 n1 nS n3 df-2 muleq1i n1 n3 mul-sl n1 n3 nmul n3 n3 1t3e3 addeq2i
  3eqtri 3p3e6 eqtri $.

$( A commutativity instance for multiplication. $)
2t3e3t2 $p |- ( 2 * 3 ) = ( 3 * 2 ) $=
  n2 n3 nmul n6 n3 n2 nmul 2t3e6 3t2e6 eqtr4i $.
