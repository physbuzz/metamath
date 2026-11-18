$[ prop.mm $]

$( Terms and equations. $)
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
$( CD, case distinction, zero-or-s. Inactive: this is the axiom we set aside.
${
  $d y t $.
  zero-or-s $a |- ( t = 0 \/ E. y t = S y ) $.
$}
$)
$( SI, successor injectivity, s-inj $)
s-inj $a |- ( S t = S u -> t = u ) $.

$( Joint congruence with the equality premises in reverse order. $)
eq-add-rev $p |- ( t = u -> ( v = w -> ( v + t ) = ( w + u ) ) ) $=
  nv nw weq nt nu weq nv nt nadd nw nu nadd weq nv nw nt nu eq-add com12 $.

$( Joint congruence with the equality premises in reverse order. $)
eq-mul-rev $p |- ( t = u -> ( v = w -> ( v * t ) = ( w * u ) ) ) $=
  nv nw weq nt nu weq nv nt nmul nw nu nmul weq nv nw nt nu eq-mul com12 $.

$( A successor is not zero; reverse ZS using equality symmetry. $)
snz $p |- -. S t = 0 $=
  nt nS n0 weq n0 nt nS weq nt zns nt nS n0 eq-sym mto $.

eq-add-right $p |- ( t = u -> ( v + t ) = ( v + u ) ) $=
  nv nv weq nt nu weq nv nt nadd nv nu nadd weq wi nv eq-refl nt nu weq nv nv
  weq nv nt nadd nv nu nadd weq nt nu nv nv eq-add-rev com12 ax-mp $.

eq-add-left $p |- ( t = u -> ( t + v ) = ( u + v ) ) $=
  nv nv weq nt nu weq nt nv nadd nu nv nadd weq wi nv eq-refl nv nv nt nu
  eq-add-rev ax-mp $.

eq-mul-right $p |- ( t = u -> ( v * t ) = ( v * u ) ) $=
  nv nv weq nt nu weq nv nt nmul nv nu nmul weq wi nv eq-refl nt nu weq nv nv
  weq nv nt nmul nv nu nmul weq nt nu nv nv eq-mul-rev com12 ax-mp $.

eq-mul-left $p |- ( t = u -> ( t * v ) = ( u * v ) ) $=
  nv nv weq nt nu weq nt nv nmul nu nv nmul weq wi nv eq-refl nv nv nt nu
  eq-mul-rev ax-mp $.

${
eq-sym-d.1 $e |- ( ph -> t = u ) $.
eq-sym-d $p |- ( ph -> u = t ) $=
  wph nt nu weq nu nt weq eq-sym-d.1 nt nu eq-sym syl $.
$}

${
eq-trans-d.1 $e |- ( ph -> t = u ) $.
eq-trans-d.2 $e |- ( ph -> u = v ) $.
eq-trans-d $p |- ( ph -> t = v ) $=
  wph nu nv weq nt nv weq eq-trans-d.2 wph nt nu weq nu nv weq nt nv weq wi
  eq-trans-d.1 nt nu nv eq-tr syl mpd $.
$}

${
eq-succ-d.1 $e |- ( ph -> t = u ) $.
eq-succ-d $p |- ( ph -> S t = S u ) $=
  wph nt nu weq nt nS nu nS weq eq-succ-d.1 nt nu eq-s syl $.
$}

${
eq-add-rev-d.1 $e |- ( ph -> t = u ) $.
eq-add-rev-d.2 $e |- ( ph -> v = w ) $.
eq-add-rev-d $p |- ( ph -> ( v + t ) = ( w + u ) ) $=
  wph nv nt nadd nv nu nadd nw nu nadd wph nt nu weq nv nt nadd nv nu nadd weq
  eq-add-rev-d.1 nt nu nv eq-add-right syl wph nv nw weq nv nu nadd nw nu nadd
  weq eq-add-rev-d.2 nv nw nu eq-add-left syl eq-trans-d $.
$}

${
eq-mul-rev-d.1 $e |- ( ph -> t = u ) $.
eq-mul-rev-d.2 $e |- ( ph -> v = w ) $.
eq-mul-rev-d $p |- ( ph -> ( v * t ) = ( w * u ) ) $=
  wph nv nt nmul nv nu nmul nw nu nmul wph nt nu weq nv nt nmul nv nu nmul weq
  eq-mul-rev-d.1 nt nu nv eq-mul-right syl wph nv nw weq nv nu nmul nw nu nmul
  weq eq-mul-rev-d.2 nv nw nu eq-mul-left syl eq-trans-d $.
$}

${
eq-equal-d.1 $e |- ( ph -> t = u ) $.
eq-equal-d.2 $e |- ( ph -> v = w ) $.
eq-equal-d $p |- ( ph -> ( t = v -> u = w ) ) $=
  wph nt nv weq nu nv weq nu nw weq wph nu nt weq nt nv weq nu nv weq wi wph
  nt nu eq-equal-d.1 eq-sym-d nu nt nv eq-tr syl wph nv nw weq nu nv weq nu nw
  weq wi eq-equal-d.2 nu nv weq nv nw weq nu nw weq nu nv nw eq-tr com12 syl
  syld $.
$}

${
eq-symi.1 $e |- t = u $.
eq-symi $p |- u = t $=
  nt nu weq nu nt weq eq-symi.1 nt nu eq-sym ax-mp $.
$}

${
eq-tri.1 $e |- t = u $.
eq-tri.2 $e |- u = v $.
eq-tri $p |- t = v $=
  nu nv weq nt nv weq eq-tri.2 nt nu weq nu nv weq nt nv weq wi eq-tri.1 nt nu nv eq-tr ax-mp ax-mp $.
$}

${
eq-si.1 $e |- t = u $.
eq-si $p |- S t = S u $=
  nt nu weq nt nS nu nS weq eq-si.1 nt nu eq-s ax-mp $.
$}

${
eq-add-i.1 $e |- t = u $.
eq-add-i.2 $e |- v = w $.
eq-add-i $p |- ( t + v ) = ( u + w ) $=
 nv nw weq nt nv nadd nu nw nadd weq eq-add-i.2 nt nu weq nv nw weq nt nv nadd nu nw nadd weq wi eq-add-i.1 nt nu nv nw eq-add ax-mp ax-mp $.
$}

${
eq-mul-i.1 $e |- t = u $.
eq-mul-i.2 $e |- v = w $.
eq-mul-i $p |- ( t * v ) = ( u * w ) $=
 nv nw weq nt nv nmul nu nw nmul weq eq-mul-i.2 nt nu weq nv nw weq nt nv nmul nu nw nmul weq wi eq-mul-i.1 nt nu nv nw eq-mul ax-mp ax-mp $.
$}

$( 0 + 2 = 2, by left recursion. $)
add-0-2-value $p |- ( 0 + S S 0 ) = S S 0 $=
  n0 nS nS add-0l $.

$( 1 + 2 = 3, by left recursion. $)
add-1-2-value $p |- ( S 0 + S S 0 ) = S S S 0 $=
  n0 nS n0 nS nS nadd n0 n0 nS nS nadd nS n0 nS nS nS n0 n0 nS nS add-sl n0 n0
  nS nS nadd n0 nS nS add-0-2-value eq-si eq-tri $.

$( 2 + 2 = 4, by left recursion. $)
add-2-2-value $p |- ( S S 0 + S S 0 ) = S S S S 0 $=
  n0 nS nS n0 nS nS nadd n0 nS n0 nS nS nadd nS n0 nS nS nS nS n0 nS n0 nS nS
  add-sl n0 nS n0 nS nS nadd n0 nS nS nS add-1-2-value eq-si eq-tri $.

$( 3 + 2 = 5, by left recursion. $)
add-3-2-value $p |- ( S S S 0 + S S 0 ) = S S S S S 0 $=
  n0 nS nS nS n0 nS nS nadd n0 nS nS n0 nS nS nadd nS n0 nS nS nS nS nS n0 nS
  nS n0 nS nS add-sl n0 nS nS n0 nS nS nadd n0 nS nS nS nS add-2-2-value eq-si
  eq-tri $.

$( 0 + 3 = 3, by left recursion. $)
add-0-3-value $p |- ( 0 + S S S 0 ) = S S S 0 $=
  n0 nS nS nS add-0l $.

$( 1 + 3 = 4, by left recursion. $)
add-1-3-value $p |- ( S 0 + S S S 0 ) = S S S S 0 $=
  n0 nS n0 nS nS nS nadd n0 n0 nS nS nS nadd nS n0 nS nS nS nS n0 n0 nS nS nS
  add-sl n0 n0 nS nS nS nadd n0 nS nS nS add-0-3-value eq-si eq-tri $.

$( 2 + 3 = 5, by left recursion. $)
add-2-3-value $p |- ( S S 0 + S S S 0 ) = S S S S S 0 $=
  n0 nS nS n0 nS nS nS nadd n0 nS n0 nS nS nS nadd nS n0 nS nS nS nS nS n0 nS
  n0 nS nS nS add-sl n0 nS n0 nS nS nS nadd n0 nS nS nS nS add-1-3-value eq-si
  eq-tri $.

$( A ground commutativity instance: both sides have the same numeral value. $)
add-3-2 $p |- ( S S S 0 + S S 0 ) = ( S S 0 + S S S 0 ) $=
  n0 nS nS nS n0 nS nS nadd n0 nS nS nS nS nS n0 nS nS n0 nS nS nS nadd
  add-3-2-value n0 nS nS n0 nS nS nS nadd n0 nS nS nS nS nS add-2-3-value
  eq-symi eq-tri $.

$( 0 * 3 = 0, by left recursion. $)
mul-0-3-value $p |- ( 0 * S S S 0 ) = 0 $=
  n0 nS nS nS mul-0l $.

$( 0 + 0 = 0, by left recursion. $)
add-0-0-value $p |- ( 0 + 0 ) = 0 $=
  n0 add-0l $.

$( 1 + 0 = 1, by left recursion. $)
add-1-0-value $p |- ( S 0 + 0 ) = S 0 $=
  n0 nS n0 nadd n0 n0 nadd nS n0 nS n0 n0 add-sl n0 n0 nadd n0 add-0-0-value
  eq-si eq-tri $.

$( 2 + 0 = 2, by left recursion. $)
add-2-0-value $p |- ( S S 0 + 0 ) = S S 0 $=
  n0 nS nS n0 nadd n0 nS n0 nadd nS n0 nS nS n0 nS n0 add-sl n0 nS n0 nadd n0
  nS add-1-0-value eq-si eq-tri $.

$( 3 + 0 = 3, by left recursion. $)
add-3-0-value $p |- ( S S S 0 + 0 ) = S S S 0 $=
  n0 nS nS nS n0 nadd n0 nS nS n0 nadd nS n0 nS nS nS n0 nS nS n0 add-sl n0 nS
  nS n0 nadd n0 nS nS add-2-0-value eq-si eq-tri $.

$( 1 * 3 = 3, by left recursion. $)
mul-1-3-value $p |- ( S 0 * S S S 0 ) = S S S 0 $=
  n0 nS n0 nS nS nS nmul n0 nS nS nS n0 nadd n0 nS nS nS n0 nS n0 nS nS nS
  nmul n0 nS nS nS n0 n0 nS nS nS nmul nadd n0 nS nS nS n0 nadd n0 n0 nS nS nS
  mul-sl n0 nS nS nS n0 nS nS nS n0 n0 nS nS nS nmul n0 n0 nS nS nS eq-refl
  mul-0-3-value eq-add-i eq-tri add-3-0-value eq-tri $.

$( 3 + 3 = 6, by left recursion. $)
add-3-3-value $p |- ( S S S 0 + S S S 0 ) = S S S S S S 0 $=
  n0 nS nS nS n0 nS nS nS nadd n0 nS nS n0 nS nS nS nadd nS n0 nS nS nS nS nS
  nS n0 nS nS n0 nS nS nS add-sl n0 nS nS n0 nS nS nS nadd n0 nS nS nS nS nS
  add-2-3-value eq-si eq-tri $.

$( 2 * 3 = 6, by left recursion. $)
mul-2-3-value $p |- ( S S 0 * S S S 0 ) = S S S S S S 0 $=
  n0 nS nS n0 nS nS nS nmul n0 nS nS nS n0 nS nS nS nadd n0 nS nS nS nS nS nS
  n0 nS nS n0 nS nS nS nmul n0 nS nS nS n0 nS n0 nS nS nS nmul nadd n0 nS nS
  nS n0 nS nS nS nadd n0 nS n0 nS nS nS mul-sl n0 nS nS nS n0 nS nS nS n0 nS
  n0 nS nS nS nmul n0 nS nS nS n0 nS nS nS eq-refl mul-1-3-value eq-add-i
  eq-tri add-3-3-value eq-tri $.

$( 0 * 2 = 0, by left recursion. $)
mul-0-2-value $p |- ( 0 * S S 0 ) = 0 $=
  n0 nS nS mul-0l $.

$( 1 * 2 = 2, by left recursion. $)
mul-1-2-value $p |- ( S 0 * S S 0 ) = S S 0 $=
  n0 nS n0 nS nS nmul n0 nS nS n0 nadd n0 nS nS n0 nS n0 nS nS nmul n0 nS nS
  n0 n0 nS nS nmul nadd n0 nS nS n0 nadd n0 n0 nS nS mul-sl n0 nS nS n0 nS nS
  n0 n0 nS nS nmul n0 n0 nS nS eq-refl mul-0-2-value eq-add-i eq-tri
  add-2-0-value eq-tri $.

$( 2 * 2 = 4, by left recursion. $)
mul-2-2-value $p |- ( S S 0 * S S 0 ) = S S S S 0 $=
  n0 nS nS n0 nS nS nmul n0 nS nS n0 nS nS nadd n0 nS nS nS nS n0 nS nS n0 nS
  nS nmul n0 nS nS n0 nS n0 nS nS nmul nadd n0 nS nS n0 nS nS nadd n0 nS n0 nS
  nS mul-sl n0 nS nS n0 nS nS n0 nS n0 nS nS nmul n0 nS nS n0 nS nS eq-refl
  mul-1-2-value eq-add-i eq-tri add-2-2-value eq-tri $.

$( 0 + 4 = 4, by left recursion. $)
add-0-4-value $p |- ( 0 + S S S S 0 ) = S S S S 0 $=
  n0 nS nS nS nS add-0l $.

$( 1 + 4 = 5, by left recursion. $)
add-1-4-value $p |- ( S 0 + S S S S 0 ) = S S S S S 0 $=
  n0 nS n0 nS nS nS nS nadd n0 n0 nS nS nS nS nadd nS n0 nS nS nS nS nS n0 n0
  nS nS nS nS add-sl n0 n0 nS nS nS nS nadd n0 nS nS nS nS add-0-4-value eq-si
  eq-tri $.

$( 2 + 4 = 6, by left recursion. $)
add-2-4-value $p |- ( S S 0 + S S S S 0 ) = S S S S S S 0 $=
  n0 nS nS n0 nS nS nS nS nadd n0 nS n0 nS nS nS nS nadd nS n0 nS nS nS nS nS
  nS n0 nS n0 nS nS nS nS add-sl n0 nS n0 nS nS nS nS nadd n0 nS nS nS nS nS
  add-1-4-value eq-si eq-tri $.

$( 3 * 2 = 6, by left recursion. $)
mul-3-2-value $p |- ( S S S 0 * S S 0 ) = S S S S S S 0 $=
  n0 nS nS nS n0 nS nS nmul n0 nS nS n0 nS nS nS nS nadd n0 nS nS nS nS nS nS
  n0 nS nS nS n0 nS nS nmul n0 nS nS n0 nS nS n0 nS nS nmul nadd n0 nS nS n0
  nS nS nS nS nadd n0 nS nS n0 nS nS mul-sl n0 nS nS n0 nS nS n0 nS nS n0 nS
  nS nmul n0 nS nS nS nS n0 nS nS eq-refl mul-2-2-value eq-add-i eq-tri
  add-2-4-value eq-tri $.

$( A ground commutativity instance: both sides have the same numeral value. $)
mul-2-3 $p |- ( S S 0 * S S S 0 ) = ( S S S 0 * S S 0 ) $=
  n0 nS nS n0 nS nS nS nmul n0 nS nS nS nS nS nS n0 nS nS nS n0 nS nS nmul
  mul-2-3-value n0 nS nS nS n0 nS nS nmul n0 nS nS nS nS nS nS mul-3-2-value
  eq-symi eq-tri $.
