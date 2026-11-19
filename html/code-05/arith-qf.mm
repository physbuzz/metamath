$[ arith-common.mm $]

$c var $.
$v x y $.
vx $f var x $.  vy $f var y $.
nx $a num x $.  ny $a num y $.

$( Substituting 0 for x by applying axioms. $)
xzero $p |- ( x = 0 -> ( x + 0 ) = x ) $=
  vx nx n0 weq vx nx n0 nadd n0 vx nx vx nx n0 weq vx nx n0 nadd n0 n0 nadd n0
  vx nx n0 n0 addeq1 n0 n0 nadd n0 weq vx nx n0 weq n0 add-0l a1i eqtrd
  vx nx n0 eq-sym eqtrd $.

$( Eliminate x from a formula by setting it to t $)
${
  $d x ps $. $d x t $.
  vtonum.1 $e |- ( x = t -> ( ph <-> ps ) ) $.
  vtonum.2 $e |- ph $.
  vtonum $a |- ps $.
$}

$( Quantifier-free induction.  ph is the formula in x; ps, ch, th and ta
   are ph at 0, y, S y and t $)
${
  $d x ps $. $d x ta $. $d x t $.
  $d x ch $. $d x th $.
  $d x y $. $d y ph $.
  ax-ind.at-zero $e |- ( x = 0 -> ( ph <-> ps ) ) $.
  ax-ind.at-var $e |- ( x = y -> ( ph <-> ch ) ) $.
  ax-ind.at-succvar $e |- ( x = S y -> ( ph <-> th ) ) $.
  ax-ind.at-num $e |- ( x = t -> ( ph <-> ta ) ) $.
  ax-ind.base $e |- ps $.
  ax-ind.step $e |- ( ch -> th ) $.
  ax-ind $a |- ta $.
$}

$( The four at- hypotheses for addrid, all instances of this. $)
addrid-at $p |- ( t = u -> ( ( t + 0 ) = t <-> ( u + 0 ) = u ) ) $=
  nt nu weq nt n0 nadd nu n0 nadd nt nu nt nu n0 addeq1 nt nu weq id eqeq12d $.

$( The induction step for addrid; closed form of successor-lemma $)
addrid-step $p |- ( ( y + 0 ) = y -> ( S y + 0 ) = S y ) $=
  vy ny n0 nadd vy ny weq vy ny nS n0 nadd vy ny n0 nadd nS vy ny nS
  vy ny nS n0 nadd vy ny n0 nadd nS weq vy ny n0 nadd vy ny weq vy ny n0 add-sl a1i
  vy ny n0 nadd vy ny weq vy ny n0 nadd vy ny vy ny n0 nadd vy ny weq id suceqd
  eqtrd $.

$( Zero is a right identity for addition.
   set.mm analogue: https://us.metamath.org/mpeuni/addrid.html $)
${
  $d x t $. $d x y $.
  addrid $p |- ( t + 0 ) = t $=
    vx nx n0 nadd vx nx weq n0 n0 nadd n0 weq vy ny n0 nadd vy ny weq
    vy ny nS n0 nadd vy ny nS weq nt n0 nadd nt weq nt vx vy
    vx nx n0 addrid-at vx nx vy ny addrid-at vx nx vy ny nS addrid-at
    vx nx nt addrid-at 00id vy addrid-step ax-ind $.
$}
