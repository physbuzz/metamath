$( Arithmetic with first-order induction.  Includes arith-common.mm but
   not arith-qf.mm: here vtonum and the induction rule are theorems. $)
$[ arith-common.mm $]

$( Variables, declared as in arith-qf.mm $)
$c var $.
$v x y $.
vx $f var x $.  vy $f var y $.
nx $a num x $.  ny $a num y $.

$( Quantifiers $)
$c A. E. $.
wal $a wff A. x ph $.
wex $a wff E. x ph $.

$( "Some x" is "not every x is not"
   set.mm analogue: https://us.metamath.org/mpeuni/df-ex.html $)
df-ex $a |- ( E. x ph <-> -. A. x -. ph ) $.

$( Generalization: what we prove about x, we prove for every x
   set.mm analogue: https://us.metamath.org/mpeuni/ax-gen.html $)
${
  ax-gen.1 $e |- ph $.
  ax-gen $a |- A. x ph $.
$}

$( A. distributes over ->
   set.mm analogue: https://us.metamath.org/mpeuni/ax-4.html $)
ax-4 $a |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $.

$( Quantifying over a variable that does not occur does nothing
   set.mm analogue: https://us.metamath.org/mpeuni/ax-5.html $)
${
  $d x ph $.
  ax-5 $a |- ( ph -> A. x ph ) $.
$}

$( Every term is equal to something.  set.mm states this for variables
   (ax-6), and for class terms it is a hypothesis A e. V
   cf. set.mm: https://us.metamath.org/mpeuni/ax6ev.html $)
${
  $d x t $.
  ax-6 $a |- E. x x = t $.
$}

$( Inference form of ax-4
   set.mm analogue: https://us.metamath.org/mpeuni/alimi.html $)
${
  alimi.1 $e |- ( ph -> ps ) $.
  alimi $p |- ( A. x ph -> A. x ps ) $=
    wph wps wi vx wal wph vx wal wps vx wal wi wph wps wi vx alimi.1 ax-gen wph
    wps vx ax-4 ax-mp $.
$}

${
  $d x t $. $d x ps $.
  $( If every x equal to t satisfies ps, and x is not in ps, then ps.
     This is where ax-6 is needed: otherwise nothing might equal t $)
  spcvlem $p |- ( A. x ( x = t -> ps ) -> ps ) $=
    vx nx nt weq wps wi vx wal vx nx nt weq wn vx wal wn wps vx nx nt weq vx
    wex vx nx nt weq wn vx wal wn nt vx ax-6 vx nx nt weq vx df-ex mpbi vx nx
    nt weq wps wi vx wal wps vx nx nt weq wn vx wal wps wn wps wn vx wal vx nx
    nt weq wps wi vx wal vx nx nt weq wn vx wal wps wn vx ax-5 vx nx nt weq wps
    wi vx wal wps wn vx nx nt weq wn wi vx wal wps wn vx wal vx nx nt weq wn vx
    wal wi vx nx nt weq wps wi wps wn vx nx nt weq wn wi vx vx nx nt weq wps
    con3 alimi wps wn vx nx nt weq wn vx ax-4 syl syl5 con1d mpi $.

  spcv.1 $e |- ( x = t -> ( ph <-> ps ) ) $.
  $( Specialization at a term
     cf. set.mm: https://us.metamath.org/mpeuni/spcv.html $)
  spcv $p |- ( A. x ph -> ps ) $=
    wph vx wal vx nx nt weq wps wi vx wal wps wph vx nx nt weq wps wi vx vx nx
    nt weq wph wps vx nx nt weq wph wps spcv.1 biimpd com12 alimi wps nt vx
    spcvlem syl $.

  vtonum.2 $e |- ph $.
  $( The rule we had to assume in arith-qf.mm, now a theorem
     cf. set.mm: https://us.metamath.org/mpeuni/vtocl.html $)
  vtonum $p |- ps $=
    wph vx wal wps wph vx vtonum.2 ax-gen wph wps nt vx spcv.1 spcv ax-mp $.
$}

$( Induction, one of Peano's axioms.  A. x ( x = t -> ph ) says "ph holds
   at t", so this reads: if ph holds at 0, and for every y ph at y implies
   ph at S y, then ph holds for every x
   cf. set.mm: https://us.metamath.org/mpeuni/peano5.html $)
${
  $d x y $. $d y ph $.
  ax-peano $a |- ( ( A. x ( x = 0 -> ph )
      /\ A. y ( A. x ( x = y -> ph ) -> A. x ( x = S y -> ph ) ) ) -> A. x ph ) $.
$}

$( The induction rule ax-ind of arith-qf.mm, with the same hypotheses
   cf. set.mm: https://us.metamath.org/mpeuni/nn0ind.html $)
${
  $d x ps $. $d x ch $. $d x th $. $d x ta $. $d x t $.
  $d x y $. $d y ph $.
  ind.at-zero $e |- ( x = 0 -> ( ph <-> ps ) ) $.
  ind.at-var $e |- ( x = y -> ( ph <-> ch ) ) $.
  ind.at-succvar $e |- ( x = S y -> ( ph <-> th ) ) $.
  ind.at-num $e |- ( x = t -> ( ph <-> ta ) ) $.
  ind.base $e |- ps $.
  ind.step $e |- ( ch -> th ) $.
  ind $p |- ta $=
    wph vx wal wta vx nx n0 weq wph wi vx wal vx nx vy nx weq wph wi vx wal vx
    nx vy nx nS weq wph wi vx wal wi vy wal wph vx wal vx nx n0 weq wph wi vx
    vx nx n0 weq wps wph ind.base vx nx n0 weq wph wps ind.at-zero biimprd mpi ax-gen vx
    nx vy nx weq wph wi vx wal vx nx vy nx nS weq wph wi vx wal wi vy vx nx vy
    nx weq wph wi vx wal wth vx nx vy nx nS weq wph wi vx wal vx nx vy nx weq
    wph wi vx wal wch wth vx nx vy nx weq wph wi vx wal vy nx vy nx weq wch vy
    nx eq-refl vx nx vy nx weq wph wi vy nx vy nx weq wch wi vy nx vx vx nx vy
    nx weq vx nx vy nx weq vy nx vy nx weq wph wch vx nx vy nx vy nx eqeq1
    ind.at-var imbi12d spcv mpi ind.step syl wth wth vx wal vx nx vy nx nS weq wph wi
    vx wal wth vx ax-5 wth vx nx vy nx nS weq wph wi vx vx nx vy nx nS weq wth
    wph vx nx vy nx nS weq wph wth ind.at-succvar biimprd com12 alimi syl syl ax-gen wph
    vx vy ax-peano mp2an wph wta nt vx ind.at-num spcv ax-mp $.
$}

$( The four at- hypotheses for addrid, as in arith-qf.mm $)
addrid-at $p |- ( t = u -> ( ( t + 0 ) = t <-> ( u + 0 ) = u ) ) $=
  nt nu weq nt n0 nadd nu n0 nadd nt nu nt nu n0 addeq1 nt nu weq id eqeq12d $.

$( The induction step for addrid, as in arith-qf.mm $)
addrid-step $p |- ( ( y + 0 ) = y -> ( S y + 0 ) = S y ) $=
  vy ny n0 nadd vy ny weq vy ny nS n0 nadd vy ny n0 nadd nS vy ny nS
  vy ny nS n0 nadd vy ny n0 nadd nS weq vy ny n0 nadd vy ny weq vy ny n0 add-sl a1i
  vy ny n0 nadd vy ny weq vy ny n0 nadd vy ny vy ny n0 nadd vy ny weq id suceqd
  eqtrd $.

$( Zero is a right identity for addition
   set.mm analogue: https://us.metamath.org/mpeuni/addrid.html $)
${
  $d x t $. $d x y $.
  addrid $p |- ( t + 0 ) = t $=
    vx nx n0 nadd vx nx weq n0 n0 nadd n0 weq vy ny n0 nadd vy ny weq
    vy ny nS n0 nadd vy ny nS weq nt n0 nadd nt weq nt vx vy
    vx nx n0 addrid-at vx nx vy ny addrid-at vx nx vy ny nS addrid-at
    vx nx nt addrid-at 00id vy addrid-step ind $.
$}
