$[ prop.mm $]

$c setvar A. $.
$v x $.
vx $f setvar x $.
wal $a wff A. x ph $.

${ ax-gen.1 $e |- ph $.  ax-gen $a |- A. x ph $. $}
ax-4 $a |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $.

$( Lift an implication $)
${
  mpg.1 $e |- ( A. x ph -> ps ) $.
  mpg.2 $e |- ph $.
  mpg $p |- ps $= ? $.
$}

${
  alimi.1 $e |- ( ph -> ps ) $.
  alimi $p |- ( A. x ph -> A. x ps ) $= ? $.
$}

al2im $p |- ( A. x ( ph -> ( ps -> ch ) ) -> ( A. x ph -> ( A. x ps -> A. x ch ) ) ) $= ? $.

${
  al2imi.1 $e |- ( ph -> ( ps -> ch ) ) $.
  al2imi $p |- ( A. x ph -> ( A. x ps -> A. x ch ) ) $= ? $.
$}

$( Collect the conjuncts $)
${
  alanimi.1 $e |- ( ( ph /\ ps ) -> ch ) $.
  alanimi $p |- ( ( A. x ph /\ A. x ps ) -> A. x ch ) $= ? $.
$}

19.26 $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ A. x ps ) ) $= ? $.

$( Split a quantified biconditional $)
albi $p |- ( A. x ( ph <-> ps ) -> ( A. x ph <-> A. x ps ) ) $= ? $.

${
  albii.1 $e |- ( ph <-> ps ) $.
  albii $p |- ( A. x ph <-> A. x ps ) $= ? $.
$}

albiim $p |- ( A. x ( ph <-> ps ) <-> ( A. x ( ph -> ps ) /\ A. x ( ps -> ph ) ) ) $= ? $.
