$[ prop.mm $]

$c setvar A. $.
$v x $.
vx $f setvar x $.
wal $a wff A. x ph $.

${ 
  ax-gen.1 $e |- ph $.  
  ax-gen $a |- A. x ph $. 
$}
ax-4 $a |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $.

$( Lift an implication $)
${
  mpg.1 $e |- ( A. x ph -> ps ) $.
  mpg.2 $e |- ph $.
  mpg $p |- ps $=
    wph vx wal wps wph vx mpg.2 ax-gen mpg.1 ax-mp $.
$}

${
  alimi.1 $e |- ( ph -> ps ) $.
  alimi $p |- ( A. x ph -> A. x ps ) $=
    wph wps wi vx wal wph vx wal wps vx wal wi wph wps wi vx alimi.1 ax-gen wph
    wps vx ax-4 ax-mp $.
$}

al2im $p |- ( A. x ( ph -> ( ps -> ch ) ) -> ( A. x ph -> ( A. x ps -> A. x ch ) ) ) $=
  wph wps wch wi wi vx wal wph vx wal wps wch wi vx wal wps vx wal wch vx wal
  wi wph wps wch wi vx ax-4 wph vx wal wps wch wi vx wal wps vx wal wch vx wal
  wi wi wi wph wps wch wi wi vx wal wps wch wi vx wal wps vx wal wch vx wal wi
  wi wph vx wal wps wch vx ax-4 a1i a1i mpdd $.

${
  al2imi.1 $e |- ( ph -> ( ps -> ch ) ) $.
  al2imi $p |- ( A. x ph -> ( A. x ps -> A. x ch ) ) $=
    wph vx wal wps wch wi vx wal wps vx wal wch vx wal wi wph wps wch wi wi vx
    wal wph vx wal wps wch wi vx wal wi wph wps wch wi wi vx al2imi.1 ax-gen
    wph wps wch wi vx ax-4 ax-mp wps wch wi vx wal wps vx wal wch vx wal wi wi
    wph vx wal wps wch vx ax-4 a1i mpd $.
$}

$( Collect the conjuncts $)
${
  alanimi.1 $e |- ( ( ph /\ ps ) -> ch ) $.
  alanimi $p |- ( ( A. x ph /\ A. x ps ) -> A. x ch ) $=
    wph vx wal wps vx wal wch vx wal wph wps wch vx wph wps wch alanimi.1 ex
    al2imi imp $.
$}

19.26 $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ A. x ps ) ) $=
  wph wps wa vx wal wph vx wal wps vx wal wa wph wps wa vx wal wph vx wal wps
  vx wal wph wps wa wph wi vx wal wph wps wa vx wal wph vx wal wi wph wps wa
  wph wi vx wph wps simpl ax-gen wph wps wa wph vx ax-4 ax-mp wph wps wa wps wi
  vx wal wph wps wa vx wal wps vx wal wi wph wps wa wps wi vx wph wps simpr
  ax-gen wph wps wa wps vx ax-4 ax-mp jca wph wps wph wps wa vx wph wps wa id
  alanimi impbii $.

$( Split a quantified biconditional 
   (Contributed by ?who?, 19-Nov-2026.) $)
albi $p |- ( A. x ( ph <-> ps ) -> ( A. x ph <-> A. x ps ) ) $=
  wph wps wb vx wal wph vx wal wps vx wal wph wps wb wph wps vx wph wps biimp
  al2imi wph wps wb wps wph vx wph wps biimpr al2imi impbid $.

${
  albii.1 $e |- ( ph <-> ps ) $.
  albii $p |- ( A. x ph <-> A. x ps ) $=
    wph wps wb vx wal wph vx wal wps vx wal wb wph wps wb vx albii.1 ax-gen wph
    wps vx albi ax-mp $.
$}

albiim $p |- ( A. x ( ph <-> ps ) <-> ( A. x ( ph -> ps ) /\ A. x ( ps -> ph ) ) ) $=
  wph wps wb vx wal wph wps wi vx wal wps wph wi vx wal wa wph wps wb vx wal
  wph wps wi vx wal wps wph wi vx wal wph wps wb wph wps wi vx wph wps biimp
  alimi wph wps wb wps wph wi vx wph wps biimpr alimi jca wph wps wi wps wph wi
  wph wps wb vx wph wps wb wph wps wi wps wph wi wa wi wph wps wi wps wph wi wa
  wph wps wb wi wa wph wps wi wps wph wi wa wph wps wb wi wph wps dfbi wph wps
  wb wph wps wi wps wph wi wa wi wph wps wi wps wph wi wa wph wps wb wi simpr
  ax-mp alanimi impbii $.

$( Two syllogisms $)
${
  barbara.maj $e |- A. x ( ph -> ps ) $.
  barbara.min $e |- A. x ( ch -> ph ) $.
  barbara $p |- A. x ( ch -> ps ) $=
    wph wps wi vx wal wch wph wi vx wal wa wch wps wi vx wal wph wps wi vx wal
    wch wph wi vx wal barbara.maj barbara.min pm3.2i wph wps wi wch wph wi wch
    wps wi vx wch wph wps pm3.34 alanimi ax-mp $.
$}

${
  celarent.maj $e |- A. x ( ph -> -. ps ) $.
  celarent.min $e |- A. x ( ch -> ph ) $.
  celarent $p |- A. x ( ch -> -. ps ) $=
    wph wps wn wi vx wal wch wph wi vx wal wa wch wps wn wi vx wal wph wps wn
    wi vx wal wch wph wi vx wal celarent.maj celarent.min pm3.2i wph wps wn wi
    wch wph wi wch wps wn wi vx wch wph wps wn pm3.34 alanimi ax-mp $.
$}
