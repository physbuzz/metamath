

$c wff |- -> -. ( ) $.
$v ph ps ch th ta $.
wph $f wff ph $.
wps $f wff ps $.
wch $f wff ch $.
wth $f wff th $.
wta $f wff ta $.
wn $a wff -. ph $.
wi $a wff ( ph -> ps ) $.
${
  min $e |- ph $.
  maj $e |- ( ph -> ps ) $.
  ax-mp $a |- ps $.
$}
ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
ax-2 $a |- ( ( ph -> ( ps -> ch ) ) ->
             ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.
ax-3 $a |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $.

$( Add an antecedent $)
${
  a1i.1 $e |- ph $.
  a1i $p |- ( ps -> ph ) $=
    wph wps wph wi a1i.1 wph wps ax-1 ax-mp $.
$}

$( Distribute an antecedent $)
${
  a2i.1 $e |- ( ph -> ( ps -> ch ) ) $.
  a2i $p |- ( ( ph -> ps ) -> ( ph -> ch ) ) $=
    wph wps wch wi wi wph wps wi wph wch wi wi a2i.1 wph wps wch ax-2 ax-mp $.
$}

$( Modus ponens under shared antecedent $)
$( You'll use it constantly! $)
${
  mpd.1 $e |- ( ph -> ps ) $.
  mpd.2 $e |- ( ph -> ( ps -> ch ) ) $.
  mpd $p |- ( ph -> ch ) $=
    wph wps wi wph wch wi mpd.1 wph wps wch mpd.2 a2i ax-mp $.
$}

$( syllogism, or "hypothetical syllogism" $)
${
  syl.1 $e |- ( ph -> ps ) $.
  syl.2 $e |- ( ps -> ch ) $.
  syl $p |- ( ph -> ch ) $=
    wph wps wch syl.1 wps wch wi wph syl.2 a1i mpd $.
$}

id $p |- ( ph -> ph ) $=
  wph wph wph wi wph wph wph ax-1 wph wph wph wi ax-1 mpd $.

$( Remove repeated antecedent. AKA contraction.
   This is theorem 2.43 of Principia Mathematica. $)
${
  pm2.43i.1 $e |- ( ph -> ( ph -> ps ) ) $.
  pm2.43i $p |- ( ph -> ps ) $=
    wph wph wps wph id pm2.43i.1 mpd $.
$}

$( The deduction form of a1i. A deduction form puts the same 
   antecedent `ph ->` in front of every hypothesis and conclusion. $)
${
  a1d.1 $e |- ( ph -> ps ) $.
  a1d $p |- ( ph -> ( ch -> ps ) ) $=
    wph wps wch wps wi a1d.1 wps wch ax-1 syl $.
$}

$( The deduction form of a2i. $)
${
  a2d.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
  a2d $p |- ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) ) $=
    wph wps wch wth wi wi wps wch wi wps wth wi wi a2d.1 wps wch wth ax-2 syl
    $.
$}

$( Syllogism inference with commutation of antecedents. $)
${
  sylcom.1 $e |- ( ph -> ( ps -> ch ) ) $.
  sylcom.2 $e |- ( ps -> ( ch -> th ) ) $.
  sylcom $p |- ( ph -> ( ps -> th ) ) $=
    wph wps wch wi wps wth wi sylcom.1 wps wch wth sylcom.2 a2i syl $.
$}

$(  Inference that commutes antecedents in an implication. $)
${
  com12.1 $e |- ( ph -> ( ps -> ch ) ) $.
  com12 $p |- ( ps -> ( ph -> ch ) ) $=
    wps wph wps wch wps wph ax-1 com12.1 sylcom $.
$}

$( "Closed form" of modus ponens $)
pm2.27 $p |- ( ph -> ( ( ph -> ps ) -> ps ) ) $=
  wph wps wi wph wps wph wps wps wps wps wi wph wps id a1i a2i com12 $.

$( implication of implications $)
${
  imim2i.1 $e |- ( ph -> ps ) $.
  imim2i $p |- ( ( ch -> ph ) -> ( ch -> ps ) ) $=
    wch wph wps wph wps wi wch imim2i.1 a1i a2i $.
$}

$( Deduction form of mpd $)
${
  mpdd.1 $e |- ( ph -> ( ps -> ch ) ) $.
  mpdd.2 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
  mpdd $p |- ( ph -> ( ps -> th ) ) $=
    wph wps wch wi wps wth wi mpdd.1 wph wps wch wth mpdd.2 a2d mpd $.
$}

$( Deduction form of syl $)
${
  syld.1 $e |- ( ph -> ( ps -> ch ) ) $.
  syld.2 $e |- ( ph -> ( ch -> th ) ) $.
  syld $p |- ( ph -> ( ps -> th ) ) $=
    wps wph wth wps wph wch wth wph wps wch syld.1 com12 syld.2 sylcom com12 $.
$}


$( Note: This can be viewed as a syllogism but with the hypothesis syl.2
   "discharged" and turned into an antecedent. $)
${
  imim1i.1 $e |- ( ph -> ps ) $.
  imim1i $p |- ( ( ps -> ch ) -> ( ph -> ch ) ) $=
    wps wch wi wph wps wch wph wps wi wps wch wi imim1i.1 a1i wps wch wi id
    syld $.
$}

$( The following closed forms of theorems we've already proved do the same
   trick. We discharge a hypothesis. 
   (Contributed by ?who?, 8-Nov-2026.) $)
imim2 $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $=
  wph wps wi wch wph wps wi wi wch wph wi wch wps wi wi wph wps wi wch ax-1 wch
  wph wps ax-2 syl $.

imim1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
  wps wch wi wph wps wi wph wch wi wps wch wph imim2 com12 $.

pm2.43 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $=
  wph wph wps wi wps wph wps pm2.27 a2i $.

pm2.04 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
  wph wps wch wi wi wph wps wi wph wch wi wi wps wph wch wi wi wph wps wch ax-2
  wps wph wps wi wph wch wi wps wph ax-1 imim1i syl $.

$( Inference form of axiom 3. "Con" is short for "contraposition" $)
${
  con4i.1 $e |- ( -. ph -> -. ps ) $.
  con4i $p |- ( ps -> ph ) $=
    wph wn wps wn wi wps wph wi con4i.1 wph wps ax-3 ax-mp $.
$}

$( Deduction form of axiom 3. $)
${
  con4d.1 $e |- ( ph -> ( -. ps -> -. ch ) ) $.
  con4d $p |- ( ph -> ( ch -> ps ) ) $=
    wph wps wn wch wn wi wch wps wi con4d.1 wps wch ax-3 syl $.
$}

$( Principle of explosion: A contradiction implies anything. $)
${
  pm2.21i.1 $e |- -. ph $.
  pm2.21i $p |- ( ph -> ps ) $=
    wps wph wph wn wps wn pm2.21i.1 a1i con4i $.
$}
$( Also principle of explosion. $)
${
  pm2.24ii.1 $e |- ph $.
  pm2.24ii.2 $e |- -. ph $.
  pm2.24ii $p |- ps $=
    wph wps pm2.24ii.1 wph wps pm2.24ii.2 pm2.21i ax-mp $.
$}
$( deduction form of explosion $)
${
  pm2.21d.1 $e |- ( ph -> -. ps ) $.
  pm2.21d $p |- ( ph -> ( ps -> ch ) ) $=
    wph wch wps wph wps wn wch wn pm2.21d.1 a1d con4d $.
$}

$( closed forms of explosion 
   (Contributed by ?who?, 8-Nov-2026.) $)
pm2.21 $p |- ( -. ph -> ( ph -> ps ) ) $=
  wph wn wph wps wph wn id pm2.21d $.
pm2.24 $p |- ( ph -> ( -. ph -> ps ) ) $=
  wph wn wph wps wph wps pm2.21 com12 $.

$( Clavius law: if a formula follows from its own negation, then it's true. 
   (Contributed by ?who?, 14-Nov-2026.) $)
pm2.18 $p |- ( ( -. ph -> ph ) -> ph ) $=
  wph wn wph wi wph wph wn wph wi wph wph wn wph wi wph wn wph wph wn wph wi wn
  wph wph wn wph wi wn pm2.21 a2i con4d pm2.43i $.

$( Double negation elimination 
   (Contributed by ?who?, 14-Nov-2026.) $)
notnotr $p |- ( -. -. ph -> ph ) $=
  wph wn wn wph wn wph wi wph wph wn wph pm2.21 wph pm2.18 syl $.

$( Double negation introduction 
   (Contributed by ?who?, 14-Nov-2026.) $)
notnot $p |- ( ph -> -. -. ph ) $=
  wph wn wn wph wph wn notnotr con4i $.
$( who's there? $)

$( Contraposition 2 $)
${
  con2i.a $e |- ( ph -> -. ps ) $.
  con2i $p |- ( ps -> -. ph ) $=
    wph wn wps wph wn wn wph wps wn wph notnotr con2i.a syl con4i $.
$}

$( Contraposition 1 $)
${
  con1i.1 $e |- ( -. ph -> ps ) $.
  con1i $p |- ( -. ps -> ph ) $=
    wph wps wn wph wn wps wps wn wn con1i.1 wps notnot syl con4i $.
$}

$( Contraposition 3 $)
${
  con3i.a $e |- ( ph -> ps ) $.
  con3i $p |- ( -. ps -> -. ph ) $=
    wph wn wps wn wph wn wn wph wps wn wn wph notnotr wph wps wps wn wn con3i.a
    wps notnot syl syl con4i $.
$}

$( Modus tollens $)
${
  mto.1 $e |- -. ps $.
  mto.2 $e |- ( ph -> ps ) $.
  mto $p |- -. ph $=
    wps wn wph wn mto.1 wph wps mto.2 con3i ax-mp $.
$}

$( Proof by cases $)
${
  pm2.61i.1 $e |- ( ph -> ps ) $.
  pm2.61i.2 $e |- ( -. ph -> ps ) $.
  pm2.61i $p |- ps $=
    wps wn wps wi wps wps wn wph wn wps wph wps pm2.61i.1 con3i pm2.61i.2 syl
    wps pm2.18 ax-mp $.
$}

$( Reductio ad absurdum $)
${
  pm2.65i.1 $e |- ( ph -> ps ) $.
  pm2.65i.2 $e |- ( ph -> -. ps ) $.
  pm2.65i $p |- -. ph $=
    wps wn wph wn wph wps pm2.65i.1 con3i wph wps wn pm2.65i.2 con3i pm2.61i $.
$}

$( Pierce's law. Note that it seems to not use negation... but
   it's in the section with ax-3? How curious. 
   (Contributed by ?who?, 14-Nov-2026.) $)
peirce $p |- ( ( ( ph -> ps ) -> ph ) -> ph ) $=
  wph wph wps wi wph wi wph wi wph wph wps wi wph wi ax-1 wph wn wph wps wi wph
  wps wi wph wi wph wi wph wps pm2.21 wph wps wi wph pm2.27 syl pm2.61i $.
