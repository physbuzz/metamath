


$c |- wff -> ( ) -. $.
$v ph ps ch th tau $.

tph $f wff ph $.
tps $f wff ps $.
tch $f wff ch $.
tth $f wff th $.
tta $f wff tau $.

wn $a wff -. ph $.
wi $a wff ( ph -> ps ) $.

  ${
    min $e |- ph $.
    maj $e |- ( ph -> ps ) $.
    $( Rule of Modus Ponens.  The postulated inference rule of propositional
       calculus.  See, e.g., Rule 1 of [Hamilton] p. 73.  The rule says, "if
       ` ph ` is true, and ` ph ` implies ` ps ` , then ` ps ` must also be
       true".  This rule is sometimes called "detachment", since it detaches
       the minor premise from the major premise.  "Modus ponens" is short for
       "modus ponendo ponens", a Latin phrase that means "the mode that by
       affirming affirms" - remark in [Sanford] p. 39.  This rule is similar to
       the rule of modus tollens ~ mto .

       Note:  In some web page displays such as the Statement List, the
       symbols " ` & ` " and " ` => ` " informally indicate the relationship
       between the hypotheses and the assertion (conclusion), abbreviating the
       English words "and" and "implies".  They are not part of the formal
       language.  (Contributed by NM, 30-Sep-1992.) $)
    ax-mp $a |- ps $.
  $}

ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.
ax-3 $a |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $.
${ 
    mp.1 $e |- ph $.
    mp.2 $e |- ( ph -> ps ) $.
    mp $p |- ps $= ? $.
$}

meredith $p |- ( ( ( ( ph -> ps ) ->
    ( -. ch -> -. th ) ) -> ch ) -> tau ) -> 
    ( ( tau -> ph ) -> ( th -> ph ) ) $= ? $. 


