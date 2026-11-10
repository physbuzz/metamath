$( Chapter 4 practice: hol. Supporting proofs are supplied.
   Fill in: syl2anc, mpd.
   Source: https://github.com/metamath/set.mm/blob/develop/hol.mm
   The source databases are public domain. $)

$c var $.   
  $c type $.  
  $c term $.  
  $c |- $.    
  $c : $.     
  $c . $.     
  $c |= $.    
  $c bool $.

  $c -> $.    
  $c ( $.     
  $c ) $.     
  $c , $.     
  $c \ $.     
  $c = $.     
  $c T. $.    
  $c [ $.     
  $c ] $.     

  $v al $.  
  $v be $.  
  $v ga $.  
  $v de $.  

  $v x y z f g p q $.  
  $v A B C F R S T $.

  hal $f type al $.

  hbe $f type be $.

  hga $f type ga $.

  hde $f type de $.

  vx $f var x $.

  vy $f var y $.

  vz $f var z $.

  vf $f var f $.

  vg $f var g $.

  vp $f var p $.

  vq $f var q $.

  ta $f term A $.

  tb $f term B $.

  tc $f term C $.

  tf $f term F $.

  tr $f term R $.

  ts $f term S $.

  tt $f term T $.

  tv $a term x : al $.

  ht $a type ( al -> be ) $.

  hb $a type bool $.

  kc $a term ( F T ) $.

  kl $a term \ x : al . T $.

  ke $a term = $.

  kt $a term T. $.

  kbr $a term [ A F B ] $.

  kct $a term ( A , B ) $.

  ${
    ax-syl.1 $e |- R |= S $.
    ax-syl.2 $e |- S |= T $.

    ax-syl $a |- R |= T $.

    syl $p |- R |= T $=
      ( ax-syl ) ABCDEF $.
  $}

  ${
    ax-jca.1 $e |- R |= S $.
    ax-jca.2 $e |- R |= T $.

    ax-jca $a |- R |= ( S , T ) $.

    jca $p |- R |= ( S , T ) $=
      ( ax-jca ) ABCDEF $.
  $}

  ${
    syl2anc.1 $e |- R |= S $.
    syl2anc.2 $e |- R |= T $.
    syl2anc.3 $e |- ( S , T ) |= A $.

    syl2anc $p |- R |= A $= ? $.
  $}

  ${
    ax-simpl.1 $e |- R : bool $.
    ax-simpl.2 $e |- S : bool $.

    ax-simpl $a |- ( R , S ) |= R $.

    ax-simpr $a |- ( R , S ) |= S $.

    simpl $p |- ( R , S ) |= R $=
      ( ax-simpl ) ABCDE $.

    simpr $p |- ( R , S ) |= S $=
      ( ax-simpr ) ABCDE $.
  $}

  ${
    ax-id.1 $e |- R : bool $.

    ax-id $a |- R |= R $.

    id $p |- R |= R $=
      ( ax-id ) ABC $.
  $}

  ${
    ax-trud.1 $e |- R : bool $.

    ax-trud $a |- R |= T. $.

    trud $p |- R |= T. $=
      ( ax-trud ) ABC $.

    ax-a1i.2 $e |- T. |= A $.

    a1i $p |- R |= A $=
      ( kt ax-trud syl ) BEABCFDG $.
  $}

  ${
    ax-cb.1 $e |- R |= A $.

    ax-cb1 $a |- R : bool $.

    ax-cb2 $a |- A : bool $.
  $}

  ${
    wctl.1 $e |- ( S , T ) : bool $.

    ax-wctl $a |- S : bool $.

    ax-wctr $a |- T : bool $.

    wctl $p |- S : bool $=
      ( ax-wctl ) ABCD $.

    wctr $p |- T : bool $=
      ( ax-wctr ) ABCD $.
  $}

  ${
    mpdan.1 $e |- R |= S $.
    mpdan.2 $e |- ( R , S ) |= T $.

    mpdan $p |- R |= T $=
      ( ax-cb1 id syl2anc ) CAABABADFGDEH $.
  $}

  ${
    simpld.1 $e |- R |= ( S , T ) $.

    simprd $p |- R |= T $=
      ( kct ax-cb2 wctl wctr simpr syl ) ABCEZCDBCBCKADFZGBCLHIJ $.
  $}

  ax-weq $a |- = : ( al -> ( al -> bool ) ) $.

  weq $p |- = : ( al -> ( al -> bool ) ) $=
    ( ax-weq ) AB $.

  ${
    ax-refl.1 $e |- A : al $.

    ax-refl $a |- T. |= ( ( = A ) A ) $.
  $}

  wtru $p |- T. : bool $=
    ( ke kc kt hb ht weq ax-refl ax-cb1 ) AABABCDDDEEADFGH $.

  tru $p |- T. |= T. $=
    ( kt wtru id ) ABC $.

  ${
    ax-eqmp.1 $e |- R |= A $.
    ax-eqmp.2 $e |- R |= ( ( = A ) B ) $.

    ax-eqmp $a |- R |= B $.
  $}

  ${
    ax-ded.1 $e |- ( R , S ) |= T $.
    ax-ded.2 $e |- ( R , T ) |= S $.

    ax-ded $a |- R |= ( ( = S ) T ) $.
  $}

  ${
    wct.1 $e |- S : bool $.
    wct.2 $e |- T : bool $.

    ax-wct $a |- ( S , T ) : bool $.

    wct $p |- ( S , T ) : bool $=
      ( ax-wct ) ABCDE $.
  $}

  ${
    wc.1 $e |- F : ( al -> be ) $.
    wc.2 $e |- T : al $.

    ax-wc $a |- ( F T ) : be $.

    wc $p |- ( F T ) : be $=
      ( ax-wc ) ABCDEFG $.
  $}

  ${
    ax-ceq.1 $e |- F : ( al -> be ) $.
    ax-ceq.2 $e |- T : ( al -> be ) $.
    ax-ceq.3 $e |- A : al $.
    ax-ceq.4 $e |- B : al $.

    ax-ceq $a |- ( ( ( = F ) T ) , ( ( = A ) B ) ) |=
      ( ( = ( F A ) ) ( T B ) ) $.
  $}

  ${
    eqcomx.1 $e |- A : al $.
    eqcomx.2 $e |- B : al $.
    eqcomx.3 $e |- R |= ( ( = A ) B ) $.

    eqcomx $p |- R |= ( ( = B ) A ) $=
      ( ke kc ax-cb1 ax-refl a1i hb ht weq ax-ceq syl2anc wc ax-eqmp ) HBIZBIZH
      CIZBIZDUADTCIZDGJZABEKLZHUAIUCIDHTIUBIZUAUGDHHIHIZUDUHDUEAAMNZNHAOZKLGAUI
      BCHHUJUJEFPQUFAMBBTUBAUIHBUJERAUIHCUJFREEPQS $.
  $}

  ${
    mpbirx.1 $e |- B : bool $.
    mpbirx.2 $e |- R |= A $.
    mpbirx.3 $e |- R |= ( ( = B ) A ) $.

    mpbirx $p |- R |= B $=
      ( hb ax-cb2 eqcomx ax-eqmp ) ABCEGBACDACEHFIJ $.
  $}

  ${
    ancoms.1 $e |- ( R , S ) |= T $.

    ancoms $p |- ( S , R ) |= T $=
      ( kct ax-cb1 wctr wctl simpr simpl syl2anc ) CBAEABBAABCABEDFZGZABLHZIBAM
      NJDK $.
  $}

  ${
    adantr.1 $e |- R |= T $.
    adantr.2 $e |- S : bool $.

    adantr $p |- ( R , S ) |= T $=
      ( kct ax-cb1 simpl syl ) ABFACABCADGEHDI $.

    adantl $p |- ( S , R ) |= T $=
      ( adantr ancoms ) ABCABCDEFG $.
  $}

  ax-wv $a |- x : al : al $.

  wv $p |- x : al : al $=
    ( ax-wv ) ABC $.

  ${
    wl.1 $e |- T : be $.

    ax-wl $a |- \ x : al . T : ( al -> be ) $.

    wl $p |- \ x : al . T : ( al -> be ) $=
      ( ax-wl ) ABCDEF $.
  $}

  ${
    ax-beta.1 $e |- A : be $.

    ax-beta $a |- T. |= ( ( = ( \ x : al . A x : al ) ) A ) $.

    ax-distrc.2 $e |- B : al $.
    ax-distrc.3 $e |- F : ( be -> ga ) $.

    ax-distrc $a |- T. |= ( ( = ( \ x : al . ( F A ) B ) )
      ( ( \ x : al . F B ) ( \ x : al . A B ) ) ) $.
  $}

  ${
    $d x R $.
    ax-leq.1 $e |- A : be $.
    ax-leq.2 $e |- B : be $.
    ax-leq.3 $e |- R |= ( ( = A ) B ) $.

    ax-leq $a |- R |= ( ( = \ x : al . A ) \ x : al . B ) $.
  $}

  ${
    $d x y $.  $d y B $.
    ax-distrl.1 $e |- A : ga $.
    ax-distrl.2 $e |- B : al $.

    ax-distrl $a |- T. |=
      ( ( = ( \ x : al . \ y : be . A B ) ) \ y : be . ( \ x : al . A B ) ) $.
  $}

  ${
    wov.1 $e |- F : ( al -> ( be -> ga ) ) $.
    wov.2 $e |- A : al $.
    wov.3 $e |- B : be $.

    ax-wov $a |- [ A F B ] : ga $.

    wov $p |- [ A F B ] : ga $=
      ( ax-wov ) ABCDEFGHIJ $.

    df-ov $a |- T. |= ( ( = [ A F B ] ) ( ( F A ) B ) ) $.
  $}

  ${
    dfov1.1 $e |- F : ( al -> ( be -> bool ) ) $.
    dfov1.2 $e |- A : al $.
    dfov1.3 $e |- B : be $.
    ${
      dfov1.4 $e |- R |= [ A F B ] $.

      dfov1 $p |- R |= ( ( F A ) B ) $=
        ( kbr kc ke ax-cb1 hb df-ov a1i ax-eqmp ) CDEKZECLDLZFJMSLTLFSFJNABOCDE
        GHIPQR $.
    $}

    dfov2.4 $e |- R |= ( ( F A ) B ) $.

    dfov2 $p |- R |= [ A F B ] $=
      ( kc kbr hb wov ke ax-cb1 df-ov a1i mpbirx ) ECKDKZCDELZFABMCDEGHINJOUAKT
      KFTFJPABMCDEGHIQRS $.
  $}

  ${
    weqi.1 $e |- A : al $.
    weqi.2 $e |- B : al $.

    weqi $p |- [ A = B ] : bool $=
      ( hb ke weq wov ) AAFBCGAHDEI $.
  $}

  ${
    eqcomi.1 $e |- A : al $.
    eqcomi.2 $e |- R |= [ A = B ] $.

    ax-eqtypi $a |- B : al $.

    eqtypi $p |- B : al $=
      ( ax-eqtypi ) ABCDEFG $.

    eqcomi $p |- R |= [ B = A ] $=
      ( ke weq eqtypi dfov1 eqcomx dfov2 ) AACBGDAHZABCDEFIZEABCDENAABCGDMENFJK
      L $.
  $}

  ${
    eqtypri.1 $e |- A : al $.
    eqtypri.2 $e |- R |= [ B = A ] $.

    ax-eqtypri $a |- B : al $.

    eqtypri $p |- B : al $=
      ( ax-eqtypri ) ABCDEFG $.
  $}

  ${
    mpbi.1 $e |- R |= A $.
    mpbi.2 $e |- R |= [ A = B ] $.

    mpbi $p |- R |= B $=
      ( hb ke weq ax-cb2 eqtypi dfov1 ax-eqmp ) ABCDFFABGCFHACDIZFABCMEJEKL $.
  $}

  ${
    eqid.1 $e |- R : bool $.
    eqid.2 $e |- A : al $.

    eqid $p |- R |= [ A = A ] $=
      ( ke weq kc ax-refl a1i dfov2 ) AABBFCAGEEFBHBHCDABEIJK $.
  $}

  ${
    ded.1 $e |- ( R , S ) |= T $.
    ded.2 $e |- ( R , T ) |= S $.

    ded $p |- R |= [ S = T ] $=
      ( hb ke weq kct ax-cb2 ax-ded dfov2 ) FFBCGAFHBACIEJCABIDJABCDEKL $.
  $}

  ${
    dedi.1 $e |- S |= T $.
    dedi.2 $e |- T |= S $.

    dedi $p |- T. |= [ S = T ] $=
      ( kt wtru adantl ded ) EABAEBCFGBEADFGH $.
  $}

  ${
    eqtru.1 $e |- R |= A $.

    eqtru $p |- R |= [ T. = A ] $=
      ( kt wtru adantr kct ax-cb1 ax-cb2 wct tru a1i ded ) BDABDACEFDBAGBAABCHA
      BCIJKLM $.
  $}

  ${
    mpbir.1 $e |- R |= A $.
    mpbir.2 $e |- R |= [ B = A ] $.

    mpbir $p |- R |= B $=
      ( hb ax-cb2 eqtypri eqcomi mpbi ) ABCDFBACFABCACDGEHEIJ $.
  $}

  ${
    ceq12.1 $e |- F : ( al -> be ) $.
    ceq12.2 $e |- A : al $.
    ${
      ceq12.3 $e |- R |= [ F = T ] $.
      ${
        ceq12.4 $e |- R |= [ A = B ] $.

        ceq12 $p |- R |= [ ( F A ) = ( T B ) ] $=
          ( kc ke weq wc ht eqtypi dfov1 ax-ceq syl2anc dfov2 ) BBECLZGDLZMFBNA
          BECHIOABGDABPZEGFHJQZACDFIKQZOMUBLUCLFMELGLMCLDLUDUDEGMFUDNHUEJRAACDM
          FANIUFKRABCDEGHUEIUFSTUA $.
      $}

      ceq1 $p |- R |= [ ( F A ) = ( T A ) ] $=
        ( ke kbr ax-cb1 eqid ceq12 ) ABCCDEFGHIACEDFJKEILHMN $.
    $}

    ceq2.3 $e |- R |= [ A = B ] $.

    ceq2 $p |- R |= [ ( F A ) = ( F B ) ] $=
      ( ht ke kbr ax-cb1 eqid ceq12 ) ABCDEFEGHABJEFCDKLFIMGNIO $.
  $}

  ${
    $d x R $.
    leq.1 $e |- A : be $.
    leq.2 $e |- R |= [ A = B ] $.

    leq $p |- R |= [ \ x : al . A = \ x : al . B ] $=
      ( ht kl ke weq wl eqtypi dfov1 ax-leq dfov2 ) ABIZRACDJACEJKFRLABCDGMABCE
      BDEFGHNZMABCDEFGSBBDEKFBLGSHOPQ $.
  $}

  ${
    beta.1 $e |- A : be $.

    beta $p |- T. |= [ ( \ x : al . A x : al ) = A ] $=
      ( kl tv kc ke kt weq wl wv wc ax-beta dfov2 ) BBACDFZACGZHDIJBKABQRABCDEL
      ACMNEABCDEOP $.
  $}

  ${
    distrc.1 $e |- F : ( be -> ga ) $.
    distrc.2 $e |- A : be $.
    distrc.3 $e |- B : al $.

    distrc $p |- T. |= [ ( \ x : al . ( F A ) B ) =
      ( ( \ x : al . F B ) ( \ x : al . A B ) ) ] $=
      ( kc kl ke kt weq wc wl ht ax-distrc dfov2 ) CCADGEKZLZFKADGLZFKZADELZFKZ
      KMNCOACUBFACDUABCGEHIPQJPBCUDUFABCRZUCFAUGDGHQJPABUEFABDEIQJPPABCDEFGIJHS
      T $.
  $}

  ${
    $d x y $.  $d y B $.
    distrl.1 $e |- A : ga $.
    distrl.2 $e |- B : al $.

    distrl $p |- T. |=
      [ ( \ x : al . \ y : be . A B ) = \ y : be . ( \ x : al . A B ) ] $=
      ( ht kl kc ke kt weq wl wc ax-distrl dfov2 ) BCJZTADBEFKZKZGLBEADFKZGLZKM
      NTOATUBGATDUABCEFHPPIQBCEUDACUCGACDFHPIQPABCDEFGHIRS $.
  $}

  ${
    eqtri.1 $e |- A : al $.
    eqtri.2 $e |- R |= [ A = B ] $.
    eqtri.3 $e |- R |= [ B = C ] $.

    eqtri $p |- R |= [ A = C ] $=
      ( ke weq eqtypi kc dfov1 hb ht wc ceq2 mpbi dfov2 ) AABDIEAJZFACDEABCEFGK
      ZHKIBLZCLUBDLEAABCIETFUAGMANCDUBEAANOIBTFPUAHQRS $.
  $}

  ${
    3eqtr4i.1 $e |- A : al $.
    3eqtr4i.2 $e |- R |= [ A = B ] $.
    ${
      3eqtr4i.3 $e |- R |= [ S = A ] $.
      3eqtr4i.4 $e |- R |= [ T = B ] $.

      3eqtr4i $p |- R |= [ S = T ] $=
        ( eqtypri eqtypi eqcomi eqtri ) AEBFDABEDGIKIABCFDGHAFCDACFDABCDGHLJKJM
        NN $.
    $}

    3eqtr3i.3 $e |- R |= [ A = S ] $.
    3eqtr3i.4 $e |- R |= [ B = T ] $.

    3eqtr3i $p |- R |= [ S = T ] $=
      ( eqcomi eqtypi 3eqtr4i ) ABCDEFGHABEDGIKACFDABCDGHLJKM $.
  $}

  ${
    oveq.1 $e |- F : ( al -> ( be -> ga ) ) $.
    oveq.2 $e |- A : al $.
    oveq.3 $e |- B : be $.
    ${
      oveq123.4 $e |- R |= [ F = S ] $.
      oveq123.5 $e |- R |= [ A = C ] $.
      oveq123.6 $e |- R |= [ B = T ] $.

      oveq123 $p |- R |= [ [ A F B ] = [ C S T ] ] $=
        ( kc kbr wc ke ht ceq12 weq wov ax-cb1 df-ov a1i dfov2 eqtypi 3eqtr4i )
        CGDQZEQZIFQZJQZHDEGRZFJIRZBCUKEABCUAZGDKLSZMSZBCEJUKHUMURMAUQDFGHIKLNOU
        BPUBCCUOULTHCUCZABCDEGKLMUDUSTUOQULQHGITRHNUEZABCDEGKLMUFUGUHCCUPUNTHUT
        ABCFJIAUQUAGIHKNUIZADFHLOUIZBEJHMPUIZUDBCUMJAUQIFVBVCSVDSTUPQUNQHVAABCF
        JIVBVCVDUFUGUHUJ $.
    $}

    ${
      oveq1.4 $e |- R |= [ A = C ] $.

      oveq1 $p |- R |= [ [ A F B ] = [ C F B ] ] $=
        ( ht ke kbr ax-cb1 eqid oveq123 ) ABCDEFGHGEIJKABCMMGHDFNOHLPZIQLBEHSKQ
        R $.

      oveq12.5 $e |- R |= [ B = T ] $.

      oveq12 $p |- R |= [ [ A F B ] = [ C F T ] ] $=
        ( ht ke kbr ax-cb1 eqid oveq123 ) ABCDEFGHGIJKLABCOOGHDFPQHMRJSMNT $.
    $}

    ${
      oveq2.4 $e |- R |= [ B = T ] $.

      oveq2 $p |- R |= [ [ A F B ] = [ A F T ] ] $=
        ( ke kbr ax-cb1 eqid oveq12 ) ABCDEDFGHIJKADGEHMNGLOJPLQ $.
    $}

    ${
      oveq.4 $e |- R |= [ F = S ] $.

      oveq $p |- R |= [ [ A F B ] = [ A S B ] ] $=
        ( ke kbr ax-cb1 eqid oveq123 ) ABCDEDFGHEIJKLADGFHMNGLOZJPBEGRKPQ $.
    $}
  $}

  ${
    ax-hbl1.1 $e |- A : ga $.
    ax-hbl1.2 $e |- B : al $.

    ax-hbl1 $a |- T. |= [ ( \ x : al . \ x : be . A B ) = \ x : be . A ] $.

    hbl1.3 $e |- R : bool $.

    hbl1 $p |- R |= [ ( \ x : al . \ x : be . A B ) = \ x : be . A ] $=
      ( kl kc ke kbr ax-hbl1 a1i ) ADBDEKZKFLQMNGJABCDEFHIOP $.
  $}

  ${
    $d x A $.
    ax-17.1 $e |- A : be $.
    ax-17.2 $e |- B : al $.

    ax-17 $a |- T. |= [ ( \ x : al . A B ) = A ] $.

    a17i.3 $e |- R : bool $.

    a17i $p |- R |= [ ( \ x : al . A B ) = A ] $=
      ( kl kc ke kbr ax-17 a1i ) ACDJEKDLMFIABCDEGHNO $.
  $}

  ${
    $d x R $.
    hbxfr.1 $e |- T : be $.
    hbxfr.2 $e |- B : al $.
    ${
      hbxfrf.3 $e |- R |= [ T = A ] $.
      hbxfrf.4 $e |- ( S , R ) |= [ ( \ x : al . A B ) = A ] $.

      hbxfrf $p |- ( S , R ) |= [ ( \ x : al . T B ) = T ] $=
        ( kl kc kct eqtypi wl ke kbr adantl wc leq ceq1 ax-cb1 wctl 3eqtr4i ) B
        ACDMZENZDGFOZACHMZENZHABUGEABCDBHDFIKPQJUALFGUKUHRSABEUJFUGABCHIQJABCHD
        FIKUBUCGFUHDRSUILUDUEZTFGHDRSKULTUF $.
    $}

  $}

  ${
    hbc.1 $e |- F : ( be -> ga ) $.
    hbc.2 $e |- A : be $.
    hbc.3 $e |- B : al $.
    hbc.4 $e |- R |= [ ( \ x : al . F B ) = F ] $.
    hbc.5 $e |- R |= [ ( \ x : al . A B ) = A ] $.

    hbc $p |- R |= [ ( \ x : al . ( F A ) B ) = ( F A ) ] $=
      ( kc kl wc wl ke kbr ax-cb1 distrc a1i ht eqtypri ceq12 eqtri ) CADGENZOZ
      FNZADGOZFNZADEOFNZNZUGHACUHFACDUGBCGEIJPQKPUIUMRSHUKGRSHLTABCDEFGIJKUAUBB
      CULEUKHGABCUCZUJFAUNDGIQKPBEULHJMUDLMUEUF $.
  $}

  ${
    hbov.1 $e |- F : ( be -> ( ga -> de ) ) $.
    hbov.2 $e |- A : be $.
    hbov.3 $e |- B : al $.
    hbov.4 $e |- C : ga $.
    hbov.5 $e |- R |= [ ( \ x : al . F B ) = F ] $.
    hbov.6 $e |- R |= [ ( \ x : al . A B ) = A ] $.
    hbov.7 $e |- R |= [ ( \ x : al . C B ) = C ] $.

    hbov $p |- R |= [ ( \ x : al . [ A F C ] B ) = [ A F C ] ] $=
      ( kt kbr kc kl ke ax-cb1 trud wov weq ht wc df-ov dfov2 hbc adantr hbxfrf
      wtru mpdan ) JRAEFHISZUAGTUPUBSJAEIUAGTIUBSJOUCUDADEIFTZHTZGRJUPBCDFHIKLN
      UEZMDDUPURUBRDUFUSCDUQHBCDUGZIFKLUHZNUHBCDFHIKLNUIUJJRAEURUAGTURUBSACDEHG
      UQJVANMABUTEFGIJKLMOPUKQUKUNULUMUO $.
  $}

  ${
    $d x y $.  $d y B $.  $d y S $.
    ax-inst.1 $e |- R |= A $.
    ax-inst.2 $e |- T. |= [ ( \ x : al . B y : al ) = B ] $.
    ax-inst.3 $e |- T. |= [ ( \ x : al . S y : al ) = S ] $.
    ax-inst.4 $e |- [ x : al = C ] |= [ A = B ] $.
    ax-inst.5 $e |- [ x : al = C ] |= [ R = S ] $.

    ax-inst $a |- S |= B $.
  $}

  ${
    $d x y R $.  $d y B $.
    insti.1 $e |- C : al $.
    insti.2 $e |- B : bool $.
    insti.3 $e |- R |= A $.
    insti.4 $e |- T. |= [ ( \ x : al . B y : al ) = B ] $.
    insti.5 $e |- [ x : al = C ] |= [ A = B ] $.

    insti $p |- R |= B $=
      ( hb tv ax-cb1 wv ax-17 ke kbr eqid ax-inst ) ABCDEFGGJKAMBGACNDGJOZACPQL
      MGABNFRSZDERSUCLOUBTUA $.
  $}

  ${
    $d y A $.  $d y B $.  $d y C $.  $d x y al $.
    clf.1 $e |- A : be $.
    clf.2 $e |- C : al $.
    clf.3 $e |- [ x : al = C ] |= [ A = B ] $.
    clf.4 $e |- T. |= [ ( \ x : al . B y : al ) = B ] $.
    clf.5 $e |- T. |= [ ( \ x : al . C y : al ) = C ] $.

    clf $p |- T. |= [ ( \ x : al . A C ) = B ] $=
      ( kl tv kc ke kbr kt wc hb wl eqtypi weqi ax-cb1 beta a1i wv ht a17i hbl1
      weq hbc hbov id ceq2 oveq12 insti ) ACDACEMZACNZOZEPQZURGOZFPQGRIBVBFABUR
      GABCEHUAZISZBEFUSGPQZHJUBZUCVARACFMADNZOFPQRKUDZABCEHUEUFABBTCVBVGFPRBUKZ
      VDADUGZVFABBTUHUHCPVGRVIVJVHUIAABCGVGURRVCIVJAABCEVGRHVJVHUJLULKUMBBTUTEV
      BPVEFVIABURUSVCACUGZSHABUSGURVEVCVKVEAUSGVKIUCUNUOJUPUQ $.
  $}

  ${
    $d y A $.  $d x y B $.  $d x y C $.  $d x y al $.
    cl.1 $e |- A : be $.
    cl.2 $e |- C : al $.
    cl.3 $e |- [ x : al = C ] |= [ A = B ] $.

    cl $p |- T. |= [ ( \ x : al . A C ) = B ] $=
      ( vy tv ke kbr eqtypi wv ax-17 clf ) ABCJDEFGHIABCEAJKZBDEACKFLMGINAJOZPA
      ACFRHSPQ $.
  $}

  ${
    $d x B $.  $d y C $.  $d x y S $.  $d y T $.  $d x al $.  $d y be $.
    ovl.1 $e |- A : ga $.
    ovl.2 $e |- S : al $.
    ovl.3 $e |- T : be $.
    ovl.4 $e |- [ x : al = S ] |= [ A = B ] $.
    ovl.5 $e |- [ y : be = T ] |= [ B = C ] $.

    ovl $p |- T. |= [ [ S \ x : al . \ y : be . A T ] = C ] $=
      ( kl kbr kc kt ke ht wl wov weq wc wtru df-ov a1i dfov2 distrl ceq1 eqtri
      tv wv weqi cl ) CIJADBEFPZPZQZBEADFPZIRZPZJRZHSABCIJURABCUAZDUQBCEFKUBUBZ
      LMUCZCUSURIRZJRZVCSVFCCUSVHTSCUDVFBCVGJAVDURIVELUEZMUETUSRVHRSUFABCIJURVE
      LMUGUHUIBCJVGSVBVIMVGVBTQSUFABCDEFIKLUJUHUKULBCEVAHJACUTIACDFKUBLUEZMCVAG
      HBEUMZJTQZVJVAGTQVLBVKJBEUNMUOACDFGIKLNUPUHOULUPUL $.
  $}

  $c /\ $.

  $c ==> $.

  tan $a term /\ $.

  tim $a term ==> $.

  ${
    $d f p q x y $.

    df-an $a |- T. |=
        [ /\ = \ p : bool . \ q : bool . [ \ f : ( bool -> ( bool -> bool ) ) .
        [ p : bool f : ( bool -> ( bool -> bool ) ) q : bool ] =
          \ f : ( bool -> ( bool -> bool ) ) .
            [ T. f : ( bool -> ( bool -> bool ) ) T. ] ] ] $.

    df-im $a |- T. |= [ ==> =
      \ p : bool . \ q : bool . [ [ p : bool /\ q : bool ] = p : bool ] ] $.

  $}

  ${
    $d f p q x y $.

    wan $p |- /\ : ( bool -> ( bool -> bool ) ) $=
      ( vp vq vf hb ht tv kbr kl kt ke tan wv wov wl wtru weqi df-an eqtypri )
      DDDEZEZDADBTCDAFZDBFZTCFZGZHZTCIIUCGZHZJGZHZHKIDSAUIDDBUHTDEUEUGTDCUDDDDU
      AUBUCTCLZDALDBLMNTDCUFDDDIIUCUJOOMNPNNCABQR $.

    wim $p |- ==> : ( bool -> ( bool -> bool ) ) $=
      ( vp vq hb ht tv tan kbr ke kl tim kt wan wv wov weqi wl df-im eqtypri )
      CCCDZDCACBCAEZCBEZFGZTHGZIZIJKCSAUDCCBUCCUBTCCCTUAFLCAMZCBMNUEOPPABQR $.

  $}

  ${
    $d f p q x A $.  $d f q x B $.
    imval.1 $e |- A : bool $.

    imval.2 $e |- B : bool $.

    imval $p |- T. |= [ [ A ==> B ] = [ [ A /\ B ] = A ] ] $=
      ( vp vq hb tim kbr tv tan ke kl kt wim wov wan wv weqi id df-im weq oveq1
      oveq oveq12 oveq2 ovl eqtri ) GABHIABGEGFGEJZGFJZKIZUILIZMMZIABKIZALIZNGG
      GABHOCDPGGGABHNUMOCDEFUAUDGGGEFULAUJKIZALIUOABGUKUIGGGUIUJKQGERZGFRZPZUQS
      CDGGGUKUIUPLUIALIZAGUBZUSUQGGGUIUJAKUTQUQURUTGUIAUQCSTZUCVBUEGGGUPAUNLUJB
      LIZVAGGGAUJKQCURPCGGGAUJKVCBQCURVCGUJBURDSTUFUCUGUH $.

    anval $p |- T. |= [ [ A /\ B ] = [ \ f : ( bool -> ( bool -> bool ) ) .
      [ A f : ( bool -> ( bool -> bool ) ) B ] =
        \ f : ( bool -> ( bool -> bool ) ) .
          [ T. f : ( bool -> ( bool -> bool ) ) T. ] ] ] $=
      ( vp vq hb tan kbr ht tv kl kt ke wov wv wl weqi oveq1 wan df-an oveq weq
      wtru id leq oveq2 ovl eqtri ) HBCIJBCHFHGHHHKKZAHFLZHGLZUKALZJZMZUKANNUNJ
      ZMZOJZMMZJUKABCUNJZMZUROJZNHHHBCIUADEPHHHBCINUTUADEAFGUBUCHHHFGUSUKABUMUN
      JZMZUROJVCBCUKHKZUPURUKHAUOHHHULUMUNUKAQZHFQZHGQZPZRZUKHAUQHHHNNUNVGUEUEP
      RZSDEVFVFHUPURVEOULBOJZVFUDZVKVLUKHAUOVDVMVJHHHULUMBUNVMVGVHVIVMHULBVHDSU
      FTUGTVFVFHVEURVBOUMCOJZVNUKHAVDHHHBUMUNVGDVIPZRVLUKHAVDVAVOVPHHHBUMUNVOCV
      GDVIVOHUMCVIESUFUHUGTUIUJ $.
  $}

  ${
    $d f x y A $.  $d f x y B $.
    dfan2.1 $e |- A : bool $.
    dfan2.2 $e |- B : bool $.

    dfan2 $p |- T. |= [ [ A /\ B ] = ( A , B ) ] $=
      ( vf vx vy kbr kt hb kl kc wl ke id a1i weqi oveq eqid wtru tan kct ht tv
      wan wov trud wv wc anval mpbi ceq1 ovl eqtri cl 3eqtr3i mpbir simpl eqtru
      jca simpr oveq12 eqcomi leq ax-cb1 dedi ) ABUAHZABUBZVGABIAVGVGJJJABUAUEC
      DUFZUGZJJJJUCZUCZEABVLEUDZHZKZJFJGJFUDZKZKZLZVLEIIVMHZKZVRLZVGAIVLJVOVRVL
      JEVNJJJABVMVLEUHZCDUFZMZJVKFVQJJGVPJFUHZMMZUIVLJVRVOVGWAWEWGVGVOWANHZVGVG
      VIOVGWHNHZVGVIEABCDUJZPUKZULVSANHVGVIVLJEVNAVRWDWGJVNABVRHZAVMVRNHZWDJJJA
      BVMWMVRWCCDWMVLVMVRWCWGQZOZRWLANHWMWNJJJFGVPAAABWFCDVPANHZJVPAWFCQZOJAJGU
      DZBNHZJWRBJGUHZDQZCSUMPUNUOPWBINHVGVIVLJEVTIVRJJJIIVMWCTTUFZWGJVTIIVRHZIW
      MXBJJJIIVMWMVRWCTTWORXCINHWMWNJJJFGVPIIIIWFTTVPINHZJVPIWFTQZOJIWRINHZJWRI
      WTTQZTSUMPUNUOPUPUQIBVGVJJVOJFJGWRKZKZLZWAXILZVGBIVLJVOXIWEJVKFXHJJGWRWTM
      MZUIZVLJXIVOVGWAWEXLWKULXJBNHVGVIJXJABXIHZBIXMVLJEVNXNXIWDXLJJJABVMVMXINH
      ZXIWCCDXOVLVMXIWCXLQZOZRUOXNBNHITJJJFGWRWRBABWTCDJWRWPWQWTSWSXAOUMPUNPXKI
      NHVGVIVLJEVTIXIXBXLJVTIIXIHZIXOXBJJJIIVMXOXIWCTTXQRXRINHXOXPJJJFGWRWRIIIW
      TTTJWRXDXEWTSXFXGOUMPUNUOPUPUQUTWHVGVHVLJEVNVTVHWDJVTVNVHXBJJJIIAVMVHBWCT
      TAVHABCDURZUSBVHABCDVAUSVBVCVDWIVHAVHXSVEWJPUQVF $.
  $}

  ${
    mp.1 $e |- T : bool $.
    mp.2 $e |- R |= S $.
    mp.3 $e |- R |= [ S ==> T ] $.

    mpd $p |- R |= T $= ? $.
  $}

  $c ind wff F. ~ ! ? \/ ?! typedef 1-1 onto @ $.
