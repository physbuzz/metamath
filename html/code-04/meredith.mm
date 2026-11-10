$( Chapter 4 practice: meredith. Supporting proofs are supplied.
   Fill in: merlem1, luk-1, luk-2, luk-3.
   Source: https://us.metamath.org/mpeuni/meredith.html
   The source databases are public domain. $)

$c wff |- -. -> ( ) $.
$v ph ps ch th ta et ze si rh mu la ka $.
wph $f wff ph $.
wps $f wff ps $.
wch $f wff ch $.
wth $f wff th $.
wta $f wff ta $.
wet $f wff et $.
wze $f wff ze $.
wsi $f wff si $.
wrh $f wff rh $.
wmu $f wff mu $.
wla $f wff la $.
wka $f wff ka $.
wn $a wff -. ph $.
wi $a wff ( ph -> ps ) $.
${
 min $e |- ph $.
 maj $e |- ( ph -> ps ) $.
 ax-mp $a |- ps $.
$}
meredith $a |- ( ( ( ( ( ph -> ps ) -> ( -. ch -> -. th ) ) -> ch ) -> ta ) -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $.
  merlem1 $p |- ( ( ( ch -> ( -. ph -> ps ) ) -> ta ) -> ( ph -> ta ) ) $= ? $.

  merlem2 $p |- ( ( ( ph -> ph ) -> ch ) -> ( th -> ch ) ) $=
    ( wi wn merlem1 meredith ax-mp ) BBDZAECEZDDADAADZDKBDCBDDAJIAFBBACKGH $.

  merlem3 $p |- ( ( ( ps -> ch ) -> ph ) -> ( ch -> ph ) ) $=
    ( wi wn merlem2 ax-mp meredith ) AADZCEZJDZDZCDBCDZDZMADCADZDOBEZPDDBDZLDZN
    KKDLDRJKIFKLQFGCABBLHGAACCMHG $.

  merlem4 $p |- ( ta -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $=
    ( wi wn meredith merlem3 ax-mp ) AADBEZIDDBDZCDCADBADDZDCKDAABBCFKJCGH $.

  merlem5 $p |- ( ( ph -> ps ) -> ( -. -. ph -> ps ) ) $=
    ( wi wn meredith merlem1 merlem4 ax-mp ) BBCZBDZJCCBCBCIICCZABCZADZDZBCCZBB
    BBBEIJNDCCBCZACZOCZKOCZBBBNAEOKDZCMTCCZACQCZRSCUAUBMBLTFAPUAGHOTAKQEHHH $.

  merlem6 $p |- ( ch -> ( ( ( ps -> ch ) -> ph ) -> ( th -> ph ) ) ) $=
    ( wi merlem4 merlem3 ax-mp ) BCEZIAEDAEEZECJEADIFJBCGH $.

  merlem7 $p |- ( ph -> ( ( ( ps -> ch ) -> th ) -> ( ( ( ch -> ta ) ->
                  ( -. th -> -. ps ) ) -> th ) ) ) $=
    ( wi wn merlem4 merlem6 meredith ax-mp ) BCFZLDFZCEFDGBGFFZDFZFZFZAPFZDNLHP
    AGZFCGZSFFZCFLFZQRFOUAFUBSMOTICEDBUAJKPSCALJKK $.

  merlem8 $p |- ( ( ( ps -> ch ) -> th ) -> ( ( ( ch -> ta ) ->
                  ( -. th -> -. ps ) ) -> th ) ) $=
    ( wph wi wn meredith merlem7 ax-mp ) EEFZEGZLFFEFEFKKFFZABFCFBDFCGAGFFCFFEE
    EEEHMABCDIJ $.

  merlem9 $p |- ( ( ( ph -> ps ) -> ( ch -> ( th -> ( ps -> ta ) ) ) ) ->
                    ( et -> ( ch -> ( th -> ( ps -> ta ) ) ) ) ) $=
    ( wi wn merlem6 merlem8 ax-mp meredith ) CDBEGZGZGZFHZGBHZPGGZBGABGZGZSOGFO
    GGMRHDHGZHAHGZGUAGRGZTNRGUCPCNQIDMRUBJKBEUAARLKOPBFSLK $.

  merlem10 $p |- ( ( ph -> ( ph -> ps ) ) -> ( th -> ( ph -> ps ) ) ) $=
    ( wi wn meredith merlem9 ax-mp ) AADZAEZJDDADADIIDDZAABDZDZCLDDZAAAAAFLADJC
    EDDADZADNDKNDLAACAFOAMCBKGHH $.

  merlem11 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    ( wi wn meredith merlem10 ax-mp ) AACZADZICCACACHHCCZAABCZCZKCZAAAAAELMCJMC
    ABLFLKJFGG $.

  merlem12 $p |- ( ( ( th -> ( -. -. ch -> ch ) ) -> ph ) -> ph ) $=
    ( wn wi merlem5 merlem2 ax-mp merlem4 merlem11 ) CBDDBEZEZAEZMAEZEZNLOBBEKE
    LBBFBKCGHAMLIHMAJH $.

  merlem13 $p |- ( ( ph -> ps ) ->
              ( ( ( th -> ( -. -. ch -> ch ) ) -> -. -. ph ) -> ps ) ) $=
    ( wi wn merlem12 merlem5 ax-mp merlem6 meredith merlem11 ) BBEZAFZDCFFCEEZN
    FZEZFZEZEAEZAEZABEQBEETUAEZUASUBOREZREZSRCDGRBEZRFPEZEREUCEZUDSEUFUGQPEUFPC
    DGQPHIRUEUFOJIRBRNUCKIIAMSTJITALIBBAQAKI $.

  luk-1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $= ? $.

  luk-2 $p |- ( ( -. ph -> ph ) -> ph ) $= ? $.

  luk-3 $p |- ( ph -> ( -. ph -> ps ) ) $= ? $.
