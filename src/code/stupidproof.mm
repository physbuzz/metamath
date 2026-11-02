$v a b c $.
$c term |- V $.

term_a $f term a $.
term_b $f term b $.
term_c $f term c $.

${
    stmnt_b $e |- b $.
    myproof $p |- b $= stmnt_b $.
$}



${
    stmnt_b2 $e |- b $.
    remove_variable $a |- $.
$}

chaos_axiom $a |- c $. 

b_is_true $p |- b $= term_b term_b chaos_axiom myproof $.

proof_of_turnstile $p |- $= term_a term_a chaos_axiom remove_variable $.


