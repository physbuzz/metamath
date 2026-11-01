


I am PUMPED 
Let's get to the point where we can parse a proof and print out the Lemmon form of the proof.

TODO: 
- ~~When we parse any statement, we need to verify all the variables used are active.~~
- ~~When we parse a proof, we need to verify all of the hypotheses used are active hypotheses.~~
- When we parse a proof, essential, or axiom, we need to find all of the mandatory
hypotheses and track them.
    To find the mandatory hypotheses, it's a lil convoluted, we'll do it in a slow O(N^2) way. Step 1 is to go up the list of active hypotheses and collect all essential hypotheses in a set, while parsing them. For any variable in an essential hypothesis, or variable in the symbols list of the statement itself, we find the floating hypothesis that defines that variable, and add it to the list of mandatory hypotheses. Finally, we do a second pass up the list of active hypotheses (iterate from 0), and push anything in our set to the list of mandatory hypotheses.


To find all essential hypotheses, 

    ${
        min $e |- P $.
        maj $e |- ( P -> Q ) $.
        mp $a |- Q $.
    $}
$( Prove a theorem $)
    th1 $p |- t = t $=
    $( Here is its proof: $)
        tt tze tpl tt weq tt tt weq tt a2 tt tze tpl
        tt weq tt tze tpl tt weq tt tt weq wim tt a2
        tt tze tpl tt tt a1 mp mp
    $.