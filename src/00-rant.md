---
title: "00 Rant about Mathematical Proof (cf. Megill ch1)"
---

<h1 id="00-rant" style="border-bottom: none;">00 Rant about Mathematical Proof (cf. Megill ch1)</h1>

<nav class="nav">
    <span class="inactivenav" aria-disabled="true">← Previous</span>
    <span class="activenav"><a href="index.html">↑ Up</a></span>
    <span class="activenav"><a href="01-megillch2.html">Next →</a></span>
</nav>

[Read in html](book/metamath.html#introduction) &nbsp;|&nbsp; [Read in pdf](book/metamath.pdf#page=19)

> [!NOTE]
> This is a draft! Last updated Oct 28 2026, at the hour of "oh jeez is it really 3am?"

@toc

The section from Megill's Metamath book titled "A Non-Mathematician’s Quest for Truth" seems to 
recount a story eerily similar to my own! It inspired me to take this opportunity, 
at the beginning of my second attempt at learning formal verification, 
to write down my own experience of my first attempt. 

Keep in mind as far as formal verification goes, I'm a novice. And in fact with regards to
many things in the computer science department, I'm an ignoramus and I plan on remaining that 
way! So don't take my statements as authoritative, they're an account of a novice's
confusion and where he's ended up after 13 years of letting thoughts stew.

In 2014-2017, I mostly hung around the math and physics departments and got degrees in both.
I later went on to get a masters in physics and only got a C in the graduate abstract algebra
coursework, so you can easily figure out which one stuck more.

I learned plenty about proofs and sets and proper classes, and I graduated from "naive set theory", 
but I still hemmed and hawed about what a 
proof is. Or, rather, due to my experience with formal verification in 2013, I would put my 
foot down and say that proofs, even
in pure math journals, are usually arguments which ultimately rest on
common sense, English language wordplay, and social conventions. This is uncomfortable, but 
you can live with this by justifying: despite this flaw, mathematics generally succeeds at 
reaching ideas of proofs which "pierce the veil" and go beyond common sense, wordplay, and social conventions. 
So much so that for many subjects in many journals, mathematicians have little doubt
that the main ideas and arguments of their theorems are correct, it's just a matter of getting
the computer to behave. And besides, if you want the ultimate in rigor, what are you going to do?
Waste your undergrad formalizing introductory math that everyone already knows? "Let's 
get on with our lives and publish good research!" 

Fine. But then surely *someone* has got down to the foundation, right?

## My version of Megill's Rant
In 2013, I had just started seriously studying math. So, absorbing the lessons
of Cantor from Velleman's book "How to Prove It", then on to real analysis from Rudin's book
and point set topology from osmosis. I also jumped into the deep end with the 2013 Coursera 
course on functional analysis taught by John Cagnol, where a few peer-graded assignments 
came back as "not rigorous enough," though I tried to use the same level of rigor as the 
instructor.

Though it's steeped in rigor, most of these things didn't quite inspire creativity from me 
until I read Stephen Wolfram's A New Kind of Science[^1]. There's a section on the axioms for
Boolean algebra, and proving that a set of axioms can follow from a single NAND axiom.

[^1]: It's in vogue to rag on this book now, but I still think it has a wonderful set of inspirations. What other
books from 2013 can inspire fresh undergrads to enumerate systems, code up
creative models, and do large computer searches over axiom systems and 
theorems, with Computer Algebra System (CAS) examples code to boot?

I found the NAND axiom inspiring, especially because Wolfram's approach presents it as a 
soup of bits, and surely there's endless creativity to be had in bit-soup. 
I figured I'd just take my usual approach:
sit in a room and think until I had a sensible notion of a proof checker. Where I got stuck,
I'd ask for help or read references along the way.

What did I need for a proof checker? First, I took the words of Feynman into account. When 
asked what is "really" going on in electrodynamics, he responded that we have to have some level
at which we can accept an answer as true. We say "that's good enough", and 
stop retorting "prove it."

My "ground level" where I'm okay with no longer asking questions, is when an engineer can show
me some simple physical system and show that it behaves regularly. If it's a simple device
implementing digital logic using flowing water, I can't ask the engineer "prove that the 
water is flowing." He'll look at me like I have two heads and say "look for yourself!" 
On the other hand, if we can show that a certain configuration of digital logic gates has
some interesting effect, or can be replaced with a simpler one, he'll be interested.

Let's take the perspective of this engineer. In my analogy, he's lived his whole life in a cave
and doesn't have the baggage of mathematics or "axioms of Boolean algebra." But he has access
to a whole bunch of binary logic devices. What might an automated verification look like, to him?

For complicated devices, he might need to reassure himself that device $A$ can be replaced
with device $B.$ He creates a jig that automatically runs through all the inputs, and 
`\texttt{and}`s all the results of $\texttt{not} (A\texttt{ xor }B)$ together (which has the truth table of $A=B$). Then our engineer's common
sense reasoning is that when the jig spits out "true", 
we can replace device $A$ with device $B.$

Well, that's okay, but we can't say that we're proving the theorems of Boolean algebra. 
In fact, when we ask our engineer if he can show me a proof of $A\texttt{ or }B=B\texttt{ or }A,$ 
he stares at us kind of funny. To him "$\texttt{or}$" is just a matter of how he connects pipes or wires,
so there's nothing to prove. It's possible to extend the types of deduction he does, but 
difficult to do so without making him do all the theorem proving work (potentially amounting
to staring at a circuit and saying "yep, that works," which is no foundation to stand on). 

So, we go to a professor and ask where we can continue the analogy so that the engineer
can complete his automated theorem prover. We also say, it's a bit strange that this engineer
can't conceptualize the axioms of Boolean algebra, and I'm starting to empathize with him too! 
The professor responds, 

> Well, all your engineer is doing is truth tables. A proof is a finite sequence of statements
> each of which follows from previous statements and ultimately axioms by rules of inference.
> Your engineer isn't doing that, and his logic gates presuppose the very rules we're trying
> to establish by the axioms of Boolean algebra.

Maybe after a few rounds of back and forth, the professor responds,

> Why not give the engineer a pen and paper?

Absolutely not! We're trying to establish the foundations of mathematics from an original 
point of view, why do we have to introduce human writing systems? Or if we use computer code,
why do we have to introduce a von Neumann architecture? Why not water pipes implementing 
digital logic? Why not an architecture that finds the ground state of a large classical or quantum system? Why not any number of complicated contraptions that we nevertheless contort to give
us some idea of "proof", which seems to be exactly what we're doing with the human brain?

I felt that no one could give me a straight answer, recieving elementary discrete math
explanations in response, when really I wanted to find the foundations of math and 
drill a borehole through them!

After a few exchanges like this I decided that Mathematica and logic circuits weren't it. 
I shelved the PNP transistors that 
I bought to try and embody my own engineer-in-a-cave analogy. I listened to the appeals to 
authority and followed the authority, ignoring the constant refrain of "don't waste your time
on formal verification, you'll waste your undergrad and write another Principia Mathematica proving some trivial fact." Well, I didn't fully ignore the advice, because to save time I 
sought out the proof system that could take me the furthest.
At the time, the biggest library of formally verified
other-peoples'-knowledge was the Mizar proof system!

I had no success here either. I spent a long time trying to understand, and running programs, 
but I had a totally unpleasant time. Maybe I was impatient and nearsighted, or maybe I didn't
appreciate the CS masters degrees that everyone else on the forum seemed to have, or 
any number of things. 
The final straw was when I was reading about Hilbert's axioms. I figured I could try experimenting with plane geometry proofs using these axioms, or at least understanding one or two of the axioms. Someone on the Mizar mailing list called them 
Hilbert's "axioms" in quotes. So okay, I figured: even Hilbert trying to be ultra-precise couldn't get
the level of precision needed for a computer proof, no one can explain to me what that 
level of precision is, there's a system that runs code and spits out "true" but I don't understand the system or the code or why I should accept this, and people say it's too complicated to try to recreate myself. I've spent months on this while making no progress! I made the natural conclusion:

"Screw this, I have coursework to do!" 
I threw my hands up in frustration and left.


### Thirteen years later...

With the benefit of hindsight and mathematical maturity, I think I can now understand the 
resolution of the above. Again, we focus on the engineer analogy and the engineer's concept
of a proof.

First, his concept of a proof checker is fine, and maybe is even good for a foundation of 
mathematics with a little more elbow grease[^2]. But the assertions
that the engineer naturally wants to make about the ability of various digital logic assemblies
to be replaced with each other,
is not the same as proving theorems in what modern mathematicians
understand as "the axioms of Boolean algebra." Once we start talking about Boolean algebra, 
we indeed have to pull in the cultural and human-specific baggage, and this is where the 
conversation with the imagined discrete math professor can become frustrating.

[^2]: I emphasize elbow grease, because I've avoided thinking about a clock or a latch in
the engineer's digital circuits. I'm truly imagining the non-turing-complete tautology-checker
machine as being a foundation for our engineer's formally verified mathematics, 
but to really be convinced of this we'd need
a separate article and examples, and plenty of creativity. If, at the end of the day, we need
to introduce clock and latch devices in order to make a convincing proof checker, 
I don't think it changes the conclusion. 

In order to embody the mathematicians' notion of Boolean algebra, the engineer would have 
to construct a complicated representation in terms of his digital devices, where strings of 
symbols represent the axioms. Suddenly, we can talk about the commutativity of the $\texttt{or}$
operator to our engineer friend! It's translated into a statement about a more complicated
representation where the device built is not manifestly symmetric at all, or may have more than two inputs[^3].
To us, the device looks strange. To the engineer, he exclaims, "this is the weird thing you 
were talking about? I see what you mean now!"

[^3]: By a complicated representation, maybe we represent "or" by a bit string "001", and the 
bit "0" is always off, while the bit "1" faithfully reproduces the input. Then "or" is represented by a particular logical function on three arguments, and this is how our engineer thinks of 
the Boolean algebra "or". There's all sorts of tricks we can reach for here, 
Church encodings, etc. plenty of options.

This also lets us catch our breath and continue to interesting questions. There's still
circular reasoning in there, and I'm using the engineer's blank stare and statement "the output
is 1, what else do you want?" as a greatsword to cut the proverbial Gordian knot. But that's fine,
a physics background trains you to accept such things! For example, in Einstein's 1905 paper
"On the Electrodynamics of Moving Bodies", he needs the measurement device of a clock
 in order to draw conclusions about the nature 
of space and time. The thought experiment doesn't depend on the detailed engineering and 
material choice of the clock, or how the probes need microcontrollers to calculate and coordinate.
But it does depend on minimal engineering concern: we conceptualize a device and through the
device, we reason about how the universe behaves.
That's
also how I think of proof verification devices. Even without the
full engineering of such things, we should
can conceptualize the procedures, and when we make statements about proof checkers,
they allow us to peer into the Platonic realm.

alt. 

> Statements about relativistic clocks, most physicists would say, are not mere statements about 
> clocks. So too, I'm ready to accept, statements about proof checkers are not merely 
> statements about proof checkers, but about the foundations of mathematics.


## Where to go from here? 

That was my experience, not identical to Megill's story under the section heading 
"A non-Mathematician's Quest for Truth," and the way that I told it here is wildly less 
frustrating than it was in reality. But I was incredibly happy to see a story which hit so
close to home. 

So what now? Well, the framing in the last section[^4] is merely a statement of overcoming
one hurdle, and understanding at what level I can happily stop my line of inquiry, 

[Essay WIP]


[^4]: I use the word "framing" and not "conclusion" because I'm still a novice, and being
highly skeptical, I wouldn't be prepared to say every assertion I hinted at holds. 

