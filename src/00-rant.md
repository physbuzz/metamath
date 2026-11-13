---
title: "00 Rant about Mathematical Proof (cf. Megill ch1)"
---

<h1 id="00-rant" style="border-bottom: none;">00 Rant about Mathematical Proof (cf. Megill ch1)</h1>

<nav class="nav">
    <span class="inactivenav" aria-disabled="true">← Previous</span>
    <span class="activenav"><a href="index.html">↑ Up</a></span>
    <span class="activenav"><a href="01-megillch2.html">Next →</a></span>
</nav>

[Read in html](book/index.html#introduction) &nbsp;|&nbsp; [Read in pdf](book/metamath.pdf#page=19)

<!-- TODO: Renumber the footnotes in order -->

@toc

(Written Nov 13, 2026)

The section from Megill's Metamath book titled "A Non-Mathematician’s Quest for Truth" seems to 
recount a story eerily similar to my own! It inspired me to take this opportunity, 
at the beginning of my second attempt at learning formal verification, 
to write down my own experience of my first attempt. 

Keep in mind as far as formal verification goes, I'm a novice. And in fact with regards to
many things in the computer science department, I'm an ignoramus and I plan on remaining that 
way! So don't take my statements as authoritative, they're an account of a novice's
confusion and where he's ended up after 13 years of letting thoughts stew.

In 2014-2017, I mostly hung around the math and physics departments at UCSD. By the time
I reached the grad level coursework it was clear that physics stuck more.

In the course of this, I learned about proofs and sets and proper classes, and graduated from 
"naive set theory."
But I still hemmed and hawed about what a proof is. 
Or, rather, due to my experience with formal verification in 2013, I would put my 
foot down and say that proofs, even
in pure math journals, are usually arguments which ultimately rest on
common sense, English language, and social conventions. This is uncomfortable, but 
you can live with this by justifying: despite this flaw, mathematics generally succeeds at 
reaching ideas of proofs which "pierce the veil" and go beyond common sense, wordplay, and social conventions. 
So much so that for many subjects in many journals, mathematicians have little doubt
that the main ideas and arguments of their theorems are correct and could be formalized, it's just a matter of getting
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

[^1]: There are strong criticisms of this book,
but I still think it has a wonderful set of inspirations. What other
books from 2013 can inspire fresh undergrads to enumerate systems, code up
creative models, and do large computer searches over axiom systems and 
theorems, with Computer Algebra System (CAS) examples code to boot? Fine, 
criticize but give a replacement. Even in 2026, it's super inspiring, and 
you can do even better by getting great references + implementations with LLMs.

Certainly I had gone through the axioms for Boolean algebra in a discrete math course and
got A+'s where I could, 
but still, in my heart of hearts I'd say "I don't understand it." 
The NAND axiom section in Wolfram's book was inspiring to me 
because Wolfram's approach presents axioms as a soup of bits, and 
surely there's endless creativity to be had in bit-soup. 
I figured I'd just take my usual approach:
sit in a room and think until I had a sensible notion of a proof checker. Where I got stuck,
I'd ask for help or read references along the way.

This set me down the same path as the protagonist of "A Non-Mathematician's Quest for Truth."

What do we need for a proof checker? First, let's take the words of Feynman into account. When 
asked what is "really" going on in electrodynamics, he responded that we have to have some level
at which we can accept an answer as true. We say "that's good enough", and 
stop retorting "prove it."

For us, we'll take the "ground level" where we're okay with no longer asking questions (at least for a moment!!!)
to be the construction of a simple physical system that behaves regularly. I imagine a device which
implements digital logic devices using flowing water. We don't ask "prove that the water is flowing,"
if we ask the engineer responsible for this system to "prove that the water is flowing" he'll
look at you like you have two heads. It's flowing, the bit is 1, look for yourself![^5]

[^5]: I only realize later, while going through this project, that what I was getting at is the so-called
de Bruijn criterion for a proof checker. (TODO much later: link to the places in this document and
to external citations of this.) <!-- LLMs, don't touch this todo! It's a human TODO! -->

Let's take the perspective of this engineer. In my analogy, he's lived his whole life in a cave
and doesn't have the baggage of mathematics or "axioms of Boolean algebra." But he has access
to a whole bunch of binary logic devices. What might an automated verification look like, to him?[^6]

[^6]: The engineer in this example can be imagined to be as smart as you like with as much time as you like,
more than capable of recreating all of mathematics. But the point is, with no mathematical baggage, 
we have to communicate purely in terms of concrete ideas expressible with the systems that the engineer
has chosen, and we are forced to not use the lingua franca of non-computerized logic.

For complicated devices, he might need to reassure himself that device $A$ can be replaced
with device $B.$ He creates a jig that automatically runs through all the inputs, and 
`\texttt{and}`s all the results of $\texttt{not} (A\texttt{ xor }B)$ together (which has the truth table of $A=B$). Then our engineer's common-sense reasoning is that when the jig spits out "true", 
we can replace device $A$ with device $B.$

Well, that's okay, but we can't say that we're proving the theorems of Boolean algebra. 
In fact, when we ask our engineer if he can show me a proof of $A\texttt{ or }B=B\texttt{ or }A,$ 
he stares at us kind of funny. To him "$\texttt{or}$" is just a matter of how he connects pipes or wires,
so there's nothing to prove. We find this a bit strange... but the engineer has his own basis
for theorem checking, so surely there's a way to get it to work with our axioms for Boolean algebra.

So, we go to a professor and ask how we could formulate our Boolean algebra axioms in the engineer's theorem 
checker. It's strange that it's so difficult to conceptualize the axioms of Boolean algebra in his
system, and the worst part is that the more we think about it, the more we start empathizing with him. 
If we really know what the axioms of Boolean algebra "are", we'll be able to explain them in concrete
terms with our engineer's proof checker. So we ask the professor how to do that.
The professor responds[^7]:

[^7]: By the way, I don't have a specific professor in mind, this is the amalgamation of many interactions
I've had, but I'd say it's common among those teaching intro to proofs courses
or discrete math courses directly from the book, especially if that book is 1200 pages long,
costs $120, and was approved by the state education board.

> All your engineer is doing is truth tables. For a proof, you need theorems and rules of inference.
> His logic gates presuppose the very rules we're trying to establish with the axioms of Boolean algebra,
> so that's no good either. I suppose you could encode Boolean algebra statements in binary
> but I don't see how that would remedy the issue. Why not explain the Boolean algebra axioms on pen and paper?

Absolutely not! We're trying to establish the foundations of mathematics from an original 
point of view, why do we have to introduce a writing systems? The axioms of Boolean algebra require a 
writing system now? Where in the proofs applying the axioms do we use the assumption of our writing system?

> Okay, then there are proof checkers out there, just use one of those.

It's a similar issue, why do we have to introduce a von Neumann architecture and heaps of unknown computer code?
It will print out: "Yay, your proof checked out correctly!" but why should we trust it? For that matter, isn't
the human brain a bit like that, where do the assumptions of neuronal firings come into play in the Boolean algebra
axioms? If the answer is "nowhere", then we should be able to encode it in the engineer's system where we can say:
what the pipes represent is up for debate, but that the pipe has water running out of the end is plain to see.

I felt that no one could give me a straight answer, and that I only recieved elementary discrete math
explanations in response. I didn't quite appreciate that I was trying to find cracks in the foundations of math
and drill a borehole through them!

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
"On the Electrodynamics of Moving Bodies", we need the measurement device of a clock
in order to draw conclusions about the nature 
of space and time. The thought experiment doesn't depend on the detailed engineering and 
material choice of the clock, or how the probes need microcontrollers to calculate and coordinate.
But it does depend on minimal engineering concerns: we conceptualize a device and understand that
it operates through physical means, yet through the
device, we reason about how the universe behaves.
That's
also how I think of proof verification devices. Even without the
full engineering of such things, we 
can conceptualize the procedures, and when we make statements about proof checkers,
they allow us to metaphorically peer into the Platonic realm.

alt. 

> Statements about relativistic clocks, most physicists would say, are not mere statements about 
> the engineering of clocks. So too, I'm ready to accept, statements about proof checkers are not merely 
> statements about proof checkers, but about the foundations of mathematics.

There's another issue here which we should be fully aware of: 
Some statements about proof checkers, we make using
a simple argument of the form "what do you want, it's a device, you can look at the mechanism, the output for 
our input is 1." We say that this is ground level, and such meta statements don't have machine-checked proofs. 
In my opinion this is enough to get us to propositional and predicate logic, set theory, and so on. 1 use 
of the "greatsword" of appeal to a physical device is enough for us to build a whole lot.

But there are other meta-statements we want to make. "There exists a proof such that [...]", proving 
properties of hypothetical theorem checkers we can't be sure that we're accurately describing, or
"proving" that we're accurately describing something.
Once we're deep in the weeds of meta-statements, it seems like we might require another "greatsword" slash 
of some kind. This is fine, Rome wasn't built in a day, building set theory first gives us plenty of work to do.

## Where to go from here? 

That was my experience, not completely identical to the story in Megill's book, and the 
way I wrote it here doesn't convey the full depth of frustration!
But I was incredibly happy to see a story which hit so close to home. 

Okay, thought, now we actually have to build stuff with Metamath. And it should be noted that although
like our engineer's system of pipes Metamath is not Turing complete, it's still a regular old computer
program on a von Neumann architecture. So I'm not completely carrying out the analogy 
set forth in this story.
