---
title: "02 Connection with Logic Programming (cf. SICP 4.4)"
---

<h1 id="02-sicp-logic" style="border-bottom: none;">02 Connection with Logic Programming (cf. SICP 4.4)</h1>

<nav class="nav">
    <span class="activenav"><a href="01-megillch2.html">← Previous</a></span>
    <span class="activenav"><a href="index.html">↑ Up</a></span>
    <span class="activenav"><a href="03-interpreter.html">Next →</a></span>
</nav>


Note: This is a bonus section! If you don't understand Lisp and don't care about SICP ch4-4 it might be greek.

In this notes section, my goal is to understand automatic proof discovery
and certificate generation using the logic programming of SICP ch4-4.

This is not as exciting as it sounds,
SICP ch4-4 is really about expanding your consciousness to think about what 
you can do with computer languages and architectures. It's not about making some
super sophisticated superpowered algorithm that churns out proofs. But there
are some analogies and correspondences that I want to understand, namely (using Metamath ch2 as an example problem)...

- In the query system, without changing the code, how do we encode the axioms so we can simply do a query for `'(|- t = t)`?
- As statements grow larger, what's the algorithmic complexity for searching for such a statement?
- In parsing a Metamath proof, I'm told that the unification algorithm used is much simpler than that in SICP 4-4. In doing our "automated proof discovery", do we use the full power of the SICP 4-4 unification algorithm? 
- Is there a way to write our query such that the SICP ch4-4 code basically just does the straightforward parsing of a metamath proof?

Next, modifying the code...

- Once the query system has found `(|- t = t)`, how can we get it to print out the Metamath proof?
- How do we turn the algorithm on its head, and enumerate valid axioms? Do we just add in a maximum stack size of something and search for `(|- . ?x)`? 

And finally...
- How do we implement a metamath kernel in Lean?

## Reviewing SICP 4-4

Remembering how streams work
@src(code/sicp44-1.rkt,collapsed)

Remembering how frames work
@src(code/sicp44-2.rkt,collapsed)

Remembering the pattern match algo
@src(code/sicp44-3.rkt,collapsed)

Remembering the unification algo
@src(code/sicp44-4.rkt,collapsed)





