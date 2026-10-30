---
title: "02 Connection with Logic Programming (cf. SICP 4.4)"
---

<h1 id="02-sicp-logic" style="border-bottom: none;">02 Connection with Logic Programming (cf. SICP 4.4)</h1>

<nav class="nav">
    <span class="activenav"><a href="01-megillch2.html">← Previous</a></span>
    <span class="activenav"><a href="index.html">↑ Up</a></span>
    <span class="activenav"><a href="03-interpreter.html">Next →</a></span>
</nav>


> [!NOTE] This is a bonus section! If you don't understand or care about Lisp, 
> or you don't care about Structure and Interpretation of Compute Programs (SICP) ch4-4 
> it's probably not worth it to read. But I worked through the chapter recently so it begs
> the connection.

In this notes section, my goal is to understand automatic proof discovery
and certificate generation using the logic programming of SICP ch4-4.

This is almost certainly not as exciting as it sounds,
SICP ch4-4 is really about expanding your consciousness to think about what 
you can do with computer languages and architectures. It's not about making some
super sophisticated superpowered algorithm that churns out proofs. 

# TODO:

First, we'll implement one simple rule system using the code.

Second, we'll implement the full metamath rules, but I'm pretty sure that with the 
current code this gives infinite recursion. So the infinite recursion can be fixed by 
adding a finite substitution depth, and eventually we "find" the statement `|- t = t` 
in our "database". It would be nice to adapt this to going the other way, enumerating theorems.

Third, we want to modify the code to also write out the metamath certificate.
We don't need to truly print out the valid `.mm` file, we can, in the spirit of SICP chapter 4,
just emit a series of quote symbols in whatever syntax might be convenient. 

Fourth, we can investigate a metamath proof checker written in Lisp? This is a good idea,
but I might do this after the cpp version when I better understand it. 



# Section Scratch Notes

But there
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





