---
title: "Metamath Study Notes"
---


[Read in html](book/metamath.html) &nbsp;|&nbsp; [Read in pdf](book/metamath.pdf) | [Read on metamath.org](https://us.metamath.org/downloads/metamath.pdf).

# Metamath Study Notes

Studying Metamath and its applications, starting with Norm Megill's 2019 Metamath book. I realized only after creating this layout that it doesn't quite make sense to work through chapter by chapter so I'll have to reorganize these markdown files.

The approach I'll probably take is:

1. read ch2 and refer to ch4 to try to parse the proof in ch2.
2. Read ch4 and write a C++ metamath interpreter, and try it on David Wheeler's [set of mm test cases](https://github.com/david-a-wheeler/metamath-test). (Appendices B, E may be relevant but not needed). Study/implement appendix D, the MIU system.
3. Read ch3 and understand some implications of `set.mm`, while using the commands in ch5.
4. Read appendix C, and perhaps Mario Carneiro's Models for Metamath.
5. Mini formalization project.

For the formalization project, here's a few things I want to study:

- Formalize something regarding Turing machines
- Enumerate the smallest theorems of some theory
- Find the shortest proof of some statement using a SAT solver
- Formalize some theorems in plane geometry from Hilbert's axioms
- Primality certificates (Pratt 1975?)
- Read and create examples from Mario Carneiro "Models for Metamath" 2016

Other things I want to do:

- Write a bonus chapter of SICP, "Metamath using Logic Programming" based on [ch 4.4.](https://www.mathandcode.com/books/sicp/ch4/notes-ch4-4.html), with (probably extremely slow, academic-curiosity-only) automatic proof discovery and certificate generation. I believe the tools of SICP 4.4 make this easy. SICP just implements the machinery and says "people use this for both proofs and databases, isn't that funny?"


I'll probably reorganize this at some point. Studying chapter-by-chapter isn't really


## Contents

- [00 Rant about Mathematical Proof (cf. Megill ch1)](00-rant.html)
- [01 Working through a Metamath Proof by Hand (Megill ch2)](01-megillch2.html)
- [02 Connection with Logic Programming (cf. SICP 4.4)](02-sicp-logic.html)

Planned:

- [03 Writing a Metamath Interpreter (Megill ch4)](03-interpreter.html)
- [04 Looking at set.mm](04-setmm.html)
