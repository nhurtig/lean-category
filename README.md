# lean-category

I've chosen to do a partial formalization of a paper I had on machine knitting. High-level summary:
- Knitting machines manipulate yarns to form knitted objects
- We program machines using programming languages
- We want those languages to have semantics for all sorts of things, but knitting languages don't have any
- Those semantics need to encode *topological* equivalence
- Turns out that a braided monoidal category structure is the right idea
- The paper presents a polynomial-time canonicalization algorithm over words in our braided monoidal
category

The [paper](https://textiles-lab.github.io/publications/2025-knit-equivalence/) is huge: 29 pages of main paper (a little
bit of math, mostly intuition and argument), and 37 pages of appendix (all math, we handwave some category/topology stuff).
The plan is to formalize just a portion of the paper -- the current plan is just to describe the categorical structure that we
canonicalize. This isn't easy: Lean 4/Mathlib doesn't have a notion of the braid group, and it doesn't have a way to form a
(braided) monoidal category from a generating quiver (just a regular old category). Also, our paper's category isn't just
braided, it's "flipped involutive", which is an obscure structure that I bet has never been formalized.
