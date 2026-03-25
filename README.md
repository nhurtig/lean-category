# Fused braids are a twisted involutive monoidal category

This project has a lot of automation; it takes a couple minutes to build.
Once Mathlib is sorted out, it shouldn't take longer
than 10 minutes, around 5 minutes on my average laptop. Notation, definitions,
and big lemmas/theorems are documented, so use your LSP's hover feature
to check them out if confused.

## Interesting stuff (TL;DR for a Lean person)

If you're in a rush, here's the minimal stuff to check out:
- Extends Mathlib's existing monoidal category theory to involutive and twisted involutive
monoidal categories, which have not been formalized before ([category definition file](LeanCategory/Basic.lean))
- Uses instance synthesis to enable a coherence tactic to pull out certain morphisms (not Nat's idea;
extended from Mathlib's category theory tactics) ([coherence tactic file](LeanCategory/FreeInvolutive/CoherenceTactic.lean))
([example of use: see `fb_coherence` under `whiskerLeft`](LeanCategory/FusedBraids/Instance.lean))
([example of nonuse: see `twist_conjugation`'s proof, where I have to move twists around (they aren't coherent)
to cancel them. Without the coherence tactics, I'd have to do this for every proof of morphism equality
involving naturality](LeanCategory/FusedBraids/Instance.lean))
- Represents the complicated category theory premorphisms and equalities
in [the category definitions file](LeanCategory/Basic.lean) using the [3 variants in `Hom`](LeanCategory/FusedBraids/Basic.lean)
and [a handful of equalities in `HomEquiv`](LeanCategory/FusedBraids/Basic.lean). Special callout to the `layer`
rule for equality, which uses the ["side effects" of witnesses of layer equality](LeanCategory/FusedBraids/Layer.lean) to rewrite morphisms.
- [An almost completely LLM-generated silly tool](sexpr_diff.py) for comparing the s-expressions of Lean terms
in explicit mode, for figuring out why Lean 4 refused to rewrite by an equality (for me, it was often
universe levels, different synthesized instances, or unsimplifiable expressions in the types)

## Goal of the project

Machine knitting is used to make lots of textiles, but it's incredibly difficult to program because
programming APIs are low-level (akin to assembly). To enable abstraction more usable languages, we
require semantics for knitting machines. [Our paper](https://textiles-lab.github.io/publications/2025-knit-equivalence/)
presents a semantics for knitting based in topology represented by category theory and an efficient
canonicalization algorithm for the words in that category (incredibly useful for compiler correctness and
optimizations). Stitches are represented by free morphisms, and the braids and twists between stitches are
natural isomorphisms.

[An animation of a topological equivalence of two knitted objects](images/canon_example.mp4)

The proofs in [our paper](https://textiles-lab.github.io/publications/2025-knit-equivalence/) use
a nonstandard representation for morphisms in their category: stitches are always in "layers", which
have only identity strands to their left and right, and morphisms are alternating layers and braids
between layers. This doesn't allow stitches to be directly beside each other in the tensor product.
Additionally, the rewrite rules are quite different. We'll call this nonstandard representation
"fused braids".

This project:
- Encodes the categorical definitions referred to in
[our paper](https://textiles-lab.github.io/publications/2025-knit-equivalence/) for the first time
that Nat is aware of
- Defines the free twisted involutive monoidal category with a free quiver, which is exactly what Nat
purports fused braids represent
- Defines fused braids and proves that they form a twisted involutive monoidal category
- Defines/proves many simplifying lemmas and tactics, both for the categorical definitions
and fused braids
- Defines functors between fused braids and the free twisted involutive monoidal category with 
a free quiver
- Shows that if the composition of the functors in one direction is the identity, and if
we have decidable equality on fused braids (proved in
[our paper](https://textiles-lab.github.io/publications/2025-knit-equivalence/)),
we have decidable equality on the categorical definition

## Main definitions

[LeanCategory/Basic.lean](LeanCategory/Basic.lean) defines the structure and diagrams for
involutive monoidal categories (adding a functor that "flips" objects to a monoidal category) and
twisted involutive monoidal categories (adding a natural isomorphism that "twists" objects). It also
defines many simplifying lemmas and some lemmas that are consequences of the axioms of twisted/involutive
monoidal categories.

[LeanCategory/FreeInvolutive/Base.lean](LeanCategory/FreeInvolutive/Base.lean) defines the objects
and premorphisms of the free involutve monoidal category.
[LeanCategory/FreeInvolutive/Instance.lean](LeanCategory/FreeInvolutive/Instance.lean) defines the
equivalence relation (commutative diagrams) on premorphisms to form morphisms as a quotient, and
shows that the free involutive monoidal category is indeed an involutive monoidal category.
[LeanCategory/FreeInvolutive/Functor.lean](LeanCategory/FreeInvolutive/Functor.lean) defines functors
from the free involutive monoidal category to some other categories. The folders [LeanCategory/FreeTwisted](LeanCategory/FreeTwisted)
and [LeanCategory/FreeTwistedQuiver](LeanCategory/FreeTwistedQuiver) have the same files, but they define the free twisted
involutive monoidal category and the free twisted involutive monoidal category with a free quiver, respectively.
The duplication is unfortunate, but I do this to use definitional equality later on. These files' structures
were adapted from Mathlib's monoidal category definitions, as they serve the same purpose.

[LeanCategory/FusedBraids/Layer.lean](LeanCategory/FusedBraids/Layer.lean) defines the "layers"
used in fused braids, including the ways to rewrite them, presented as a "category" (i.e., categorical
structure but without quotienting by the relations) that projects its "side effects" the free twisted involutive monoidal
category via a "functor" $\phi$.

[LeanCategory/FusedBraids/Base.lean](LeanCategory/FusedBraids/Base.lean) defines the objects of
fused braids (again,
in a very similar way to the previous objects).
[LeanCategory/FusedBraids/Basic.lean](LeanCategory/FusedBraids/Basic.lean) defines the morphisms
of fused braids
[LeanCategory/FusedBraids/Instance.lean](LeanCategory/FusedBraids/Instance.lean) shows that the
fused braids form a twisted involutive monoidal category.

[LeanCategory/FusedBraids/ToFusedBraids.lean](LeanCategory/FusedBraids/ToFusedBraids.lean) defines the functor from the free twisted involutive
monoidal category with a free quiver to fused braids using the previous functor definitions.
[LeanCategory/FusedBraids/FromFusedBraids.lean](LeanCategory/FusedBraids/FromFusedBraids.lean) defines the reverse direction functor; the
"meaning" of fused braids in more widely accepted categorical terms.

[LeanCategory/InvolutiveComp.lean](LeanCategory/InvolutiveComp.lean) defines helper definitions/notation for
composition of morphisms up to involutive monoidal coherence, which saves lots of time and space
throughout defining fused braids and proving their properties.
[LeanCategory/FreeInvolutive/CoherenceTactic.lean](LeanCategory/FreeInvolutive/CoherenceTactic.lean) defines
a tactic that uses Lean's instance synthesis to prove equalities of morphisms using coherence. Both of these
files' tricks were borrowed from Mathlib's category theory tactics and are not my own, but I did do the
work of adapting them to involutive monoidal categories.

## Main theorems

Every time I define something as a category or functor, I have to prove many properties -- these are the
most difficult results that were proved.

[LeanCategory/FunctorCompare.lean](LeanCategory/FunctorCompare.lean) is the conclusion file; it shows that
if the functor composition is well-behaved and the paper's stated result is true, then we have efficient,
decidable equality on the morphisms of the free twisted involutive monoidal category with a free quiver.

## References

- [Our paper](https://textiles-lab.github.io/publications/2025-knit-equivalence/)
- [The twisted involutive monoidal categories paper](http://www.tac.mta.ca/tac/volumes/25/14/25-14.pdf)
- [A more accessible and shorter, but little outdated, blog post by Nat](https://uwplse.org/2025/03/31/Algebraic-Knitting.html)
- [A great and highly accessible resource about the connections between string diagram topology and category theory,
but it doesn't get into involutions/twists (only monoidal/braids)](https://arxiv.org/abs/0908.3347)

## Future work

[LeanCategory/FunctorCompare.lean](LeanCategory/FunctorCompare.lean) clearly defines the two missing
pieces for full formalization of the paper:
- Show the composition of the functors is the identity. This should be very little work (a couple days by my guess);
just lots of @[simp] lemmas for each case of each functor.
- Show the result of the paper on fused braids. This is lots of work, as there are 37 pages of math to get
through. I wouldn't have to deal with Mathlib's category theory though. The paper nicely separates the proof
burden into three stages: reordering layers with the "swap" rule, moving around twists using the "layer" rule,
and canonicalizing the twists between layers. The first two, especially, the "swap" case, will be very difficult.
The twist canonicalization should be more doable by extending [Hannah Fechtner's MS thesis](https://www.hannahfechtner.com/finallyyy.pdf),
which formalizes the canonicalization of the braid group, to the twisted setting.

It'd also be nice to formalize coherence for involutive monoidal categories, but that's not important for
machine knitting.

It'd also be nice to remove some of the duplication, but I'm not sure that's a good use of my time.

