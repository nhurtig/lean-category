# Definitions and alternative definitions for twisted and involutive monoidal categories

This project has a lot of automation, so it'll probably check slower than
others per line of proof. Once Mathlib is sorted out, it shouldn't take longer
than 10 minutes, around 5 minutes on my average laptop. Notation, definitions,
and big lemmas/theorems are documented, so use your LSP's hover feature
to check them out if confused.

## Interesting stuff (TL;DR)

If you're in a rush, here's the minimal stuff to check out:
- Lots of code and hundreds of lemmas/theorems (mostly simplifying lemmas though)
- Extends Mathlib's existing monoidal category theory to involutive and twisted involutive
monoidal categories, which have not been formalized before ([category definition file](LeanCategory/Basic.lean))
- Uses instance synthesis to enable a coherence tactic to pull out certain morphisms (not my idea;
extended from Mathlib's category theory tactics) ([coherence tactic file](LeanCategory/FreeInvolutive/CoherenceTactic.lean))
([example of use: see `nat_coherence` under `whiskerLeft`](LeanCategory/NatDefinition/Instance.lean))
([example of nonuse: see `twist_conjugation`'s proof, where I have to move twists around (they aren't coherent)
to cancel them. Without the coherence tactics, I'd have to do this for every proof of morphism equality
involving naturality](LeanCategory/NatDefinition/Instance.lean))
- Represents the complicated category theory premorphisms and equalities
in [the category definitions file](LeanCategory/Basic.lean) using the [3 variants in `Hom`](LeanCategory/NatDefinition/Basic.lean)
and [a handful of equalities in `HomEquiv`](LeanCategory/NatDefinition/Basic.lean). Special callout to the `layer`
rule for equality, which uses the ["side effects" of witnesses of layer equality](LeanCategory/NatDefinition/Layer.lean) to rewrite morphisms.
- [An almost completely LLM-generated silly tool](sexpr_diff.py) for comparing the s-expressions of Lean terms
in explicit mode, for figuring out why Lean 4 refused to rewrite by an equality (for me, it was often
universe levels, different synthesized instances, or unsimplifiable expressions in the types)

## AI usage

I tried using Aristotle a couple times; I wasn't impressed (no results, or the
proofs were very ugly and incredibly long). Possible that it was user error; I didn't try too hard
at it. Nothing from Aristotle made it into this repo. About
half the time, I had Copilot suggesting code completions to me. It didn't help
the mentally hard stuff, but it helped greatly with repetitive code/definition
(left vs. right cases, skewator vs. involutor, etc.). I occasionally prompted an
LLM to ask it for help/tips. Success rate was around 30% for those prompts; bits
and pieces (a few lines) were copied from those LLM chats into the code.

You might remember from the "talk to an LLM about your project" assignment that my
LLM told me to use strict definitions for objects, rather than nonstrict, because
that'd be easier. The LLM was very wrong; the strict definitions get you into dependent
type theory trouble much easier (proofs of object equality litter the morphisms); the
nonstrict way is definitely the way to go for proof assistants. I suppose I wouldn't
have learned this lesson if not for the LLM's advice, but it is a cautionary tale to
not follow an LLM's advice unless you understand the material it's giving you advice on
well enough to verify its claims.

## Goal of the project

Machine knitting is used to make lots of textiles, but it's incredibly difficult to program because
programming APIs are low-level (akin to assembly). To enable abstraction more usable languages, we
require semantics for knitting machines. [Nat's paper](https://textiles-lab.github.io/publications/2025-knit-equivalence/)
presents a semantics for knitting based in topology represented by category theory and an efficient
canonicalization algorithm for the words in that category (incredibly useful for compiler correctness and
optimizations). Stitches are represented by free morphisms, and the braids and twists between stitches are
natural isomorphisms.

[An animation of a topological equivalence of two knitted objects](docs/canon_example.mp4)

The proofs in [Nat's paper](https://textiles-lab.github.io/publications/2025-knit-equivalence/) use
a nonstandard representation for morphisms in their category: stitches are always in "layers", which
have only identity strands to their left and right, and morphisms are alternating layers and braids
between layers. This doesn't allow stitches to be directly beside each other in the tensor product.
Additionally, the rewrite rules are quite different.

This project:
- Encodes the categorical definitions referred to in
[Nat's paper](https://textiles-lab.github.io/publications/2025-knit-equivalence/) for the first time
that Nat is aware of
- Defines the free twisted involutive monoidal category with a free quiver, which is exactly what Nat
purports Nat's definition represents
- Defines Nat's definition and proves that it is a twisted involutive monoidal category
- Defines/proves many simplifying lemmas and tactics, both for the categorical definitions
and Nat's definitions
- Defines functors between Nat's definition and the free twisted involutive monoidal category with 
a free quiver
- Shows that if the composition of the functors in one direction is the identity, and if
we have decidable equality on Nat's definition (proved in
[Nat's paper](https://textiles-lab.github.io/publications/2025-knit-equivalence/)),
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

[LeanCategory/NatDefinition/Layer.lean](LeanCategory/NatDefinition/Layer.lean) defines the "layers"
used in Nat's definition, including the ways to rewrite them, presented as a "category" (i.e., categorical
structure but without quotienting by the relations) that projects its "side effects" the free twisted involutive monoidal
category via a "functor" $\phi$.

[LeanCategory/NatDefinition/Base.lean](LeanCategory/NatDefinition/Base.lean) defines Nat's objects (again,
in a very similar way to the previous objects).
[LeanCategory/NatDefinition/Basic.lean](LeanCategory/NatDefinition/Basic.lean) defines Nat's morphisms.
[LeanCategory/NatDefinition/Instance.lean](LeanCategory/NatDefinition/Instance.lean) shows that Nat's
definition is indeed a twisted involutive monoidal category.

[LeanCategory/NatDefinition/ToNat.lean](LeanCategory/NatDefinition/ToNat.lean) defines the functor from the free twisted involutive
monoidal category with a free quiver to Nat's definition using the previous functor definitions.
[LeanCategory/NatDefinition/FromNat.lean](LeanCategory/NatDefinition/FromNat.lean) defines the reverse direction functor; the
"meaning" of Nat's definition in more widely accepted categorical terms.

[LeanCategory/InvolutiveComp.lean](LeanCategory/InvolutiveComp.lean) defines helper definitions/notation for
composition of morphisms up to involutive monoidal coherence, which saves lots of time and space
throughout defining Nat's definition and proving its properties.
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

- [Nat's paper](https://textiles-lab.github.io/publications/2025-knit-equivalence/)
- [The twisted involutive monoidal categories paper](http://www.tac.mta.ca/tac/volumes/25/14/25-14.pdf)
- [A more accessible and shorter, but little outdated, blog post by Nat](https://uwplse.org/2025/03/31/Algebraic-Knitting.html)
- [A great and highly accessible resource about the connections between string diagram topology and category theory,
but it doesn't get into involutions/twists (only monoidal/braids)](https://arxiv.org/abs/0908.3347)

## Future work

[LeanCategory/FunctorCompare.lean](LeanCategory/FunctorCompare.lean) clearly defines the two missing
pieces for full formalization of the paper:
- Show the composition of the functors is the identity. This should be very little work (a couple days by my guess);
just lots of @[simp] lemmas for each case of each functor.
- Show the result of the paper on Nat's definition. This is lots of work, as there are 37 pages of math to get
through. I wouldn't have to deal with Mathlib's category theory though. The paper nicely separates the proof
burden into three stages: reordering layers with the "swap" rule, moving around twists using the "layer" rule,
and canonicalizing the twists between layers. The first two, especially, the "swap" case, will be very difficult.
The twist canonicalization should be more doable by connecting [Hannah Fechtner's MS thesis](https://www.hannahfechtner.com/finallyyy.pdf),
which formalizes the canonicalization of the braid group to the twisted setting.

