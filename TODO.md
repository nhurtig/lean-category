Nat has spent many hours on this project this quarter already, and has made lots of progress so far. The progress
is a little hard to measure, because the code is undocumented and not organized (yet). He argues that completing
the non-REACH goals will be good enough for a project, but let him know if not. He might end up doing some
REACH goals anyways.

Steps:
1. DONE: Define what a flipped involutive monoidal category is
    - A flipped involutive monoidal category is an involutive category with a
    twist. Involutive category is a monoidal category with an involution on objects;
    monoidal category is in Mathlib. See Egger "On Involutive Monoidal Categories" for
    the twist/involution with their coherence diagrams and other associated nonsense
1. DONE: Define the free strict flipped involutive monoidal category over a quiver (free nonstrict no-quiver monoidal is in Mathlib;
   free category over a quiver is in Mathlib)
1. DONE: Define the word structure (premorphisms) that the paper canonicalizes: essentially, a hardcore restriction on the
tensor product and a grouping of all the braids (or twists, if you ask a flipped involutive monoidal category)
together
1. DONE save layer: Define the equivalences between words that our paper proves it canonicalizes. The "layer" rewrites (from
the naturality of the braid/twist isomorphism) are very
hard to define; the others are easy to medium.
1. Define the layer rewrites:
    1. Define the layer subgroupoid, a subgroupoid of the free strict flipped involutive monoidal category without
    a quiver that abstractly represents the twists that strands can make adjacent to a layer. Objects are the
    lists containing the bundle of strands connected to the box and each other strand individually, all uniquely
    named
    1. Define the (family of) functor(s) from the layer subgroupoid to the actual braids that turns the bundle
    of strands into the box's strands and renames the surrounding strands to their potentially duplicated names;
    this is $\phi$ from the paper
    1. Similarly define $\tau$ for the bottom (inverse) bits
    1. Now the layer moves are: for any braid $x$ in the layer subgroupoid, slap $\phi(x)$ above and the inverse of
    $\tau(x)$ below
1. Define prefunctors (just on words, not respecting equivalences)
between the "popular" way to define twisted involutive monoidal categories and the
paper's "easy to canonicalize" form
1. Document/clean up/organize the work

REACH: close the loop on representation
1. Show these functors respect equivalences (the layer case will be especially hard)
1. Show these functors perfectly invert each other (not just an equivalence; an isomorphism)
1. Conclude that if we have a decision procedure for our representation, we have a decision
procedure for the original representation by piping through the functors

REACH: use decision procedure for braids for twists
1. Grab Hannah Fetchner's braid decision result
1. Forgetful functor from strict free no-quiver flipped involutive monoidal categories on $n$ strands to
braids on $2n$ strands
1. In defining that functor, we must show that equivalence is preserved
1. Also show that equivalence is not hallucinated: if two braid representations are equal, their twists
must be too
1. Conclude that a braid decision procedure can decide twist equivalence

REACH: show that flipped involutive monoidal categories are substructures of other well-known categories
1. Define a balanced monoidal category as an extension of a braided monoidal category (braided exists in Mathlib!)
1. Show that a flipped involutive category is a balanced monoidal category (hence a braided monoidal category)
1. Also could formalize Egger's claimed properties (like $T_\ell$ vs $T_r$ coherence diagrams)

REACH: visualization
1. Visualizer for words in a free strict flipped involutive monoidal category (no quiver to start with)
1. Incorporate that visualizer into Lean 4's InfoView using widgets
1. Visualize arrows from the quiver as boxes

FUTURE WORK: start defining/proving the paper's canonicalization process
- This is so much work that it doesn't even qualify as a reach goal
