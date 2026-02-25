two options to define the layer rewrites. Either do the whole layer subgroupoid nonsense,
or just define each layer rewrite individually (L1 left/right inv/not; L2 left/right inv/not; L3 inv/not).

    1. Define the forgetful functor from the free strict flipped involutive monoidal category w/o a quiver
    to the symmetric groupoid (aka all symmetric groups together) direct product with the powers of 2
    groupoid (all powers of 2 groups together)
    as the permutation/twisting respectively of the strands
    1. Define the projection of a "typed braid" with another functor:  NO I don't like this; this requires
    enrichment to have this be a functor, which is annoying
    1. 

Third option: define the untyped versions and define concatenation of typed w/ untyped
(this requires symmetric group on untyped to get the other boundary)

Fourth option: define the asymmetric concatenation of one typed braid w/ another, where the
lengths line up but the colors don't (still requires symmetric group, but whatever)

Fifth option: define the asymmetric concatenation of one typed braid w/ another, where the
lengths line up but the colors don't, and the killed types are unique

Sixth option: screw projections! We don't need them until canonicalization.

Seventh option: Keep the types unique between layers by requiring that they are unique.
Layer change the types at their boundaries. So a layer records the same left/right and input/output
for category isomorphism purposes, but it reports stuff that's much simpler: its codomain is
stuff that's in order with \kappa in the middle; its domain is literally anything that lines up
with its bottom. Even better, we don't need the top stuff to be in order -- just no duplicates!
Well, \kappa can't be the output -- the output strands need to be able to separate, so it needs to
be multiple. Also, there's no sense in marking \kappa because it'll not line up with the other layer
it connects to. Okay, I think we've decided that at SOME point, there has to be a non-functor that
handles global state to figure out objects: maybe it's the enrichment, maybe it's the isomorphism
of categories. But what would the type of the isomorphism be? Takes a Hom X Y and returns a... something?
It'd be nice if the layers all had a guarantee that their objects were duplicate-free, as we could
define projections real quick and easy. But maybe we should leave the jank until the canonicalization
step.

OPTION 6 DECIDED. CAN KICKED.

Later Nat's interpretation of the above:
1. define the layer subgroupoid L as a free no-quiver twist thingy over... lists of \kappa and r's
1. each layer has an "above" and "below" object in L -- a list of \kappa and r's
1. Layer moves are parameterized by twists from "above" \hom anything
1. Define \phi, reconstruction object map, which takes a layer, then an L object, and returns a regular object
1. Note that \phi on "above" is L's codomain
1. Sim. for \tau or smth on "below"

Can we generalize \phi? It's just a function from objects to objects...

Do we need to extend StarMonoid to a SizedStarMonoid where each element has a \N size? Nah...
I think we can just have the r's be indexed with \N (unbounded!) and then \phi maps stuff
with too high of indices to the identity... but how do we index into the sides when they
aren't too high? Well, they're legit List Strand so we should be good.

