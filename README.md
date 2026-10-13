# ComMon

Everything I happen to know about commutative monoids, I guess.

## Commutative Monoids

A commutative monoid,
as formalized in the Agda standard library,
is essentially a setoid equipped with an
equivalence-respecting associative and commutative binary operation
and an identity element.

A homomorphism of commutative monoids
is an equivalence-respecting function
between the underlying setoids.

The category __CMon__ has commutative monoids as objects
and monoid homomorphisms as morphisms.

## Free / Forgetful Adjunction

The forgetful functor, `U`, sending a commutative monoid
to its underlying setoid,
has a left adjoint, `Free`,
the free commutative monoid on a setoid.

For a setoid `A`,
the underlying setoid of the commutative monoid `Free A`
is a setoid with carrier type `List A`
and with permutation of lists as the equivalence relation.
The binary operation is appending lists
and the identity element is the empty list.

Following the adjunction
from __Setoids__ to __CMon__ via `Free`
and back to __Setoids__ via `U`,
we get a monad on __Setoids__,
the _multiset_ monad, `MSet = U ∘ Free`.
This unit of this monad
is the singleton function,
ending an element `x` of the type `A`
to the multiset of type `MSet A` with a single element, `x`.
The join operation is concatenation of multisets:
it collapses a multiset of multisets (something of type `MSet (MSet A)`)
into a single multiset (of type `MSet A`).

Dually, a round trip starting from __CMon__
gives a comonad on CMon,
the _formal sum_ comonad, `⅀ = Free ∘ U`.
For a commutative monoid `M`,
`⅀ M` is a commutative monoid whose
elements are formal sums of elements of `M`,
represented as lists of elements
with append for addition,
empty list for identity,
and permutation for equivalence.
The counit homomorphism
evaluates a formal sum in `⅀ M`
back into an element of `M`.
The comultiplication homomorphism,
from `⅀ M` to `⅀ (⅀ M)` converts each term
of a formal sum to a formal sum with a single term.

## Quotient

A congruence relation on commutative monoid `M`
is an equivalence relation `_≋_` on the underlying setoid
such that if `x ≋ y` then `z + x ≋ z + y`.
Importantly, `_≋_` must be an equivalence relation
with respect to the equivalence on `M`,
meaning reflexivity takes the form `x ≈ y` implies `x ≋ y`,
rather than just `x ≋ x`.

Given such a congruence relation,
we can form the quotient `M/≋`
and the canonical projection (a homomorphism)
from `M` to `M/≋` sending each element
to its equivalence class.
Conceptually,
the quotient is the original commutative monoid
with the minimum amount of identifications imposed
to make elements related by `_≋_` actually equal,
and this is expressed via a universal property.
