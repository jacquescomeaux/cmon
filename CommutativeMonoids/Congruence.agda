{-# OPTIONS --without-K --safe #-}

open import Algebra using (CommutativeMonoid)
open import Level using (Level; _⊔_; suc)

module CommutativeMonoids.Congruence
    {c ℓ : Level}
    (M : CommutativeMonoid c ℓ)
  where

import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Relation.Binary using (Rel; IsEquivalence; Setoid)

module M = CommutativeMonoid M

open M using (Carrier; _≈_; _∙_; comm)

private
  variable
    w x y z : Carrier

record IsCongruence (R : Rel Carrier ℓ) : Set (c ⊔ ℓ) where

  field
    refl : x ≈ y → R x y
    sym : R x y → R y x
    trans : R x y → R y z → R x z
    congˡ : R x y → R (z ∙ x) (z ∙ y)

  isEquiv : IsEquivalence R
  isEquiv = record
      { refl = refl M.refl
      ; sym = sym
      ; trans = trans
      }

  private
    setoid : Setoid c ℓ
    setoid = record { isEquivalence = isEquiv }

  open ≈-Reasoning setoid

  congʳ : R x y → R (x ∙ z) (y ∙ z)
  congʳ {x} {y} {z} x≋y = begin
      x ∙ z ≈⟨ refl (comm x z) ⟩
      z ∙ x ≈⟨ congˡ x≋y ⟩
      z ∙ y ≈⟨ refl (comm z y) ⟩
      y ∙ z ∎

  cong : R w x → R y z → R (w ∙ y) (x ∙ z)
  cong {w} {x} {y} {z} w≋x y≋z = begin
      w ∙ y ≈⟨ congʳ w≋x ⟩
      x ∙ y ≈⟨ congˡ y≋z ⟩
      x ∙ z ∎

record Congruence : Set (c ⊔ suc ℓ) where

  infix 4 _≋_

  field
    _≋_ : Rel Carrier ℓ
    isCongruence : IsCongruence _≋_

  open IsCongruence isCongruence public
