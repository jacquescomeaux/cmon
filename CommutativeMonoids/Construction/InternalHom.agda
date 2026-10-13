{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)

module CommutativeMonoids.Construction.InternalHom {c ℓ : Level} where

open import Algebra using (CommutativeMonoid)
open import CommutativeMonoids.Category using (CommutativeMonoidHomomorphism; _≗_; ≗-isEquivalence)
open import CommutativeMonoids.Homomorphism.PointwiseSum c ℓ using (_+_)
open import CommutativeMonoids.Homomorphism.Zero c ℓ using (𝟎)
open import Data.Product using (_,_)

-- Monoid homomorphisms between two fixed commutative monoids
-- form a commutative monoid.
-- Not actually "internal" unless c = ℓ
CMon[_,_] : CommutativeMonoid c ℓ → CommutativeMonoid c ℓ → CommutativeMonoid (c ⊔ ℓ) (c ⊔ ℓ)
CMon[_,_] M N = record
    { Carrier = CommutativeMonoidHomomorphism M N
    ; _≈_ = _≗_
    ; _∙_ = _+_
    ; ε = 𝟎
    ; isCommutativeMonoid = record
        { isMonoid = record
            { isSemigroup = record
                { isMagma = record
                    { isEquivalence = ≗-isEquivalence
                    ; ∙-cong = λ f≈g h≈k x → ∙-cong (f≈g x) (h≈k x)
                    }
                ; assoc = λ f g h x → assoc (⟦ f ⟧ x) (⟦ g ⟧ x) (⟦ h ⟧ x)
                }
            ; identity = (λ f x → identityˡ (⟦ f ⟧ x)) , (λ f x → identityʳ (⟦ f ⟧ x))
            }
        ; comm = λ f g x → comm (⟦ f ⟧ x) (⟦ g ⟧ x)
        }
    }
  where
    open CommutativeMonoid N
    open CommutativeMonoidHomomorphism using (⟦_⟧)
