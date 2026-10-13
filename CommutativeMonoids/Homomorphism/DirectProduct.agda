{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module CommutativeMonoids.Homomorphism.DirectProduct (c ℓ : Level) where

open import Algebra using (CommutativeMonoid)
open import Algebra.Morphism.Construct.DirectProduct using (module Monoid-Export)
open import CommutativeMonoids.Category using (CommutativeMonoids; CommutativeMonoidHomomorphism; mk-⇒)
open import CommutativeMonoids.Construction.DirectProduct c ℓ using (_×_)

open CommutativeMonoidHomomorphism using () renaming (isMonoidHomomorphism to isMH)
open CommutativeMonoids using (_∘_)

module _ {A B : CommutativeMonoid c ℓ} where

  private
    module A = CommutativeMonoid A
    module B = CommutativeMonoid B

  open Monoid-Export

  π₁ : CommutativeMonoidHomomorphism (A × B) A
  π₁ = mk-⇒ record { isMonoidHomomorphism = proj₁ {refl = A.refl} }

  π₂ : CommutativeMonoidHomomorphism (A × B) B
  π₂ = mk-⇒ record { isMonoidHomomorphism = proj₂ {refl = B.refl} }

  module _ {X : CommutativeMonoid c ℓ} where

    ⟨_,_⟩
        : CommutativeMonoidHomomorphism X A
        → CommutativeMonoidHomomorphism X B
        → CommutativeMonoidHomomorphism X (A × B)
    ⟨_,_⟩ f g = mk-⇒ record { isMonoidHomomorphism = < isMH f , isMH g > }

module _ {A B C D : CommutativeMonoid c ℓ} where

  _×ₘ_
      : CommutativeMonoidHomomorphism A B
      → CommutativeMonoidHomomorphism C D
      → CommutativeMonoidHomomorphism (A × C) (B × D)
  _×ₘ_ f g = ⟨ f ∘ π₁ , g ∘ π₂ ⟩

  infixr 8 _×ₘ_
