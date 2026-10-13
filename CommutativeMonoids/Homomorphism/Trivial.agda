{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module CommutativeMonoids.Homomorphism.Trivial (c ℓ : Level) where

open import Algebra using (CommutativeMonoid)
open import CommutativeMonoids.Category using (CommutativeMonoids; CommutativeMonoidHomomorphism; mk-⇒)
open import CommutativeMonoids.Trivial c ℓ using (⊤ₘ)

module _ {X : CommutativeMonoid c ℓ} where

  open CommutativeMonoid X hiding (_≈_)

  ! : CommutativeMonoidHomomorphism X ⊤ₘ
  ! = _

  ¡ : CommutativeMonoidHomomorphism ⊤ₘ X
  ¡ = mk-⇒ record
      { ⟦_⟧ = λ _ → ε
      ; isMonoidHomomorphism = record
          { isMagmaHomomorphism = record
              { isRelHomomorphism = record { cong = λ _ → refl }
              ; homo = λ _ _ → sym (identityˡ ε)
              }
          ; ε-homo = refl
          }
      }

  open CommutativeMonoids using (_≈_)

  module _ {f : CommutativeMonoidHomomorphism X ⊤ₘ} where

    !-unique : f ≈ !
    !-unique = _

  module _ {f : CommutativeMonoidHomomorphism ⊤ₘ X} where

    open CommutativeMonoidHomomorphism f

    ¡-unique : f ≈ ¡
    ¡-unique _ = ε-homo
