{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module CommutativeMonoids.Homomorphism.Zero (c ℓ : Level) where

open import Algebra using (CommutativeMonoid)
open import CommutativeMonoids.Category using (CommutativeMonoidHomomorphism; mk-⇒)

module _ {A B : CommutativeMonoid c ℓ} where

  open CommutativeMonoid B

  -- The "zero" homomorphism sends everything to ε
  𝟎 : CommutativeMonoidHomomorphism A B
  𝟎 = mk-⇒ record
      { ⟦_⟧ = λ _ → ε
      ; isMonoidHomomorphism = record
          { isMagmaHomomorphism = record
              { isRelHomomorphism = record { cong = λ _ → refl }
              ; homo = λ _ _ → sym (identityˡ ε)
              }
          ; ε-homo = refl
          }
      }
