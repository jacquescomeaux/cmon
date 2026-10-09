{-# OPTIONS --without-K --safe #-}

open import Algebra using (CommutativeMonoid)
open import CommutativeMonoids.Congruence using (Congruence)
open import Level using (Level; _⊔_)

module CommutativeMonoids.Quotient
    {c ℓ : Level}
    (M : CommutativeMonoid c ℓ)
    (≋ : Congruence M)
  where

open import CommutativeMonoids.Category using (CommutativeMonoidHomomorphism; mk-⇒)
open import Data.Product using (_,_)
open import Function using (id)

open Congruence ≋

private
  module M = CommutativeMonoid M

-- Quotient of M by congruence relation
M/~ : CommutativeMonoid c ℓ
M/~ = record
    { isCommutativeMonoid = record
        { isMonoid = record
            { isSemigroup = record
              { isMagma = record
                  { isEquivalence = isEquiv
                  ; ∙-cong = cong
                  }
              ; assoc = λ x y z → refl (M.assoc x y z)
              }
            ; identity = (λ x → refl (M.identityˡ x)) , (λ x → refl (M.identityʳ x))
            }
        ; comm = λ x y → refl (M.comm x y)
        }
    }

-- The canonical projection into the quotient
π : CommutativeMonoidHomomorphism M M/~
π = mk-⇒ record
    { ⟦_⟧ = id
    ; isMonoidHomomorphism = record
        { isMagmaHomomorphism = record
            { isRelHomomorphism = record { cong = refl }
            ; homo = λ x y → refl (M.refl {x M.∙ y})
            }
        ; ε-homo = refl (M.refl {M.ε})
        }
    }
