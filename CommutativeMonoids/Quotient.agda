{-# OPTIONS --without-K --safe #-}

open import Algebra using (CommutativeMonoid)
open import CommutativeMonoids.Congruence using (Congruence)
open import Level using (Level; _⊔_)

module CommutativeMonoids.Quotient
    {c ℓ : Level}
    (M : CommutativeMonoid c ℓ)
    (≋ : Congruence M)
  where

open import CommutativeMonoids.Category
  using (CommutativeMonoidHomomorphism; mk-⇒; _≗_)
  renaming (module CommutativeMonoids to CMon)
open import Data.Product using (_,_)
open import Function using (id)
open import Relation.Binary using (_Preserves_⟶_)

open Congruence ≋

private
  module M = CommutativeMonoid M

-- Quotient of M by congruence relation
M/≋ : CommutativeMonoid c ℓ
M/≋ = record
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
π : CommutativeMonoidHomomorphism M M/≋
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

-- Universal property of the quotient
module Universal
    {N : CommutativeMonoid c ℓ}
    -- A homomorphism that equates elements related by _≋_
    (f : CommutativeMonoidHomomorphism M N)
    (let private module N = CommutativeMonoid N)
    (let private module f = CommutativeMonoidHomomorphism f)
    (preserves-≋ : f.⟦_⟧ Preserves _≋_ ⟶ N._≈_)
  where

  -- The induced homomorphism out of the quotient
  induced : CommutativeMonoidHomomorphism M/≋ N
  induced = mk-⇒ record
      { ⟦_⟧ = f.⟦_⟧
      ; isMonoidHomomorphism = record
          { isMagmaHomomorphism = record
              { isRelHomomorphism = record { cong = preserves-≋ }
              ; homo = f.homo
              }
          ; ε-homo = f.ε-homo
          }
      }

  open CMon using (_∘_)

  -- The equating homomorphism factors through the canonical projection via its induced homomorphism
  factors : f ≗ induced ∘ π
  factors x = N.refl

  -- The induced homomorphism is the unique factorizing homomorphism
  unique : (g : CommutativeMonoidHomomorphism M/≋ N) → f ≗ g ∘ π → g ≗ induced
  unique _ f≗g∘π x = N.sym (f≗g∘π x)
