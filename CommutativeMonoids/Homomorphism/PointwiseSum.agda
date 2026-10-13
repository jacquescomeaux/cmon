{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module CommutativeMonoids.Homomorphism.PointwiseSum (c ℓ : Level) where

import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Algebra using (CommutativeMonoid)
open import CommutativeMonoids.Category using (CommutativeMonoidHomomorphism; mk-⇒)

module _ {A B : CommutativeMonoid c ℓ} where

  private
    module A = CommutativeMonoid A
    module B = CommutativeMonoid B

  open B

  _+_
      : CommutativeMonoidHomomorphism A B
      → CommutativeMonoidHomomorphism A B
      → CommutativeMonoidHomomorphism A B
  _+_ f g = mk-⇒ record
      { ⟦_⟧ = λ x → f.⟦ x ⟧ ∙ g.⟦ x ⟧
      ; isMonoidHomomorphism = record
          { isMagmaHomomorphism = record
              { isRelHomomorphism = record { cong = λ ≈x → ∙-cong (f.⟦⟧-cong ≈x) (g.⟦⟧-cong ≈x) }
              ; homo = homo
              }
          ; ε-homo = trans (∙-cong f.ε-homo g.ε-homo) (identityˡ ε)
          }
      }
    where
      module f = CommutativeMonoidHomomorphism f
      module g = CommutativeMonoidHomomorphism g
      homo
          : (x y : A.Carrier)
          → f.⟦ x A.∙ y ⟧ ∙ g.⟦ x A.∙ y ⟧ ≈ (f.⟦ x ⟧ ∙ g.⟦ x ⟧) ∙ (f.⟦ y ⟧ ∙ g.⟦ y ⟧)
      homo x y = begin
          f.⟦ x A.∙ y ⟧ ∙ g.⟦ x A.∙ y ⟧             ≈⟨ ∙-cong (f.homo x y) (g.homo x y) ⟩
          (f.⟦ x ⟧ ∙ f.⟦ y ⟧) ∙ (g.⟦ x ⟧ ∙ g.⟦ y ⟧) ≈⟨ assoc _ _ _ ⟩
          f.⟦ x ⟧ ∙ (f.⟦ y ⟧ ∙ (g.⟦ x ⟧ ∙ g.⟦ y ⟧)) ≈⟨ ∙-congˡ (assoc _ _ _) ⟨
          f.⟦ x ⟧ ∙ ((f.⟦ y ⟧ ∙ g.⟦ x ⟧) ∙ g.⟦ y ⟧) ≈⟨ ∙-congˡ (∙-congʳ (comm _ _))  ⟩
          f.⟦ x ⟧ ∙ ((g.⟦ x ⟧ ∙ f.⟦ y ⟧) ∙ g.⟦ y ⟧) ≈⟨ ∙-congˡ (assoc _ _ _) ⟩
          f.⟦ x ⟧ ∙ (g.⟦ x ⟧ ∙ (f.⟦ y ⟧ ∙ g.⟦ y ⟧)) ≈⟨ assoc _ _ _ ⟨
          f.⟦ x ⟧ ∙ g.⟦ x ⟧ ∙ (f.⟦ y ⟧ ∙ g.⟦ y ⟧)   ∎
        where
          open ≈-Reasoning setoid

  infixr 7 _+_
