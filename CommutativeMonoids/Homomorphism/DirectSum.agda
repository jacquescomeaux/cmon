{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module CommutativeMonoids.Homomorphism.DirectSum (c ℓ : Level) where

import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Algebra using (CommutativeMonoid)
open import CommutativeMonoids.Category using (CommutativeMonoids; CommutativeMonoidHomomorphism; mk-⇒)
open import CommutativeMonoids.Construction.DirectSum c ℓ using (_⊕_)
open import Data.Product using (_,_)

open CommutativeMonoids using (_∘_)

module _ {A B : CommutativeMonoid c ℓ} where

  private
    module A = CommutativeMonoid A
    module B = CommutativeMonoid B

  i₁ : CommutativeMonoidHomomorphism A (A ⊕ B)
  i₁ = mk-⇒ record
      { ⟦_⟧ = _, B.ε
      ; isMonoidHomomorphism = record
          { isMagmaHomomorphism = record
              { isRelHomomorphism = record { cong = _, B.refl }
              ; homo = λ x y → A.refl , B.sym (B.identityˡ B.ε)
              }
          ; ε-homo = A.refl , B.refl
          }
      }

  i₂ : CommutativeMonoidHomomorphism B (A ⊕ B)
  i₂ = mk-⇒ record
      { ⟦_⟧ = A.ε ,_
      ; isMonoidHomomorphism = record
          { isMagmaHomomorphism = record
              { isRelHomomorphism = record { cong = A.refl ,_ }
              ; homo = λ x y → A.sym (A.identityˡ A.ε) , B.refl
              }
          ; ε-homo = A.refl , B.refl
          }
      }

  module _ {X : CommutativeMonoid c ℓ} where

    open CommutativeMonoid X


    [_,_]
        : CommutativeMonoidHomomorphism A X
        → CommutativeMonoidHomomorphism B X
        → CommutativeMonoidHomomorphism (A ⊕ B) X
    [_,_] f g = mk-⇒ record
        { ⟦_⟧ = λ (x , y) → f.⟦ x ⟧ ∙ g.⟦ y ⟧
        ; isMonoidHomomorphism = record
            { isMagmaHomomorphism = record
                { isRelHomomorphism = record { cong = λ (≈x , ≈y) → ∙-cong (f.⟦⟧-cong ≈x) (g.⟦⟧-cong ≈y) }
                ; homo = λ (x₁ , y₁) (x₂ , y₂) → homo x₁ x₂ y₁ y₂
                }
            ; ε-homo = trans (∙-cong f.ε-homo g.ε-homo) (identityˡ ε)
            }
        }
      where
        module f = CommutativeMonoidHomomorphism f
        module g = CommutativeMonoidHomomorphism g
        homo
            : (x₁ x₂ : A.Carrier)
              (y₁ y₂ : B.Carrier)
            → f.⟦ x₁ A.∙ x₂ ⟧ ∙ g.⟦ y₁ B.∙ y₂ ⟧ ≈ (f.⟦ x₁ ⟧ ∙ g.⟦ y₁ ⟧) ∙ (f.⟦ x₂ ⟧ ∙ g.⟦ y₂ ⟧)
        homo x₁ x₂ y₁ y₂ = begin
            f.⟦ x₁ A.∙ x₂ ⟧ ∙ g.⟦ y₁ B.∙ y₂ ⟧             ≈⟨ ∙-cong (f.homo x₁ x₂) (g.homo y₁ y₂) ⟩
            (f.⟦ x₁ ⟧ ∙ f.⟦ x₂ ⟧) ∙ (g.⟦ y₁ ⟧ ∙ g.⟦ y₂ ⟧) ≈⟨ assoc _ _ _ ⟩
            f.⟦ x₁ ⟧ ∙ (f.⟦ x₂ ⟧ ∙ (g.⟦ y₁ ⟧ ∙ g.⟦ y₂ ⟧)) ≈⟨ ∙-congˡ (assoc _ _ _) ⟨
            f.⟦ x₁ ⟧ ∙ ((f.⟦ x₂ ⟧ ∙ g.⟦ y₁ ⟧) ∙ g.⟦ y₂ ⟧) ≈⟨ ∙-congˡ (∙-congʳ (comm _ _))  ⟩
            f.⟦ x₁ ⟧ ∙ ((g.⟦ y₁ ⟧ ∙ f.⟦ x₂ ⟧) ∙ g.⟦ y₂ ⟧) ≈⟨ ∙-congˡ (assoc _ _ _) ⟩
            f.⟦ x₁ ⟧ ∙ (g.⟦ y₁ ⟧ ∙ (f.⟦ x₂ ⟧ ∙ g.⟦ y₂ ⟧)) ≈⟨ assoc _ _ _ ⟨
            f.⟦ x₁ ⟧ ∙ g.⟦ y₁ ⟧ ∙ (f.⟦ x₂ ⟧ ∙ g.⟦ y₂ ⟧)   ∎
          where
            open ≈-Reasoning setoid

module _ {A B C D : CommutativeMonoid c ℓ} where

  _⊕₁_
      : CommutativeMonoidHomomorphism A B
      → CommutativeMonoidHomomorphism C D
      → CommutativeMonoidHomomorphism (A ⊕ C) (B ⊕ D)
  _⊕₁_ f g = [ i₁ ∘ f , i₂ ∘ g ]

  infixr 8 _⊕₁_
