{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)

module CommutativeMonoids.FreeForget.Free (c ℓ : Level) where

import Data.List.Relation.Binary.Equality.Setoid as ≋
import Data.List.Relation.Binary.Permutation.Algorithmic as Permutation
import Data.List.Relation.Binary.Permutation.Algorithmic.Properties as ↭-Properties
import Function.Relation.Binary.Setoid.Equality as ≈ₛ

open import Algebra using (IsCommutativeMonoid; CommutativeMonoid)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor)
open import CommutativeMonoids.Category using (CommutativeMonoids; CommutativeMonoidHomomorphism; mk-⇒)
open import Data.List using (List; _++_; map)
open import Data.List.Properties using (++-assoc; map-++; map-id; map-∘)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
open import Data.Product using (_,_)
open import Function using (_⟶ₛ_; Func)
open import Pointwise.ExtraProperties using (map-cong)
open import Relation.Binary using (Setoid)

open Func
open List
open Pointwise

module _ (A : Setoid c ℓ) where

  open Permutation A using (_↭_; ↭-reflexive; ↭-refl; ↭-sym; ↭-trans)
  open Setoid A
  open ↭-Properties A using (↭-swap-++; ↭-cong)
  open ≋ A using (≋-reflexive)

  ↭-isCM : IsCommutativeMonoid _↭_ _++_ []
  ↭-isCM = record
      { isMonoid = record
          { isSemigroup = record
              { isMagma = record
                  { isEquivalence = record
                      { refl = λ {x} → ↭-refl x
                      ; sym = ↭-sym
                      ; trans = ↭-trans
                      }
                  ; ∙-cong = ↭-cong
                  }
              ; assoc = λ x y z → ↭-reflexive (≋-reflexive (++-assoc x y z))
              }
          ; identity = ↭-refl , λ x → ↭-swap-++ x []
          }
      ; comm = ↭-swap-++
      }

  FreeCommutativeMonoid : CommutativeMonoid c (c ⊔ ℓ)
  FreeCommutativeMonoid = record
      { Carrier = List Carrier
      ; _≈_ = _↭_
      ; _∙_ = _++_
      ; ε = []
      ; isCommutativeMonoid = ↭-isCM
      }

module _ {A B : Setoid c ℓ} where

  open Permutation B using (↭-refl; ↭-reflexive)
  open ≋ B using (≋-reflexive)

  open import Permutation.ExtraProperties using (map-↭)
  mapₘ : A ⟶ₛ B → CommutativeMonoidHomomorphism (FreeCommutativeMonoid A) (FreeCommutativeMonoid B)
  mapₘ f = mk-⇒ record
      { ⟦_⟧ = map (to f)
      ; isMonoidHomomorphism = record
          { isMagmaHomomorphism = record
              { isRelHomomorphism = record
                  { cong = map-↭ f
                  }
              ; homo = λ x y → ↭-reflexive (≋-reflexive (map-++ (to f) x y))
              }
          ; ε-homo = ↭-refl []
          }
      }

Free : Functor (Setoids c ℓ) (CommutativeMonoids c (c ⊔ ℓ))
Free = record
    { F₀ = FreeCommutativeMonoid
    ; F₁ = mapₘ
    ; identity = λ {A} x → ↭-reflexive A (≋-reflexive A (map-id x))
    ; homomorphism = λ {A B C} x → ↭-reflexive C (≋-reflexive C (map-∘ x))
    ; F-resp-≈ = λ {A B f g} f≈g x → ↭-reflexive B (map-cong f g (λ x → f≈g {x}) x)
    }
  where
    open Permutation using (↭-reflexive)
    open ≋ using (≋-reflexive; map⁺)

module Free = Functor Free
