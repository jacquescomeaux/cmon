{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --hidden-argument-puns #-}

open import Level using (Level; suc; _⊔_)

module Setoids.Coequalizer (c ℓ : Level) where

import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Diagram.Coequalizer (Setoids c (c ⊔ ℓ)) using (Coequalizer)
open import Function using (id; _⟶ₛ_; Func; _⟨$⟩_)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)

open Func

module _ {A B : Setoid c (c ⊔ ℓ)} (f g : A ⟶ₛ B) where

  private

    module A = Setoid A
    module B = Setoid B

    variable
      a b : A.Carrier
      v w x y z : B.Carrier

  data _≋_ : Rel B.Carrier (c ⊔ ℓ) where
    refl : x B.≈ y → x ≋ y
    fwd  : x B.≈ f ⟨$⟩ a → g ⟨$⟩ a B.≈ y → y ≋ z → x ≋ z
    bwd  : x B.≈ g ⟨$⟩ a → f ⟨$⟩ a B.≈ y → y ≋ z → x ≋ z

  infix 4 _≋_

  ≋-refl : x ≋ x
  ≋-refl {x} = refl (B.refl {x})

  ≈-≋ : x B.≈ y → y ≋ z → x ≋ z
  ≈-≋ x≈y (refl y≈z) = refl (B.trans x≈y y≈z)
  ≈-≋ x≈y (fwd y≈fa ga≈w w≋z) = fwd (B.trans x≈y y≈fa) ga≈w w≋z
  ≈-≋ x≈y (bwd y≈ga fa≈w w≋z) = bwd (B.trans x≈y y≈ga) fa≈w w≋z

  ≋-euclidean : y ≋ x → y ≋ z → x ≋ z
  ≋-euclidean (refl y≈x) y≋z = ≈-≋ (B.sym y≈x) y≋z
  ≋-euclidean (fwd y≈fa ga≈w w≋x) y≋z = ≋-euclidean w≋x (bwd (B.sym ga≈w) (B.sym y≈fa) y≋z)
  ≋-euclidean (bwd y≈ga fa≈w w≋x) y≋z = ≋-euclidean w≋x (fwd (B.sym fa≈w) (B.sym y≈ga) y≋z)

  ≋-sym : x ≋ y → y ≋ x
  ≋-sym x≋y = ≋-euclidean x≋y ≋-refl

  ≋-trans : x ≋ y → y ≋ z → x ≋ z
  ≋-trans x≋y = ≋-euclidean (≋-sym x≋y)

  ≋-isEquiv : IsEquivalence _≋_
  ≋-isEquiv = record
      { refl = ≋-refl
      ; sym = ≋-sym
      ; trans = ≋-trans
      }

  C : Setoid c (c ⊔ ℓ)
  C = record { isEquivalence = ≋-isEquiv }

  -- The universal coequalizing arrow
  h : B ⟶ₛ C
  h = record { cong = refl }

  -- The universal arrow coequalizes f and g
  coequalizes : h ⟨$⟩ (f ⟨$⟩ a) ≋ h ⟨$⟩ (g ⟨$⟩ a)
  coequalizes = fwd B.refl B.refl ≋-refl

  module _ {X : Setoid c (c ⊔ ℓ)} {k : B ⟶ₛ X} where

    private
      module X = Setoid X

    module _ (eq : {a : A.Carrier} → k ⟨$⟩ (f ⟨$⟩ a) X.≈ k ⟨$⟩ (g ⟨$⟩ a)) where

      open ≈-Reasoning X

      u-cong : x ≋ y → k ⟨$⟩ x X.≈ k ⟨$⟩ y
      u-cong (refl x≈y) = cong k x≈y
      u-cong {y} (fwd {x} {a} {y = z} x≈fa ga≈z z≋y) = begin
          k ⟨$⟩ x         ≈⟨ cong k x≈fa ⟩
          k ⟨$⟩ (f ⟨$⟩ a) ≈⟨ eq ⟩
          k ⟨$⟩ (g ⟨$⟩ a) ≈⟨ cong k ga≈z ⟩
          k ⟨$⟩ z         ≈⟨ u-cong z≋y ⟩
          k ⟨$⟩ y         ∎
      u-cong {y} (bwd {x} {a} {y = z} x≈ga fa≈z z≋y) = begin
          k ⟨$⟩ x         ≈⟨ cong k x≈ga ⟩
          k ⟨$⟩ (g ⟨$⟩ a) ≈⟨ eq ⟨
          k ⟨$⟩ (f ⟨$⟩ a) ≈⟨ cong k fa≈z ⟩
          k ⟨$⟩ z         ≈⟨ u-cong z≋y ⟩
          k ⟨$⟩ y         ∎

      -- The induced factorizing arrow
      u : C ⟶ₛ X
      u = record
          { to = to k
          ; cong = u-cong
          }

      -- Any other coequalizing arrow factors through the coequalizer via the induced arrow
      universal : k ⟨$⟩ x X.≈ u ⟨$⟩ (h ⟨$⟩ x)
      universal = X.refl

    module _ {i : C ⟶ₛ X} (eq : {a : A.Carrier} → k ⟨$⟩ (f ⟨$⟩ a) X.≈ k ⟨$⟩ (g ⟨$⟩ a)) where

      -- The induced arrow is unique
      unique : k ⟨$⟩ x X.≈ i ⟨$⟩ (h ⟨$⟩ x) → i ⟨$⟩ x X.≈ u eq ⟨$⟩ x
      unique = X.sym

  coequalizer : Coequalizer f g
  coequalizer = record
      { obj = C
      ; arr = h
      ; isCoequalizer = record
          { equality = coequalizes
          ; coequalize = λ {X k} eq → u {X} {k} eq
          ; universal = λ {X k eq} → universal {X} {k} eq
          ; unique = λ {X k i eq} k≈i∘h → unique {X} {k} {i} eq k≈i∘h
          }
      }
