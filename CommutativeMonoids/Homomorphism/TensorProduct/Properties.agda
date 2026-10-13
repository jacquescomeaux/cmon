{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)

module CommutativeMonoids.Homomorphism.TensorProduct.Properties {c ℓ : Level} where

import CommutativeMonoids.Construction.TensorProduct {c} {ℓ} as ⊗
import CommutativeMonoids.Homomorphism.TensorProduct {c} {ℓ} as ⊗-⇒

open import Algebra using (CommutativeMonoid)
open import CommutativeMonoids.Category using (CommutativeMonoids; CommutativeMonoidHomomorphism)
open import CommutativeMonoids.Construction.FormalSum c ℓ using (FormalSum)
open import CommutativeMonoids.Homomorphism.TensorProduct {c} {ℓ} using () renaming (f⊗g to infixr 10 _⊗₁_)
open import Data.List.Properties using (map-∘; map-cong; map-id)
open import Data.Product using (dmap)

open CommutativeMonoids {c} {c ⊔ ℓ} using (_∘_; id; _≈_; ∘-resp-≈ʳ)
open ⊗ using () renaming (M⊗N to infixr 10 _⊗₀_)

⊗₁-resp-∘
    : {A B C D E F : CommutativeMonoid c (c ⊔ ℓ)}
      {f : CommutativeMonoidHomomorphism B C}
      {g : CommutativeMonoidHomomorphism A B}
      {h : CommutativeMonoidHomomorphism E F}
      {k : CommutativeMonoidHomomorphism D E}
    → (f ∘ g) ⊗₁ (h ∘ k) ≈ f ⊗₁ h ∘ g ⊗₁ k
⊗₁-resp-∘ {B = B} {C} {E = E} {F} {f} {g} {h} {k} x = C⊗F.reflexive (map-∘ x)
  where
    open ⊗ C F using () renaming (M⊗N to C⊗F)
    module C⊗F = CommutativeMonoid C⊗F

⊗₁-resp-id
    : {M N : CommutativeMonoid c (c ⊔ ℓ)}
    → id {M} ⊗₁ id {N} ≈ id {M ⊗₀ N}
⊗₁-resp-id {M} {N} x = M⊗N.reflexive (map-id x)
  where
    open ⊗ M N using (M⊗N)
    module M⊗N = CommutativeMonoid M⊗N

⊗₁-resp-≈
    : {A B C D : CommutativeMonoid c (c ⊔ ℓ)}
      {f h : CommutativeMonoidHomomorphism A B}
      {g k : CommutativeMonoidHomomorphism C D}
    → f ≈ h
    → g ≈ k
    → f ⊗₁ g ≈ h ⊗₁ k
⊗₁-resp-≈ {A} {B} {C} {D} {f} {h} {g} {k} f≈h g≈k =
    ∘-resp-≈ʳ
      {f = FormalSum.F.₁ f×ₘg}
      {FormalSum.F.₁ h×ₘk}
      {eval}
      (FormalSum.F.F-resp-≈ {f = f×ₘg} {h×ₘk} f×ₘg≈h×ₘk)
  where
    open ⊗ B D using (eval)
    open ⊗-⇒ f g using (f×ₘg)
    open ⊗-⇒ h k using () renaming (f×ₘg to h×ₘk)
    f×ₘg≈h×ₘk : f×ₘg ≈ h×ₘk
    f×ₘg≈h×ₘk = dmap f≈h g≈k
