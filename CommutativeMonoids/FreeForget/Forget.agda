{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module CommutativeMonoids.FreeForget.Forget (c ℓ : Level) where

open import Algebra using (CommutativeMonoid)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor)
open import CommutativeMonoids.Category using (CommutativeMonoids; CommutativeMonoidHomomorphism)
open import Function using (_⟶ₛ_)
open import Relation.Binary using (Setoid)

open CommutativeMonoidHomomorphism using (func)

Underlying : CommutativeMonoid c ℓ → Setoid c ℓ
Underlying = CommutativeMonoid.setoid

Forget : Functor (CommutativeMonoids c ℓ) (Setoids c ℓ)
Forget = record
    { F₀ = Underlying
    ; F₁ = func
    ; identity = λ {A} → refl A
    ; homomorphism = λ {Z = Z} → refl Z
    ; F-resp-≈ = λ f≈g {x} → f≈g x
    }
  where
    open CommutativeMonoid using (refl)

module Forget = Functor Forget
