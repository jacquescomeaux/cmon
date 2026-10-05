{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)

module Setoids.Multiset (c ℓ : Level) where

open import Categories.Adjoint.Properties using (adjoint⇒monad)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Monad using (Monad)
open import CommutativeMonoids.FreeForget.Adjunction using (Free⊣Forget)
open import Function using (_⟶ₛ_)
open import Relation.Binary using (Setoid)

open Setoid using (Carrier)

-- The multiset monad
Multiset : Monad (Setoids c (c ⊔ ℓ))
Multiset = adjoint⇒monad (Free⊣Forget c ℓ)

module Multiset = Monad Multiset

MSet : Setoid c (c ⊔ ℓ) → Setoid c (c ⊔ ℓ)
MSet = Multiset.F.₀

module _ {A : Setoid c (c ⊔ ℓ)} where

  pureₛ : A ⟶ₛ MSet A
  pureₛ = Multiset.η.η A

  joinₛ : MSet (MSet A) ⟶ₛ MSet A
  joinₛ = Multiset.μ.η A
