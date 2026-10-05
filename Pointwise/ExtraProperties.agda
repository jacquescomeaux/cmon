{-# OPTIONS --without-K --safe #-}

module Pointwise.ExtraProperties where

import Data.List.Relation.Binary.Equality.Setoid as ≋
import Function.Relation.Binary.Setoid.Equality as ≈ₛ

open import Data.List using (List; map)
open import Data.List.Relation.Binary.Pointwise as PW using (Pointwise; map⁺)
open import Function using (_⟶ₛ_; Func)
open import Level using (Level)
open import Relation.Binary using (Setoid)

module _ {c c′ ℓ ℓ′ : Level} {A : Setoid c ℓ} {B : Setoid c′ ℓ′} (f g : A ⟶ₛ B) where

  open Func
  open List
  open Pointwise
  open Setoid A using (Carrier)
  open Setoid B using (trans)
  open ≈ₛ A B using (_≈_)
  open ≋ A using (≋-refl)
  open ≋ B using (_≋_)

  map-cong : f ≈ g → (xs : List Carrier) → map (to f) xs ≋ map (to g) xs
  map-cong f≈g xs = map⁺ (to f) (to g) (PW.map (λ {a} a≈b → trans (f≈g a) (cong g a≈b)) ≋-refl)
