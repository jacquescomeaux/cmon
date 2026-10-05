{-# OPTIONS --without-K --safe #-}

module Permutation.ExtraProperties where

import Data.List.Relation.Binary.Permutation.Algorithmic as ↭

open import Data.List using (List; map)
open import Data.List.Relation.Binary.Permutation.Algorithmic.Properties using (↭ₛ⇒↭; ↭⇒↭ₛ)
open import Data.List.Relation.Binary.Permutation.Setoid.Properties using (map⁺)
open import Function using (_⟶ₛ_; Func; _∘_)
open import Level using (Level)
open import Relation.Binary using (Setoid)

module _ {c c′ ℓ ℓ′ : Level} {S : Setoid c ℓ} {T : Setoid c′ ℓ′} where

  open ↭ S using () renaming (_↭_ to _↭S_)
  open ↭ T using () renaming (_↭_ to _↭T_)

  open Func

  private
    module S = Setoid S

  map-↭
      : {x y : List S.Carrier}
      → (f : S ⟶ₛ T)
      → x ↭S y
      → map (to f) x ↭T map (to f) y
  map-↭ f = ↭ₛ⇒↭ T ∘ map⁺ S T (cong f) ∘ ↭⇒↭ₛ S
