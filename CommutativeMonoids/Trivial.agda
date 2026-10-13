{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module CommutativeMonoids.Trivial (c ℓ : Level) where

open import Algebra using (CommutativeMonoid)
open import Data.Unit.Polymorphic using (⊤)

⊤ₘ : CommutativeMonoid c ℓ
⊤ₘ = record
    { Carrier = ⊤
    ; _≈_ = λ _ _ → ⊤
    }
