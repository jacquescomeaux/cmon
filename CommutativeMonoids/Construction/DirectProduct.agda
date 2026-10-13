{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module CommutativeMonoids.Construction.DirectProduct (c ℓ : Level) where

open import Algebra using (CommutativeMonoid)
open import Algebra.Construct.DirectProduct using (commutativeMonoid)

-- Direct product of commutative monoids
_×_ : CommutativeMonoid c ℓ → CommutativeMonoid c ℓ → CommutativeMonoid c ℓ
_×_ = commutativeMonoid

infixr 7 _×_
