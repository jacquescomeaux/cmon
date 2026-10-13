{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module CommutativeMonoids.Construction.DirectSum (c ℓ : Level) where

open import Algebra using (CommutativeMonoid)
open import CommutativeMonoids.Construction.DirectProduct c ℓ using (_×_)

-- The direct sum and direct product of commutative monoids are the same
_⊕_ : CommutativeMonoid c ℓ → CommutativeMonoid c ℓ → CommutativeMonoid c ℓ
_⊕_ = _×_

infixr 7 _⊕_
