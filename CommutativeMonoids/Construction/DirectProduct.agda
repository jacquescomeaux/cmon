{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module CommutativeMonoids.Construction.DirectProduct (c ℓ : Level) where

open import Algebra using (CommutativeMonoid)
open import Algebra.Construct.DirectProduct
  using ()
  renaming (commutativeMonoid to infixr 7 _×_)
  public

-- Also provide ⊕ notation to emphasize role as biproduct
_⊕_ : CommutativeMonoid c ℓ → CommutativeMonoid c ℓ → CommutativeMonoid c ℓ
_⊕_ M N = M × N

infixr 7 _⊕_
