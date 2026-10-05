{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)

module CommutativeMonoids.FormalSum (c ℓ : Level) where

open import Algebra using (CommutativeMonoid)
open import Categories.Adjoint.Properties using (adjoint⇒comonad)
open import Categories.Comonad using (Comonad)
open import CommutativeMonoids.Category using (CommutativeMonoids; CommutativeMonoidHomomorphism)
open import CommutativeMonoids.FreeForget.Adjunction c ℓ using (Free⊣Forget)

-- The "formal sum" comonad
FormalSum : Comonad (CommutativeMonoids c (c ⊔ ℓ))
FormalSum = adjoint⇒comonad Free⊣Forget

module FormalSum = Comonad FormalSum

⅀ : CommutativeMonoid c (c ⊔ ℓ) → CommutativeMonoid c (c ⊔ ℓ)
⅀ = FormalSum.F.₀

module _ (M : CommutativeMonoid c (c ⊔ ℓ)) where

  evalₘ : CommutativeMonoidHomomorphism (⅀ M) M
  evalₘ = FormalSum.ε.η M

  comultₘ : CommutativeMonoidHomomorphism (⅀ M) (⅀ (⅀ M))
  comultₘ = FormalSum.δ.η M
