{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)

module CommutativeMonoids.TensorProduct.Bifunctor {c ℓ : Level} where

open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import CommutativeMonoids.Category using (CommutativeMonoidHomomorphism) renaming (CommutativeMonoids to CMon)
open import CommutativeMonoids.TensorProduct {c} {ℓ} using () renaming (M⊗N to infixr 10 _⊗₀_) public
open import CommutativeMonoids.TensorProduct.Morphism {c} {ℓ} using () renaming (f⊗g to infixr 10 _⊗₁_) public
open import CommutativeMonoids.TensorProduct.Morphism.Properties {c} {ℓ} using (⊗₁-resp-id; ⊗₁-resp-∘; ⊗₁-resp-≈)
open import Data.Product using (uncurry′; _,_)

-⊗- : Bifunctor (CMon c (c ⊔ ℓ)) (CMon c (c ⊔ ℓ)) (CMon c (c ⊔ ℓ))
-⊗- = record
    { F₀ = uncurry′ _⊗₀_
    ; F₁ = uncurry′ _⊗₁_
    ; identity = ⊗₁-resp-id
    ; homomorphism = λ { {f = f , f′} {g , g′} → ⊗₁-resp-∘ {f = g} {f} {g′} {f′} }
    ; F-resp-≈ = λ { {f = f , f′} {g , g′} (f≈g , h≈k) → ⊗₁-resp-≈ {f = f} {g} {f′} {g′} f≈g h≈k }
    }

module -⊗- = Functor -⊗-
