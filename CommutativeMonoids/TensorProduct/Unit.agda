{-# OPTIONS --without-K --safe #-}

open import Level using (Level; Lift; lift)

module CommutativeMonoids.TensorProduct.Unit (c ℓ : Level) where

open import Algebra using (CommutativeMonoid)
open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ; +-comm)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

ℕₘ : CommutativeMonoid c ℓ
ℕₘ = record
    { Carrier = Lift c ℕ
    ; _≈_ = λ (lift x) (lift y) → Lift ℓ (x ≡ y)
    ; _∙_ = λ (lift x) (lift y) → lift (x + y)
    ; ε = lift 0
    ; isCommutativeMonoid = record
        { isMonoid = record
            { isSemigroup = record
                { isMagma = record
                    { isEquivalence = record
                        { refl = lift ≡.refl
                        ; sym = λ (lift x≡y) → lift (≡.sym x≡y)
                        ; trans = λ (lift x≡y) (lift y≡z) → lift (≡.trans x≡y y≡z)
                        }
                    ; ∙-cong = λ (lift ≡x) (lift ≡y) → lift (≡.cong₂ _+_ ≡x ≡y)
                    }
                ; assoc = λ (lift x) (lift y) (lift z) → lift (+-assoc x y z)
                }
            ; identity = (λ (lift x) → lift (+-identityˡ x)) , (λ (lift x) → lift (+-identityʳ x))
            }
        ; comm = λ (lift x) (lift y) → lift (+-comm x y)
        }
    }
