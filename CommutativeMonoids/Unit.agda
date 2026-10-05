{-# OPTIONS --without-K --safe #-}

open import Level using (Level; Lift; lift; _⊔_)

module CommutativeMonoids.Unit {c ℓ : Level} where

import Algebra.Properties.CommutativeMonoid.Mult as Mult
import CommutativeMonoids.Coequalizer {c} {c ⊔ ℓ} as Coeq
import CommutativeMonoids.TensorProduct as ⊗
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Algebra using (CommutativeMonoid)
open import Algebra.Construct.DirectProduct using () renaming (commutativeMonoid to _⊕_)
open import CommutativeMonoids.Category using (CommutativeMonoids; CommutativeMonoidHomomorphism; mk-⇒)
open import CommutativeMonoids.FreeForget.Adjunction c ℓ using (singleton; sum)
open import CommutativeMonoids.FreeForget.Forget c (c ⊔ ℓ) using () renaming (Underlying to U)
open import Data.List using (List; [_]; map)
open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ; +-comm)
open import Data.Product using (_,_)
open import Function using (_⟶ₛ_; Func)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open List
open Func

ℕₘ : CommutativeMonoid c (c ⊔ ℓ)
ℕₘ = record
    { Carrier = Lift c ℕ
    ; _≈_ = λ (lift x) (lift y) → Lift (c ⊔ ℓ) (x ≡ y)
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

module _ {M : CommutativeMonoid c (c ⊔ ℓ)} where

  open ⊗ {c} {ℓ} ℕₘ M using (f; g; u!; fₘ; gₘ; I) renaming (M⊗N to ℕₘ⊗M)

  open Coeq fₘ gₘ using (_≋_; ≋-setoid; ≡-fwd; ≡-bwd; ≋-refl; ∙-resp-≋)
  open CommutativeMonoid M
  open I
  open Mult M using (_×_; ×-cong; ×-homo-0; ×-homo-+; ×-distrib-+; ×-idem)
  open _≋_
  open ℕ
  open ≈-Reasoning ≋-setoid

  private
    module ℕₘ⊗M = CommutativeMonoid ℕₘ⊗M
    module CMon = CommutativeMonoids

  open CMon using (_∘_; id)

  pattern 0× a = lift 0 , a
  pattern 1× a = lift 1 , a

  ×ₛ : U (ℕₘ ⊕ M) ⟶ₛ U M
  ×ₛ = record
      { to = λ (lift n , a) → n × a
      ; cong = λ (lift ≡n , ≈a) → ×-cong ≡n ≈a
      }


  ×-ε : (n : ℕ) → n × ε ≈ ε
  ×-ε zero = refl
  ×-ε (suc n) = trans (identityˡ (n × ε)) (×-ε n)

  λ⇒ : CommutativeMonoidHomomorphism ℕₘ⊗M M
  λ⇒ =
      u!
        M
        ×ₛ
        (λ {a} → ×-homo-0 a)
        (λ { {lift n} → ×-ε n })
        (λ { {lift n} {lift m} {a} → sym (×-homo-+ a n m) })
        (λ { {lift n} {a} {b} → sym (×-distrib-+ a b n) })

  λ⇐ : CommutativeMonoidHomomorphism M ℕₘ⊗M
  λ⇐ = mk-⇒ record
      { ⟦_⟧ = λ x → [ 1× x ]
      ; isMonoidHomomorphism = record
          { isMagmaHomomorphism = record
              { isRelHomomorphism = record
                  { cong = λ x≈y → base (cong (singleton (U (ℕₘ ⊕ M))) (lift ≡.refl , x≈y))
                  }
              ; homo = λ x y → ≡-bwd [] [ ∙ʳ (lift 1) x y ]
              }
          ; ε-homo = ≡-fwd [] [ εʳ (lift 1) ]
          }
      }

  ≋-n×a : (n : ℕ) (a : Carrier) → [ 1× (n × a) ] ≋ [ lift n , a ]
  ≋-n×a zero a = begin
      [ 1× (0 × a) ]  ≈⟨ ≡-fwd [] [ εʳ (lift 1) ] ⟩
      []              ≈⟨ ≡-bwd [] [ εˡ a ] ⟩
      [ 0× a ]        ∎
  ≋-n×a (suc n) a = begin
      [ 1× (a ∙ n × a) ]    ≈⟨ ≡-bwd [] [ ∙ʳ (lift 1) a (n × a) ] ⟩
      1× a ∷ [ 1× (n × a) ] ≈⟨ ∙-resp-≋ (≋-refl {[ 1× a ]}) (≋-n×a n a) ⟩
      1× a ∷ [ lift n , a ] ≈⟨ ≡-fwd [] [ ∙ˡ (lift 1) (lift n) a ] ⟩
      [ lift (suc n) , a ]  ∎

  λ⇐∘λ⇒ : λ⇐ ∘ λ⇒ CMon.≈ id
  λ⇐∘λ⇒ [] = ≡-fwd [] [ εʳ (lift 1) ]
  λ⇐∘λ⇒ ((lift n , a) ∷ xs) = begin
      [ 1× (n × a ∙ sum M (map (to ×ₛ) xs)) ]       ≈⟨ ≡-bwd [] [ ∙ʳ (lift 1) (n × a) (sum M (map (to ×ₛ) xs)) ] ⟩
      1× (n × a) ∷ [ 1× (sum M (map (to ×ₛ) xs)) ]  ≈⟨ ∙-resp-≋ (≋-n×a n a) (λ⇐∘λ⇒ xs) ⟩
      (lift n , a) ∷ xs                             ∎

  λ⇒∘λ⇐ : λ⇒ ∘ λ⇐ CMon.≈ id
  λ⇒∘λ⇐ xs = trans (identityʳ (xs ∙ ε)) (identityʳ xs)
