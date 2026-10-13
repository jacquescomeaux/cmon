{-# OPTIONS --without-K --safe #-}

open import Level using (Level; Lift; lift; _⊔_)

module CommutativeMonoids.Homomorphism.Unitors {c ℓ : Level} where

import Algebra.Properties.CommutativeMonoid.Mult as Mult
import CommutativeMonoids.Category.Coequalizer.FromFree {c} {ℓ} as Coeq
import CommutativeMonoids.Congruence {c} {c ⊔ ℓ} as Cong
import CommutativeMonoids.Construction.CongruenceClosure {c} {ℓ} as CongruenceClosure
import CommutativeMonoids.Construction.TensorProduct {c} {ℓ} as ⊗
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Algebra using (CommutativeMonoid)
open import Algebra.Construct.DirectProduct using () renaming (commutativeMonoid to _⊕_)
open import CommutativeMonoids.Category using (CommutativeMonoids; CommutativeMonoidHomomorphism; mk-⇒)
open import CommutativeMonoids.Construction.FormalSum c (c ⊔ ℓ) using (⅀)
open import CommutativeMonoids.FreeForget.Adjunction c ℓ using (singleton; sum)
open import CommutativeMonoids.FreeForget.Forget c (c ⊔ ℓ) using () renaming (Underlying to U)
open import CommutativeMonoids.TensorProduct.Unit c (c ⊔ ℓ) using (ℕₘ)
open import Data.List using (List; [_]; map)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_,_)
open import Data.Product.Function.NonDependent.Setoid using (swapₛ)
open import Function using (_⟶ₛ_; Func)
open import Function.Construct.Setoid using () renaming (_∙_ to _⊚_)

open List
open Func

private
  module ℕₘ = CommutativeMonoid ℕₘ

module _ {M : CommutativeMonoid c (c ⊔ ℓ)} where

  open CommutativeMonoid M
  open Mult M using (_×_; ×-cong; ×-homo-0; ×-homo-+; ×-distrib-+; ×-idem)
  open ℕ

  ×-ε : (n : ℕ) → n × ε ≈ ε
  ×-ε zero = refl
  ×-ε (suc n) = trans (identityˡ (n × ε)) (×-ε n)

  module LeftUnitor where

    open ⊗ ℕₘ M using (f; g; fₘ; gₘ; I; Iₛ; eval; module Universal′) renaming (M⊗N to ℕₘ⊗M)
    open Coeq {Iₛ} {⅀ (ℕₘ ⊕ M)} f g using (_~_)
    open Cong (⅀ (ℕₘ ⊕ M)) using (Congruence)
    open CongruenceClosure (⅀ (ℕₘ ⊕ M)) _~_ using (_≋_; ≋-congˡ; ≋-congruence; step-fwd; step-bwd)
    open Congruence ≋-congruence using () renaming (cong to ≋-cong)
    open _~_
    open I

    open CommutativeMonoidHomomorphism using (⟦⟧-cong)

    private
      module ℕₘ⊗M = CommutativeMonoid ℕₘ⊗M
      module CMon = CommutativeMonoids

    open CMon using (_∘_; id)

    open ≈-Reasoning ℕₘ⊗M.setoid

    pattern 0× a = lift 0 , a
    pattern 1× a = lift 1 , a

    ×ₛ : U (ℕₘ ⊕ M) ⟶ₛ U M
    ×ₛ = record
        { to = λ (lift n , a) → n × a
        ; cong = λ (lift ≡n , ≈a) → ×-cong ≡n ≈a
        }

    λ⇒ : CommutativeMonoidHomomorphism ℕₘ⊗M M
    λ⇒ =
        Universal′.u!
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
                    { cong = λ x≈y → ⟦⟧-cong eval (cong (singleton (U (ℕₘ ⊕ M))) (ℕₘ.refl , x≈y))
                    }
                ; homo = λ x y → step-bwd (f~g (∙ʳ (lift 1) x y))
                }
            ; ε-homo = step-fwd (f~g (εʳ (lift 1)))
            }
        }

    ≋-n×a : (n : ℕ) (a : Carrier) → [ 1× (n × a) ] ≋ [ lift n , a ]
    ≋-n×a zero a = begin
        [ 1× (0 × a) ]  ≈⟨ step-fwd (f~g (εʳ (lift 1))) ⟩
        []              ≈⟨ step-bwd (f~g (εˡ a)) ⟩
        [ 0× a ]        ∎
    ≋-n×a (suc n) a = begin
        [ 1× (a ∙ n × a) ]    ≈⟨ step-bwd (f~g (∙ʳ (lift 1) a (n × a))) ⟩
        1× a ∷ [ 1× (n × a) ] ≈⟨ ≋-congˡ {z = [ 1× a ]} (≋-n×a n a) ⟩
        1× a ∷ [ lift n , a ] ≈⟨ step-fwd (f~g (∙ˡ (lift 1) (lift n) a)) ⟩
        [ lift (suc n) , a ]  ∎

    λ⇐∘λ⇒ : λ⇐ ∘ λ⇒ CMon.≈ id
    λ⇐∘λ⇒ [] = step-fwd (f~g (εʳ (lift 1)))
    λ⇐∘λ⇒ ((lift n , a) ∷ xs) = begin
        [ 1× (n × a ∙ sum M (map (to ×ₛ) xs)) ]       ≈⟨ step-bwd (f~g (∙ʳ (lift 1) (n × a) (sum M (map (to ×ₛ) xs)))) ⟩
        1× (n × a) ∷ [ 1× (sum M (map (to ×ₛ) xs)) ]  ≈⟨ ≋-cong (≋-n×a n a) (λ⇐∘λ⇒ xs) ⟩
        (lift n , a) ∷ xs                             ∎

    λ⇒∘λ⇐ : λ⇒ ∘ λ⇐ CMon.≈ id
    λ⇒∘λ⇐ xs = trans (identityʳ (xs ∙ ε)) (identityʳ xs)

  module RightUnitor where

    open ⊗ M ℕₘ using (f; g; fₘ; gₘ; I; Iₛ; eval; module Universal′) renaming (M⊗N to M⊗ℕₘ)
    open Coeq {Iₛ} {⅀ (M ⊕ ℕₘ)} f g using (_~_)
    open Cong (⅀ (M ⊕ ℕₘ)) using (Congruence)
    open CongruenceClosure (⅀ (M ⊕ ℕₘ)) _~_ using (_≋_; ≋-congˡ; ≋-congruence; step-fwd; step-bwd)
    open Congruence ≋-congruence using () renaming (cong to ≋-cong)
    open _~_
    open I

    open CommutativeMonoidHomomorphism using (⟦⟧-cong)
    open ℕ

    private
      module M⊗ℕₘ = CommutativeMonoid M⊗ℕₘ
      module CMon = CommutativeMonoids

    open CMon using (_∘_; id)

    open ≈-Reasoning M⊗ℕₘ.setoid

    pattern 0× a = a , lift 0
    pattern 1× a = a , lift 1

    ×ₛ : U (M ⊕ ℕₘ) ⟶ₛ U M
    ×ₛ = LeftUnitor.×ₛ ⊚ swapₛ

    ρ⇒ : CommutativeMonoidHomomorphism M⊗ℕₘ M
    ρ⇒ =
        Universal′.u!
          ×ₛ
          (λ { {lift n} → ×-ε n })
          (λ {a} → ×-homo-0 a)
          (λ { {a} {b} {lift n} → sym (×-distrib-+ a b n) })
          (λ { {a} {lift n} {lift m} → sym (×-homo-+ a n m) })

    ρ⇐ : CommutativeMonoidHomomorphism M M⊗ℕₘ
    ρ⇐ = mk-⇒ record
        { ⟦_⟧ = λ x → [ 1× x ]
        ; isMonoidHomomorphism = record
            { isMagmaHomomorphism = record
                { isRelHomomorphism = record
                    { cong = λ x≈y → ⟦⟧-cong eval (cong (singleton (U (M ⊕ ℕₘ))) (x≈y , ℕₘ.refl))
                    }
                ; homo = λ x y → step-bwd (f~g (∙ˡ x y (lift 1)))
                }
            ; ε-homo = step-fwd (f~g (εˡ (lift 1)))
            }
        }

    ≋-n×a : (n : ℕ) (a : Carrier) → [ 1× (n × a) ] ≋ [ a , lift n ]
    ≋-n×a zero a = begin
        [ 1× (0 × a) ]  ≈⟨ step-fwd (f~g (εˡ (lift 1))) ⟩
        []              ≈⟨ step-bwd (f~g (εʳ a)) ⟩
        [ 0× a ]        ∎
    ≋-n×a (suc n) a = begin
        [ 1× (a ∙ n × a) ]    ≈⟨ step-bwd (f~g (∙ˡ a (n × a) (lift 1))) ⟩
        1× a ∷ [ 1× (n × a) ] ≈⟨ ≋-congˡ {z = [ 1× a ]} (≋-n×a n a) ⟩
        1× a ∷ [ a , lift n ] ≈⟨ step-fwd (f~g (∙ʳ a (lift 1) (lift n))) ⟩
        [ a , lift (suc n) ]  ∎

    ρ⇐∘ρ⇒ : ρ⇐ ∘ ρ⇒ CMon.≈ id
    ρ⇐∘ρ⇒ [] = step-fwd (f~g (εˡ (lift 1)))
    ρ⇐∘ρ⇒ ((a , lift n) ∷ xs) = begin
        [ 1× (n × a ∙ sum M (map (to ×ₛ) xs)) ]       ≈⟨ step-bwd (f~g (∙ˡ (n × a) (sum M (map (to ×ₛ) xs)) (lift 1))) ⟩
        1× (n × a) ∷ [ 1× (sum M (map (to ×ₛ) xs)) ]  ≈⟨ ≋-cong (≋-n×a n a) (ρ⇐∘ρ⇒ xs) ⟩
        (a , lift n) ∷ xs                             ∎

    ρ⇒∘ρ⇐ : ρ⇒ ∘ ρ⇐ CMon.≈ id
    ρ⇒∘ρ⇐ xs = trans (identityʳ (xs ∙ ε)) (identityʳ xs)
