{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)

module CommutativeMonoids.FreeForget.Adjunction (c ℓ : Level) where

import Data.List.Relation.Binary.Equality.Setoid as ≋
import Data.List.Relation.Binary.Permutation.Algorithmic as Permutation
import Relation.Binary.PropositionalEquality as ≡
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Algebra using (CommutativeMonoid)
open import Categories.Adjoint using (Adjoint; _⊣_)
open import Categories.Functor using (_∘F_) renaming (id to Id)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import CommutativeMonoids.Category using (CommutativeMonoidHomomorphism; mk-⇒)
open import CommutativeMonoids.FreeForget.Forget c (c ⊔ ℓ) using (Forget; Underlying)
open import CommutativeMonoids.FreeForget.Free c (c ⊔ ℓ) using (Free; FreeCommutativeMonoid)
open import Data.List using (List; _++_; map; foldr; [_]; concat)
open import Data.List.Properties using (map-++; concat-map-[_])
open import Function using (_⟶ₛ_; Func; _⟨$⟩_)
open import Permutation.ExtraProperties using (map-↭)
open import Relation.Binary using (Setoid)

open List
open Func

module _ (A : Setoid c (c ⊔ ℓ)) where

  open Permutation A using (_↭_)
  open _↭_

  singleton : A ⟶ₛ Forget.₀ (Free.₀ A)
  singleton .to = [_]
  singleton .cong x≈y = x≈y ∷ []

unit : NaturalTransformation Id (Forget ∘F Free)
unit = ntHelper record
    { η = singleton
    ; commute = λ {_ Y} f {x} → ↭-refl Y [ f ⟨$⟩ x ]
    }
  where
    open Permutation using (↭-refl)

module _ (M : CommutativeMonoid c (c ⊔ ℓ)) where

  open CommutativeMonoid M
  open ≋ setoid using (_≋_)

  sum : List Carrier → Carrier
  sum = foldr _∙_ ε

  sum-++ : (xs ys : List Carrier) → sum (xs ++ ys) ≈ sum xs ∙ sum ys
  sum-++ [] ys = sym (identityˡ (sum ys))
  sum-++ (x ∷ xs) ys = trans (∙-congˡ (sum-++ xs ys)) (sym (assoc x (sum xs) (sum ys)))

  open Permutation setoid using (_↭_; _⋎[_]_)
  open ≈-Reasoning setoid
  open _↭_

  sum-↭ : {xs ys : List Carrier} → xs ↭ ys → sum xs ≈ sum ys
  sum-↭ [] = refl
  sum-↭ (x≈y ∷ xs↭ys) = ∙-cong x≈y (sum-↭ xs↭ys)
  sum-↭ {x ∷ xs} {y ∷ ys} (xs↭y∷zs ⋎[ zs ] x∷zs↭ys) = begin
      x ∙ sum xs        ≈⟨ ∙-congˡ (sum-↭ xs↭y∷zs) ⟩
      x ∙ (y ∙ sum zs)  ≈⟨ assoc x y (sum zs) ⟨
      x ∙ y ∙ sum zs    ≈⟨ ∙-congʳ (comm x y) ⟩
      y ∙ x ∙ sum zs    ≈⟨ assoc y x (sum zs) ⟩
      y ∙ sum (x ∷ zs)  ≈⟨ ∙-congˡ (sum-↭ x∷zs↭ys) ⟩
      y ∙ sum ys        ∎

  eval : CommutativeMonoidHomomorphism (Free.₀ (Forget.₀ M)) M
  eval = mk-⇒ record
      { ⟦_⟧ = sum
      ; isMonoidHomomorphism = record
          { isMagmaHomomorphism = record
              { isRelHomomorphism = record
                  { cong = sum-↭
                  }
              ; homo = sum-++
              }
          ; ε-homo = refl
          }
      }

module _ {X Y : CommutativeMonoid c (c ⊔ ℓ)} (f : CommutativeMonoidHomomorphism X Y) where

  private
    module X = CommutativeMonoid X

  open CommutativeMonoid Y
  open CommutativeMonoidHomomorphism f
  open ≈-Reasoning setoid

  sum-map : (xs : List X.Carrier) → sum Y (map ⟦_⟧ xs) ≈ ⟦ sum X xs ⟧
  sum-map [] = sym ε-homo
  sum-map (x ∷ xs) = begin
      ⟦ x ⟧ ∙ sum Y (map ⟦_⟧ xs)  ≈⟨ ∙-congˡ (sum-map xs) ⟩
      ⟦ x ⟧ ∙ ⟦ sum X xs ⟧        ≈⟨ homo x (sum X xs) ⟨
      ⟦ x X.∙ sum X xs ⟧          ∎

counit : NaturalTransformation (Free ∘F Forget) Id
counit = ntHelper record
    { η = eval
    ; commute = sum-map
    }

module _ {A : Setoid c (c ⊔ ℓ)} where

  open Setoid A
  open Permutation A using (_↭_; ↭-reflexive)
  open ≋ A using (≋-reflexive)

  zig : (xs : List Carrier) → concat (map [_] xs) ↭ xs
  zig xs = ↭-reflexive (≋-reflexive (concat-map-[ xs ]))

module _ {M : CommutativeMonoid c (c ⊔ ℓ)} where

  open CommutativeMonoid M

  zag : {x : Carrier} → sum M [ x ] ≈ x
  zag {x} = identityʳ x

Free⊣Forget : Free ⊣ Forget
Free⊣Forget = record
    { unit = unit
    ; counit = counit
    ; zig = zig
    ; zag = λ {M} → zag {M}
    }

module Free⊣Forget = Adjoint Free⊣Forget

module _ {A : Setoid c (c ⊔ ℓ)} {M : CommutativeMonoid c (c ⊔ ℓ)} where

  -- Extend a function into the underlying setoid of a commutative monoid
  -- into a monoid homomorphism from the free commutative monoid
  foldMap : A ⟶ₛ Underlying M → CommutativeMonoidHomomorphism (FreeCommutativeMonoid A) M
  foldMap = Free⊣Forget.Radjunct

  -- Restrict a monoid homomorphism from a free commutative monoid
  -- into an ordinary function from the base setoid
  onGenerators : CommutativeMonoidHomomorphism (FreeCommutativeMonoid A) M → A ⟶ₛ Underlying M
  onGenerators = Free⊣Forget.Ladjunct
