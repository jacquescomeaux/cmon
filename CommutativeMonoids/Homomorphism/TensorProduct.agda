{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)
open import Algebra using (CommutativeMonoid)
open import CommutativeMonoids.Category using (CommutativeMonoidHomomorphism; CommutativeMonoids; mk-⇒)

module CommutativeMonoids.Homomorphism.TensorProduct
    {c ℓ : Level}
    {A B C D : CommutativeMonoid c (c ⊔ ℓ)}
    (f : CommutativeMonoidHomomorphism A B)
    (g : CommutativeMonoidHomomorphism C D)
  where

import CommutativeMonoids.Category.Coequalizer.FromFree {c} {ℓ} as Coeq
import CommutativeMonoids.Construction.CongruenceClosure {c} {ℓ} as CongruenceClosure
import CommutativeMonoids.Construction.TensorProduct {c} {ℓ} as ⊗

open import Algebra.Construct.DirectProduct using () renaming (commutativeMonoid to _⊕_)
open import CommutativeMonoids.Construction.FormalSum c ℓ using (⅀; FormalSum)
open import Data.Product using (_,_) renaming (map to ×-map)
open import Function using (Func)
open import Relation.Binary.Construct.Closure.Symmetric using (SymClosure)
open import Setoids.Multiset c ℓ using (pureₛ)

open CommutativeMonoids using (_∘_)
open Func
open SymClosure

private
  module ⊗-A-C = ⊗ A C
  module ⊗-B-D = ⊗ B D
  module B = CommutativeMonoid B
  module D = CommutativeMonoid D
  module ⅀B⊕D = CommutativeMonoid (⅀ (B ⊕ D))
  module A⊕C = CommutativeMonoid (A ⊕ C)
  module B⊕D = CommutativeMonoid (B ⊕ D)
  module f = CommutativeMonoidHomomorphism f
  module g = CommutativeMonoidHomomorphism g

open ⊗-A-C using () renaming (M⊗N to A⊗C)
open ⊗-B-D using () renaming (M⊗N to B⊗D)

open Coeq {⊗-B-D.Iₛ} {⅀ (B ⊕ D)} ⊗-B-D.f ⊗-B-D.g using (_~_)
open CongruenceClosure (⅀ (B ⊕ D)) _~_ using (_≋_; ≋-refl; _~[_]_)
open ⊗-B-D.I
open _~_
open _≋_

⟦_⟧ : A⊕C.Carrier → B⊕D.Carrier
⟦_⟧ = ×-map f.⟦_⟧ g.⟦_⟧

⟦⟧-cong : {x y : A⊕C.Carrier} → x A⊕C.≈ y → ⟦ x ⟧ B⊕D.≈ ⟦ y ⟧
⟦⟧-cong = ×-map f.⟦⟧-cong g.⟦⟧-cong

f×ₘg : CommutativeMonoidHomomorphism (A ⊕ C) (B ⊕ D)
f×ₘg = mk-⇒ record
    { ⟦_⟧ = ⟦_⟧
    ; isMonoidHomomorphism = record
        { isMagmaHomomorphism = record
            { isRelHomomorphism = record { cong = ⟦⟧-cong }
            ; homo = λ (a , b) (c , d) → f.homo a c , g.homo b d
            }
        ; ε-homo = f.ε-homo , g.ε-homo
        }
    }

f⊗g : CommutativeMonoidHomomorphism A⊗C B⊗D
f⊗g =
    ⊗-A-C.Universal.u!
      (⊗-B-D.eval ∘ FormalSum.F.₁ f×ₘg)
      (λ {y} → cong pureₛ (f.ε-homo , D.refl) ~[ fwd (f~g (εˡ g.⟦ y ⟧)) ] ⅀B⊕D.refl ◅ ≋-refl)
      (λ {x} → cong pureₛ (B.refl , g.ε-homo) ~[ fwd (f~g (εʳ f.⟦ x ⟧)) ] ⅀B⊕D.refl ◅ ≋-refl)
      (λ {x₁ x₂ y} → _~[_]_ {ctx = ⅀B⊕D.ε} ⅀B⊕D.refl (fwd (f~g (∙ˡ f.⟦ x₁ ⟧ f.⟦ x₂ ⟧ g.⟦ y ⟧))) (cong pureₛ (B.sym (f.homo x₁ x₂) , D.refl)) ◅ ≋-refl)
      (λ {x y₁ y₂} → _~[_]_ {ctx = ⅀B⊕D.ε} ⅀B⊕D.refl (fwd (f~g (∙ʳ f.⟦ x ⟧ g.⟦ y₁ ⟧ g.⟦ y₂ ⟧))) (cong pureₛ (B.refl , D.sym (g.homo y₁ y₂))) ◅ ≋-refl)
