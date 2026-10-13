{-# OPTIONS --without-K --safe #-}

import CommutativeMonoids.FreeForget.Free as Fr
import CommutativeMonoids.FreeForget.Forget as Fo

open import Algebra using (CommutativeMonoid)
open import Function using (_⟶ₛ_; _⟨$⟩_)
open import Level using (Level; _⊔_)
open import Relation.Binary using (Setoid; Rel)

-- Coequalizers for f g : A ⇒ B where the commutative monoid
-- structure on A is explicitly ignored
module CommutativeMonoids.Category.Coequalizer.FromFree
    {c ℓ : Level}
    (open Fr c (c ⊔ ℓ) using () renaming (FreeCommutativeMonoid to F))
    (open Fo c (c ⊔ ℓ) using () renaming (Underlying to U))
    {A : Setoid c (c ⊔ ℓ)}
    {B : CommutativeMonoid c (c ⊔ ℓ)}
    (f g : A ⟶ₛ U B)
  where

import CommutativeMonoids.Construction.CongruenceClosure {c} {ℓ} as CongruenceClosure
import CommutativeMonoids.Construction.Quotient as Quotient
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import CommutativeMonoids.Category
  using (CommutativeMonoids; CommutativeMonoidHomomorphism; _≗_)
  renaming (module CommutativeMonoids to CMon)

open import Categories.Adjoint using (Adjoint)
open import Categories.Diagram.Coequalizer (CommutativeMonoids c (c ⊔ ℓ)) using (Coequalizer)
open import CommutativeMonoids.FreeForget.Adjunction c ℓ using (Free⊣Forget; foldMap)
open import Data.List using ([_])
open import Function.Construct.Setoid using () renaming (_∙_ to _⊚_)

open Adjoint Free⊣Forget using (Radjunct-resp-≈; Radjunct-comm′)
open CMon using (_∘_)

f♭ g♭ : CommutativeMonoidHomomorphism (F A) B
f♭ = foldMap f
g♭ = foldMap g

private

  module A = Setoid A
  module B = CommutativeMonoid B

  variable
    x y : B.Carrier

open B

data _~_ : Rel Carrier (c ⊔ ℓ) where
  f~g : (a : A.Carrier) → f ⟨$⟩ a ~ g ⟨$⟩ a

infix 4 _~_

open CongruenceClosure B _~_ using (_≋_; _◅[_]_; ≋-congruence; step-fwd; equates-≋)
open Quotient B ≋-congruence using (module Universal) renaming (M/≋ to C; π to h)

private
  module C = CommutativeMonoid C
  module h = CommutativeMonoidHomomorphism h

coequalizes′ : {a : A.Carrier} → h.⟦ f ⟨$⟩ a ⟧ ≋ h.⟦ g ⟨$⟩ a ⟧
coequalizes′ {a} = step-fwd (f~g a)

coequalizes : h ∘ f♭ ≗ h ∘ g♭
coequalizes = begin
    h ∘ f♭                ≈⟨ Radjunct-comm′ {f = f} {h} ⟨
    foldMap (h.func ⊚ f)  ≈⟨ Radjunct-resp-≈ {B = C} {h.func ⊚ f} {h.func ⊚ g} coequalizes′ ⟩
    foldMap (h.func ⊚ g)  ≈⟨ Radjunct-comm′ {f = g} {h} ⟩
    h ∘ g♭                ∎
  where
    open CMon.HomReasoning

module _
    {X : CommutativeMonoid c (c ⊔ ℓ)}
    (k : CommutativeMonoidHomomorphism B X)
    (eq : k ∘ f♭ ≗ k ∘ g♭)
  where

  private
    module X = CommutativeMonoid X
    module k = CommutativeMonoidHomomorphism k

  eq′ : (a : A.Carrier) → k.⟦ f ⟨$⟩ a ⟧ X.≈ k.⟦ g ⟨$⟩ a ⟧
  eq′ a = begin
      k.⟦ f ⟨$⟩ a ⟧       ≈⟨ k.⟦⟧-cong (identityʳ (f ⟨$⟩ a)) ⟨
      k.⟦ (f ⟨$⟩ a) ∙ ε ⟧ ≈⟨ eq [ a ] ⟩
      k.⟦ (g ⟨$⟩ a) ∙ ε ⟧ ≈⟨ k.⟦⟧-cong (identityʳ (g ⟨$⟩ a)) ⟩
      k.⟦ g ⟨$⟩ a ⟧       ∎
    where
      open ≈-Reasoning X.setoid

  k-equates-~ : x ~ y → k.⟦ x ⟧ X.≈ k.⟦ y ⟧
  k-equates-~ (f~g a) = eq′ a

  k-equates-≋ : x ≋ y → k.⟦ x ⟧ X.≈ k.⟦ y ⟧
  k-equates-≋ = equates-≋ k k-equates-~

  open Universal k k-equates-≋

  u! : CommutativeMonoidHomomorphism C X
  u! = induced

  universal : k ≗ u! ∘ h
  universal = factors

  u!-unique : (g : CommutativeMonoidHomomorphism C X) → k ≗ g ∘ h → g ≗ u!
  u!-unique = unique

coequalizer : Coequalizer {F A} {B} f♭ g♭
coequalizer = record
    { obj = C
    ; arr = h
    ; isCoequalizer = record
        { equality = coequalizes
        ; coequalize = λ {_ k} → u! k
        ; universal = λ {_ k eq} → universal k eq
        ; unique = λ {_ k i eq} → u!-unique k eq i
        }
    }
