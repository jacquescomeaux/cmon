{-# OPTIONS --without-K --safe #-}

open import Algebra using (CommutativeMonoid)
open import Level using (Level; _⊔_)
open import CommutativeMonoids.Category
  using (CommutativeMonoids ; CommutativeMonoidHomomorphism; _≗_)
  renaming (module CommutativeMonoids to CMon)

module CommutativeMonoids.Coequalizer
    {c ℓ : Level}
    {A B : CommutativeMonoid c (c ⊔ ℓ)}
    (f g : CommutativeMonoidHomomorphism A B)
  where

import CommutativeMonoids.CongruenceClosure {c} {ℓ} as CongruenceClosure
import CommutativeMonoids.Quotient as Quotient

open import Categories.Diagram.Coequalizer (CommutativeMonoids c (c ⊔ ℓ)) using (Coequalizer)
open import CommutativeMonoids.Congruence using (Congruence)
open import Relation.Binary using (Rel)

open CMon using (_∘_)

private

  module A = CommutativeMonoid A
  module B = CommutativeMonoid B

  module f = CommutativeMonoidHomomorphism f
  module g = CommutativeMonoidHomomorphism g

  variable
    x y : B.Carrier

open B

data _~_ : Rel Carrier c where
  f~g : (a : A.Carrier) → f.⟦ a ⟧ ~ g.⟦ a ⟧

infix 4 _~_

open CongruenceClosure B _~_ using (_≋_; _◅[_]_; ≋-congruence; step-fwd; equates-≋)
open Quotient B ≋-congruence using (module Universal) renaming (M/≋ to C; π to h)

coequalizes : h ∘ f ≗ h ∘ g
coequalizes a = step-fwd (f~g a)

module _
    {X : CommutativeMonoid c (c ⊔ ℓ)}
    (k : CommutativeMonoidHomomorphism B X)
    (eq : k ∘ f ≗ k ∘ g)
  where

  private
    module X = CommutativeMonoid X
    module k = CommutativeMonoidHomomorphism k

  k-equates-~ : x ~ y → k.⟦ x ⟧ X.≈ k.⟦ y ⟧
  k-equates-~ (f~g a) = eq a

  k-equates-≋ : x ≋ y → k.⟦ x ⟧ X.≈ k.⟦ y ⟧
  k-equates-≋ = equates-≋ k k-equates-~

  open Universal k k-equates-≋

  u! : CommutativeMonoidHomomorphism C X
  u! = induced

  universal : k ≗ u! ∘ h
  universal = factors

  u!-unique : (g : CommutativeMonoidHomomorphism C X) → k ≗ g ∘ h → g ≗ u!
  u!-unique = unique

coequalizer : Coequalizer f g
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
