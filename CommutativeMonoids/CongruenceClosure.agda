{-# OPTIONS --without-K --safe #-}

open import Algebra using (CommutativeMonoid)
open import Level using (Level; _⊔_)
open import Relation.Binary using (Rel; IsEquivalence; Setoid; _Preserves_⟶_)

module CommutativeMonoids.CongruenceClosure
    {c ℓ : Level}
    (M : CommutativeMonoid c (c ⊔ ℓ))
    (open CommutativeMonoid M)
    (R : Rel Carrier ℓ)
  where

import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import CommutativeMonoids.Category using (CommutativeMonoidHomomorphism; mk-⇒)
open import CommutativeMonoids.Congruence using (Congruence)
open import Data.Product using (_,_)
open import Function using (id)
open import Relation.Binary.Construct.Closure.Symmetric using (SymClosure)

open SymClosure

private
  variable
    x y z : Carrier

-- Symmetric context closure modulo equivalence of R
record _~_ (x y : Carrier) : Set (c ⊔ ℓ) where

  constructor _~[_]_

  field
    {u v ctx} : Carrier
    x≈cu : x ≈ ctx ∙ u
    uRv : SymClosure R u v
    cv≈y : ctx ∙ v ≈ y

infix 4 _~_
infix 6 _~[_]_

~-sym : x ~ y → y ~ x
~-sym (x≈cu ~[ fwd uRv ] cv≈y) = sym cv≈y ~[ bwd uRv ] sym x≈cu
~-sym (x≈cu ~[ bwd vRu ] cv≈y) = sym cv≈y ~[ fwd vRu ] sym x≈cu

~-congˡ : (z : Carrier) → x ~ y → z ∙ x ~ z ∙ y
~-congˡ {x} {y} z x~y = zx≈czu ~[ uRv ] czv≈zy
  where
    open _~_ x~y
    open ≈-Reasoning setoid
    zx≈czu : z ∙ x ≈ ctx ∙ z ∙ u
    zx≈czu = begin
        z ∙ x         ≈⟨ ∙-congˡ x≈cu ⟩
        z ∙ (ctx ∙ u) ≈⟨ assoc z ctx u ⟨
        z ∙ ctx ∙ u   ≈⟨ ∙-congʳ (comm z ctx) ⟩
        ctx ∙ z ∙ u   ∎
    czv≈zy : ctx ∙ z ∙ v ≈ z ∙ y
    czv≈zy = begin
        ctx ∙ z ∙ v   ≈⟨ ∙-congʳ (comm ctx z) ⟩
        z ∙ ctx ∙ v   ≈⟨ assoc z ctx v ⟩
        z ∙ (ctx ∙ v) ≈⟨ ∙-congˡ cv≈y ⟩
        z ∙ y         ∎

-- Congruence closure modulo equivalence of R
data _≋_ : Rel Carrier (c ⊔ ℓ) where
  base : x ≈ y → x ≋ y
  _◅_  : x ~ y → y ≋ z → x ≋ z

pattern _◅[_]_ {x} {z} x~y y y≋z = _◅_ {x} {y} {z} x~y y≋z

infix 4 _≋_
infixr 5 _◅_ _◅[_]_

≈-≋-trans : x ≈ y → y ≋ z → x ≋ z
≈-≋-trans x≈y (base y≈z) = base (trans x≈y y≈z)
≈-≋-trans x≈y (y≈cu ~[ u~v ] cv≈w ◅[ w ] w≈z) = trans x≈y y≈cu ~[ u~v ] cv≈w ◅[ w ] w≈z

≋-refl : x ≋ x
≋-refl {x} = base (refl {x})

≋-euclidean : y ≋ x → y ≋ z → x ≋ z
≋-euclidean (base y≈x) y≋z = ≈-≋-trans (sym y≈x) y≋z
≋-euclidean {y} (y~w ◅[ w ] w≋x) y≋z = ≋-euclidean w≋x (~-sym y~w ◅[ y ] y≋z)

≋-sym : x ≋ y → y ≋ x
≋-sym x≋y = ≋-euclidean x≋y ≋-refl

≋-trans : x ≋ y → y ≋ z → x ≋ z
≋-trans x≋y = ≋-euclidean (≋-sym x≋y)

≋-isEquiv : IsEquivalence _≋_
≋-isEquiv = record
    { refl = ≋-refl
    ; sym = ≋-sym
    ; trans = ≋-trans
    }

≋-congˡ : x ≋ y → z ∙ x ≋ z ∙ y
≋-congˡ (base x≈y) = base (∙-congˡ x≈y)
≋-congˡ {z = z} (x~w ◅[ w ] w≋y) = ~-congˡ z x~w ◅[ z ∙ w ] ≋-congˡ w≋y

-- Congruence closure modulo equivalence of R
≋-congruence : Congruence M
≋-congruence = record
    { _≋_ = _≋_
    ; isCongruence = record
        { refl = base
        ; sym = ≋-sym
        ; trans = ≋-trans
        ; congˡ = ≋-congˡ
        }
    }

-- Using equations directly
one-step : x ~ y → x ≋ y
one-step x~y = x~y ◅ ≋-refl

ctx-step-fwd : (v : Carrier) → R x y → v ∙ x ≋ v ∙ y
ctx-step-fwd {x} {y} v xRy = one-step (refl ~[ fwd xRy ] refl)

ctx-step-bwd : (v : Carrier) → R x y → v ∙ y ≋ v ∙ x
ctx-step-bwd v xRy = one-step (refl ~[ bwd xRy ] refl)

step-fwd : R x y → x ≋ y
step-fwd {x} {y} xRy = one-step (sym (identityˡ x) ~[ fwd xRy ] identityˡ y)

step-bwd : R x y → y ≋ x
step-bwd {x} {y} xRy = one-step (sym (identityˡ y) ~[ bwd xRy ] identityˡ x)

-- A proof that f equates elements related by R extends to
-- a proof that f equates elements related by _≋_
module _
    {X : CommutativeMonoid c (c ⊔ ℓ)}
    (f : CommutativeMonoidHomomorphism M X)
    (let private module X = CommutativeMonoid X)
    (let private module f = CommutativeMonoidHomomorphism f)
    (equates-R : f.⟦_⟧ Preserves R ⟶ X._≈_)
  where

  equates-Rₛ : f.⟦_⟧ Preserves (SymClosure R) ⟶ X._≈_
  equates-Rₛ (fwd xRy) = equates-R xRy
  equates-Rₛ (bwd yRx) = X.sym (equates-R yRx)

  equates-~ : f.⟦_⟧ Preserves _~_ ⟶ X._≈_
  equates-~ {x} {y} x~y = let open _~_ x~y in begin
      f.⟦ x ⟧               ≈⟨ f.⟦⟧-cong x≈cu ⟩
      f.⟦ ctx ∙ u ⟧         ≈⟨ f.homo ctx u ⟩
      f.⟦ ctx ⟧ X.∙ f.⟦ u ⟧ ≈⟨ X.∙-congˡ (equates-Rₛ uRv) ⟩
      f.⟦ ctx ⟧ X.∙ f.⟦ v ⟧ ≈⟨ f.homo ctx v ⟨
      f.⟦ ctx ∙ v ⟧         ≈⟨ f.⟦⟧-cong cv≈y ⟩
      f.⟦ y ⟧               ∎
    where
      open ≈-Reasoning X.setoid

  equates-≋ : f.⟦_⟧ Preserves _≋_ ⟶ X._≈_
  equates-≋ (base x≈y) = f.⟦⟧-cong x≈y
  equates-≋ (x~z ◅[ z ] z≋y) = X.trans (equates-~ x~z) (equates-≋ z≋y)
