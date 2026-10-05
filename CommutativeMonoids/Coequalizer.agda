{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)
open import Algebra using (CommutativeMonoid)
open import CommutativeMonoids.Category using (CommutativeMonoids; CommutativeMonoidHomomorphism; mk-⇒)

module CommutativeMonoids.Coequalizer
    {c ℓ : Level}
    {A B : CommutativeMonoid c (c ⊔ ℓ)}
    (f g : CommutativeMonoidHomomorphism A B)
  where

import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Categories.Diagram.Coequalizer (CommutativeMonoids c (c ⊔ ℓ)) using (Coequalizer)
open import Data.Product using (_,_)
open import Function using (id)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)

private

  module A = CommutativeMonoid A
  module B = CommutativeMonoid B

  module f = CommutativeMonoidHomomorphism f
  module g = CommutativeMonoidHomomorphism g

  variable
    a b : A.Carrier
    u v w x y z : B.Carrier

open B

data _≋_ : Rel B.Carrier (c ⊔ ℓ) where
  base : x ≈ y → x ≋ y
  fwd  : x ≈ v ∙ f.⟦ a ⟧ → v ∙ g.⟦ a ⟧ ≈ y → y ≋ z → x ≋ z
  bwd  : x ≈ v ∙ g.⟦ a ⟧ → v ∙ f.⟦ a ⟧ ≈ y → y ≋ z → x ≋ z

infix 4 _≋_

≡-fwd : (v : B.Carrier) (a : A.Carrier) → v ∙ f.⟦ a ⟧ ≋ v ∙ g.⟦ a ⟧
≡-fwd _ _ = fwd refl refl (base refl)

≡-bwd : (v : B.Carrier) (a : A.Carrier) → v ∙ g.⟦ a ⟧ ≋ v ∙ f.⟦ a ⟧
≡-bwd _ _ = bwd refl refl (base refl)

≋-refl : x ≋ x
≋-refl {x} = base (refl {x})

≈-≋ : x ≈ y → y ≋ z → x ≋ z
≈-≋ x≈y (base y≈z) = base (trans x≈y y≈z)
≈-≋ x≈y (fwd y≈fa ga≈w w≋z) = fwd (trans x≈y y≈fa) ga≈w w≋z
≈-≋ x≈y (bwd y≈ga fa≈w w≋z) = bwd (trans x≈y y≈ga) fa≈w w≋z

≋-euclidean : y ≋ x → y ≋ z → x ≋ z
≋-euclidean (base y≈x) y≋z = ≈-≋ (sym y≈x) y≋z
≋-euclidean (fwd y≈fa ga≈w w≋x) y≋z = ≋-euclidean w≋x (bwd (sym ga≈w) (sym y≈fa) y≋z)
≋-euclidean (bwd y≈ga fa≈w w≋x) y≋z = ≋-euclidean w≋x (fwd (sym fa≈w) (sym y≈ga) y≋z)

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

≋-setoid : Setoid c (c ⊔ ℓ)
≋-setoid = record { isEquivalence = ≋-isEquiv }

≈-∙-≋ : x ≈ y → u ≋ v → x ∙ u ≋ y ∙ v
≈-∙-≋ x≈y (base u≈v) = base (∙-cong x≈y u≈v)
≈-∙-≋ {x} {y} x≈y (fwd {u} {w} {a} {z} {v} u≈wf⟦a⟧ wg⟦a⟧≈z z≋v) = fwd xu≈ywf⟦a⟧ ywg⟦a⟧≈yz (≈-∙-≋ refl z≋v)
  where
    open ≈-Reasoning setoid
    xu≈ywf⟦a⟧ : x ∙ u ≈ y ∙ w ∙ f.⟦ a ⟧
    xu≈ywf⟦a⟧ = begin
        x ∙ u             ≈⟨ ∙-cong x≈y u≈wf⟦a⟧ ⟩
        y ∙ (w ∙ f.⟦ a ⟧) ≈⟨ assoc y w f.⟦ a ⟧ ⟨
        y ∙ w ∙ f.⟦ a ⟧   ∎
    ywg⟦a⟧≈yz : y ∙ w ∙ g.⟦ a ⟧ ≈ y ∙ z
    ywg⟦a⟧≈yz = begin
        y ∙ w ∙ g.⟦ a ⟧   ≈⟨ assoc y w g.⟦ a ⟧ ⟩
        y ∙ (w ∙ g.⟦ a ⟧) ≈⟨ ∙-congˡ wg⟦a⟧≈z ⟩
        y ∙ z             ∎
≈-∙-≋ {x} {y} x≈y (bwd {u} {w} {a} {z} {v} u≈wg⟦a⟧ wf⟦a⟧≈z z≋v) = bwd xu≈ywg⟦a⟧ ywf⟦a⟧≈yz (≈-∙-≋ refl z≋v)
  where
    open ≈-Reasoning setoid
    xu≈ywg⟦a⟧ : x ∙ u ≈ y ∙ w ∙ g.⟦ a ⟧
    xu≈ywg⟦a⟧ = begin
        x ∙ u             ≈⟨ ∙-cong x≈y u≈wg⟦a⟧ ⟩
        y ∙ (w ∙ g.⟦ a ⟧) ≈⟨ assoc y w g.⟦ a ⟧ ⟨
        y ∙ w ∙ g.⟦ a ⟧   ∎
    ywf⟦a⟧≈yz : y ∙ w ∙ f.⟦ a ⟧ ≈ y ∙ z
    ywf⟦a⟧≈yz = begin
        y ∙ w ∙ f.⟦ a ⟧   ≈⟨ assoc y w f.⟦ a ⟧ ⟩
        y ∙ (w ∙ f.⟦ a ⟧) ≈⟨ ∙-congˡ wf⟦a⟧≈z ⟩
        y ∙ z             ∎

∙-resp-≋ : x ≋ y → u ≋ v → x ∙ u ≋ y ∙ v
∙-resp-≋ (base x≈y) u≋v = ≈-∙-≋ x≈y u≋v
∙-resp-≋ {u = u} {v} (fwd {x} {w} {a} {z} x≈wf⟦a⟧ wg⟦a⟧≈z z≋y) u≋v = fwd xu≈wuf⟦a⟧ wug⟦a⟧≈yu (∙-resp-≋ z≋y u≋v)
  where
    open ≈-Reasoning setoid
    xu≈wuf⟦a⟧ : x ∙ u ≈ w ∙ u ∙ f.⟦ a ⟧
    xu≈wuf⟦a⟧ = begin
        x ∙ u             ≈⟨ ∙-congʳ x≈wf⟦a⟧ ⟩
        w ∙ f.⟦ a ⟧ ∙ u   ≈⟨ assoc w f.⟦ a ⟧ u ⟩
        w ∙ (f.⟦ a ⟧ ∙ u) ≈⟨ ∙-congˡ (comm f.⟦ a ⟧ u) ⟩
        w ∙ (u ∙ f.⟦ a ⟧) ≈⟨ assoc w u f.⟦ a ⟧ ⟨
        w ∙ u ∙ f.⟦ a ⟧ ∎
    wug⟦a⟧≈yu : w ∙ u ∙ g.⟦ a ⟧ ≈ z ∙ u
    wug⟦a⟧≈yu = begin
        w ∙ u ∙ g.⟦ a ⟧   ≈⟨ assoc w u g.⟦ a ⟧ ⟩
        w ∙ (u ∙ g.⟦ a ⟧) ≈⟨ ∙-congˡ (comm u g.⟦ a ⟧) ⟩
        w ∙ (g.⟦ a ⟧ ∙ u) ≈⟨ assoc w g.⟦ a ⟧ u ⟨
        w ∙ g.⟦ a ⟧ ∙ u   ≈⟨ ∙-congʳ wg⟦a⟧≈z ⟩
        z ∙ u             ∎
∙-resp-≋ {u = u} {v} (bwd {x} {w} {a} {z} x≈wg⟦a⟧ wf⟦a⟧≈z z≋y) u≋v = bwd xu≈wug⟦a⟧ wuf⟦a⟧≈yu (∙-resp-≋ z≋y u≋v)
  where
    open ≈-Reasoning setoid
    xu≈wug⟦a⟧ : x ∙ u ≈ w ∙ u ∙ g.⟦ a ⟧
    xu≈wug⟦a⟧ = begin
        x ∙ u             ≈⟨ ∙-congʳ x≈wg⟦a⟧ ⟩
        w ∙ g.⟦ a ⟧ ∙ u   ≈⟨ assoc w g.⟦ a ⟧ u ⟩
        w ∙ (g.⟦ a ⟧ ∙ u) ≈⟨ ∙-congˡ (comm g.⟦ a ⟧ u) ⟩
        w ∙ (u ∙ g.⟦ a ⟧) ≈⟨ assoc w u g.⟦ a ⟧ ⟨
        w ∙ u ∙ g.⟦ a ⟧ ∎
    wuf⟦a⟧≈yu : w ∙ u ∙ f.⟦ a ⟧ ≈ z ∙ u
    wuf⟦a⟧≈yu = begin
        w ∙ u ∙ f.⟦ a ⟧   ≈⟨ assoc w u f.⟦ a ⟧ ⟩
        w ∙ (u ∙ f.⟦ a ⟧) ≈⟨ ∙-congˡ (comm u f.⟦ a ⟧) ⟩
        w ∙ (f.⟦ a ⟧ ∙ u) ≈⟨ assoc w f.⟦ a ⟧ u ⟨
        w ∙ f.⟦ a ⟧ ∙ u   ≈⟨ ∙-congʳ wf⟦a⟧≈z ⟩
        z ∙ u             ∎

C : CommutativeMonoid c (c ⊔ ℓ)
C = record
    { isCommutativeMonoid = record
        { isMonoid = record
            { isSemigroup = record
              { isMagma = record
                  { isEquivalence = ≋-isEquiv
                  ; ∙-cong = ∙-resp-≋
                  }
              ; assoc = λ x y z → base (assoc x y z)
              }
            ; identity = (λ x → base (identityˡ x)) , (λ x → base (identityʳ x))
            }
        ; comm = λ x y → base (comm x y)
        }
    }

h : CommutativeMonoidHomomorphism B C
h = mk-⇒ record
    { ⟦_⟧ = id
    ; isMonoidHomomorphism = record
        { isMagmaHomomorphism = record
            { isRelHomomorphism = record
                { cong = base
                }
            ; homo = λ x y → ≋-refl {x ∙ y}
            }
        ; ε-homo = ≋-refl {ε}
        }
    }

private
  module h = CommutativeMonoidHomomorphism h

coequalizes : (a : A.Carrier) → h.⟦ f.⟦ a ⟧ ⟧ ≋ h.⟦ g.⟦ a ⟧ ⟧
coequalizes a = fwd (sym (identityˡ f.⟦ a ⟧)) (identityˡ g.⟦ a ⟧) ≋-refl

module _ {X : CommutativeMonoid c (c ⊔ ℓ)} {k : CommutativeMonoidHomomorphism B X} where

  private
    module X = CommutativeMonoid X
    module k = CommutativeMonoidHomomorphism k

  module _ (eq : (a : A.Carrier) → k.⟦ f.⟦ a ⟧ ⟧ X.≈ k.⟦ g.⟦ a ⟧ ⟧) where

    open ≈-Reasoning X.setoid

    u-cong : x ≋ y → k.⟦ x ⟧ X.≈ k.⟦ y ⟧
    u-cong (base x≈y) = k.⟦⟧-cong x≈y
    u-cong {x} {y} (fwd {x} {v} {a} {y = z} {w} x≈vf⟦a⟧ vg⟦a⟧≈z z≋y) = begin
        k.⟦ x ⟧                   ≈⟨ k.⟦⟧-cong x≈vf⟦a⟧ ⟩
        k.⟦ v ∙ f.⟦ a ⟧ ⟧         ≈⟨ k.homo v f.⟦ a ⟧ ⟩
        k.⟦ v ⟧ X.∙ k.⟦ f.⟦ a ⟧ ⟧ ≈⟨ X.∙-congˡ (eq a) ⟩
        k.⟦ v ⟧ X.∙ k.⟦ g.⟦ a ⟧ ⟧ ≈⟨ k.homo v g.⟦ a ⟧ ⟨
        k.⟦ v ∙ g.⟦ a ⟧ ⟧         ≈⟨ k.⟦⟧-cong vg⟦a⟧≈z ⟩
        k.⟦ z ⟧                   ≈⟨ u-cong z≋y ⟩
        k.⟦ w ⟧                   ∎
    u-cong {x} {y} (bwd {x} {v} {a} {y = z} {w} x≈vg⟦a⟧ vf⟦a⟧≈z z≋y) = begin
        k.⟦ x ⟧                   ≈⟨ k.⟦⟧-cong x≈vg⟦a⟧ ⟩
        k.⟦ v ∙ g.⟦ a ⟧ ⟧         ≈⟨ k.homo v g.⟦ a ⟧ ⟩
        k.⟦ v ⟧ X.∙ k.⟦ g.⟦ a ⟧ ⟧ ≈⟨ X.∙-congˡ (eq a) ⟨
        k.⟦ v ⟧ X.∙ k.⟦ f.⟦ a ⟧ ⟧ ≈⟨ k.homo v f.⟦ a ⟧ ⟨
        k.⟦ v ∙ f.⟦ a ⟧ ⟧         ≈⟨ k.⟦⟧-cong vf⟦a⟧≈z ⟩
        k.⟦ z ⟧                   ≈⟨ u-cong z≋y ⟩
        k.⟦ y ⟧                   ∎

    u! : CommutativeMonoidHomomorphism C X
    u! = mk-⇒ record
        { ⟦_⟧ = k.⟦_⟧
        ; isMonoidHomomorphism = record
            { isMagmaHomomorphism = record
                { isRelHomomorphism = record
                    { cong = u-cong
                    }
                ; homo = k.homo
                }
            ; ε-homo = k.ε-homo
            }
        }

    private
      module u = CommutativeMonoidHomomorphism u!

    universal : (X : B.Carrier) → k.⟦ x ⟧ X.≈ u.⟦ h.⟦ x ⟧ ⟧
    universal x = X.refl

  module _ {i : CommutativeMonoidHomomorphism C X} (eq : (a : A.Carrier) → k.⟦ f.⟦ a ⟧ ⟧ X.≈ k.⟦ g.⟦ a ⟧ ⟧) where

    private
      module i = CommutativeMonoidHomomorphism i
      module u = CommutativeMonoidHomomorphism (u! eq)

    unique : k.⟦ x ⟧ X.≈ i.⟦ h.⟦ x ⟧ ⟧ → i.⟦ x ⟧ X.≈ u.⟦ x ⟧
    unique = X.sym

coequalizer : Coequalizer f g
coequalizer = record
    { obj = C
    ; arr = h
    ; isCoequalizer = record
        { equality = coequalizes
        ; coequalize = λ {X k} eq → u! {X} {k} eq
        ; universal = λ {X k eq} x → universal {X} {k} eq x
        ; unique = λ {X k i eq} k≈i∘h x → unique {X} {k} {i} eq (k≈i∘h x)
        }
    }
