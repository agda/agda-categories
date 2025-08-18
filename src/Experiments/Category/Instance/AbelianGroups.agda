{-# OPTIONS --without-K --safe #-}
module Experiments.Category.Instance.AbelianGroups where

open import Level
open import Function using (_$_)

open import Data.Product using (Σ; _,_; proj₁)
open import Data.Unit using (⊤)

open import Algebra.Core
open import Algebra.Bundles using (AbelianGroup) public
open import Algebra.Structures using (IsAbelianGroup) public
open import Algebra.Properties.AbelianGroup

import Algebra.Definitions as Define
open import Algebra.Morphism.Structures
import Algebra.Morphism.Definitions as MorDefine

open import Relation.Binary
import Relation.Binary.Reasoning.Setoid as SR

open import Categories.Category
open import Categories.Functor
open import Categories.Morphism
open import Categories.Morphism.Notation

import Categories.Morphism.Reasoning as MR


-- FIXME: Where should this live????
Delooping : ∀ {c ℓ} → AbelianGroup c ℓ → Category 0ℓ c ℓ
Delooping G = record
  { Obj = ⊤
  ; _⇒_ = λ _ _ → Carrier
  ; _≈_ = _≈_
  ; id = ε
  ; _∘_ = _∙_
  ; assoc = assoc _ _ _
  ; sym-assoc = sym (assoc _ _ _)
  ; identityˡ = identityˡ _
  ; identityʳ = identityʳ _
  ; identity² = identityʳ _
  ; equiv = isEquivalence
  ; ∘-resp-≈ = ∙-cong
  }
  where
    open AbelianGroup G


-- FIXME: Random group properties
_[_∙_] : ∀ {c′ ℓ′} → (G : AbelianGroup c′ ℓ′) → AbelianGroup.Carrier G → AbelianGroup.Carrier G → AbelianGroup.Carrier G
_[_∙_] = AbelianGroup._∙_

_[_⁻¹] : ∀ {c′ ℓ′} → (G : AbelianGroup c′ ℓ′) → AbelianGroup.Carrier G → AbelianGroup.Carrier G
_[_⁻¹] = AbelianGroup._⁻¹

module _ {c ℓ} (G : AbelianGroup c ℓ) where
  open AbelianGroup G
  open SR setoid
  open MR (Delooping G)

  ⁻¹-distrib-∙ : ∀ x y → (x ∙ y) ⁻¹ ≈ x ⁻¹ ∙ y ⁻¹
  ⁻¹-distrib-∙ x y = sym $ uniqueˡ-⁻¹ (x ⁻¹ ∙ y ⁻¹) (x ∙ y) $ begin
    (x ⁻¹ ∙ y ⁻¹) ∙ (x ∙ y) ≈⟨ ∙-congˡ (comm x y) ⟩
    (x ⁻¹ ∙ y ⁻¹) ∙ (y ∙ x) ≈⟨ cancelInner (inverseˡ y) ⟩
    x ⁻¹ ∙  x               ≈⟨ inverseˡ x ⟩
    ε                       ∎

-- The stdlib provides an annoying version of group homomorphisms, so it's easier to roll our own bundled form
record AbelianGroupHomomorphism {c c′ ℓ ℓ′} (G : AbelianGroup c ℓ) (H : AbelianGroup c′ ℓ′) : Set (c ⊔ c′ ⊔ ℓ ⊔ ℓ′) where
  private
    module G = AbelianGroup G
    module H = AbelianGroup H
    open MorDefine G.Carrier H.Carrier H._≈_
    open G using () renaming (_∙_ to _∙ᴳ_; ε to εᴳ; _⁻¹ to _⁻¹ᴳ; _≈_ to _≈ᴳ_)
    open H using () renaming (_∙_ to _∙ᴴ_; ε to εᴴ; _⁻¹ to _⁻¹ᴴ; _≈_ to _≈ᴴ_)
    open SR H.setoid

  field
    ⟦_⟧ : G.Carrier → H.Carrier
    cong : ∀ {x y} → x ≈ᴳ y → ⟦ x ⟧ ≈ᴴ ⟦ y ⟧
    homo : Homomorphic₂ ⟦_⟧ _∙ᴳ_ _∙ᴴ_

  ε-homo : ⟦ εᴳ ⟧ ≈ᴴ εᴴ
  ε-homo = begin
    ⟦ εᴳ ⟧                           ≈˘⟨ H.identityˡ ⟦ εᴳ ⟧ ⟩
    εᴴ ∙ᴴ ⟦ εᴳ ⟧                     ≈˘⟨ H.∙-congʳ (H.inverseˡ ⟦ εᴳ ⟧) ⟩
    ⟦ εᴳ ⟧ ⁻¹ᴴ ∙ᴴ ⟦ εᴳ ⟧ ∙ᴴ ⟦ εᴳ ⟧   ≈⟨ H.assoc (⟦ εᴳ ⟧ ⁻¹ᴴ) ⟦ εᴳ ⟧ ⟦ εᴳ ⟧ ⟩
    ⟦ εᴳ ⟧ ⁻¹ᴴ ∙ᴴ (⟦ εᴳ ⟧ ∙ᴴ ⟦ εᴳ ⟧) ≈˘⟨ H.∙-congˡ (homo εᴳ εᴳ) ⟩
    ⟦ εᴳ ⟧ ⁻¹ᴴ ∙ᴴ ⟦ εᴳ ∙ᴳ εᴳ ⟧       ≈⟨ H.∙-congˡ (cong (G.identityʳ εᴳ)) ⟩
    ⟦ εᴳ ⟧ ⁻¹ᴴ ∙ᴴ ⟦ εᴳ ⟧             ≈⟨ H.inverseˡ ⟦ εᴳ ⟧ ⟩
    εᴴ                               ∎

  ⁻¹-homo : ∀ x → ⟦ x ⁻¹ᴳ ⟧ ≈ᴴ ⟦ x ⟧ ⁻¹ᴴ
  ⁻¹-homo x = begin
    ⟦ x ⁻¹ᴳ ⟧                         ≈˘⟨  H.identityˡ ⟦ x ⁻¹ᴳ ⟧  ⟩
    εᴴ ∙ᴴ ⟦ x ⁻¹ᴳ ⟧                   ≈˘⟨ H.∙-congʳ (H.inverseˡ ⟦ x ⟧) ⟩
    ⟦ x ⟧ ⁻¹ᴴ ∙ᴴ ⟦ x ⟧ ∙ᴴ ⟦ x ⁻¹ᴳ ⟧   ≈⟨ H.assoc (⟦ x ⟧ ⁻¹ᴴ) ⟦ x ⟧ ⟦ x ⁻¹ᴳ ⟧ ⟩
    ⟦ x ⟧ ⁻¹ᴴ ∙ᴴ (⟦ x ⟧ ∙ᴴ ⟦ x ⁻¹ᴳ ⟧) ≈˘⟨ H.∙-congˡ (homo x (x ⁻¹ᴳ)) ⟩
    ⟦ x ⟧ ⁻¹ᴴ ∙ᴴ ⟦ x ∙ᴳ x ⁻¹ᴳ ⟧       ≈⟨ H.∙-congˡ (cong (G.inverseʳ x)) ⟩
    ⟦ x ⟧ ⁻¹ᴴ ∙ᴴ ⟦ εᴳ ⟧               ≈⟨ H.∙-congˡ ε-homo ⟩
    ⟦ x ⟧ ⁻¹ᴴ ∙ᴴ εᴴ                   ≈⟨ H.identityʳ (⟦ x ⟧ ⁻¹ᴴ) ⟩
    ⟦ x ⟧ ⁻¹ᴴ ∎

open AbelianGroupHomomorphism

AbelianGroups : ∀ c ℓ → Category (suc c ⊔ suc ℓ) (c ⊔ ℓ) (c ⊔ ℓ)
AbelianGroups c ℓ = record
  { Obj = AbelianGroup c ℓ
  ; _⇒_ = AbelianGroupHomomorphism
  ; _≈_ = λ {G} {H} f g → ∀ x → AbelianGroup._≈_ H (⟦ f ⟧ x) (⟦ g ⟧ x)
  ; id = λ {G} → record
    { ⟦_⟧ = λ x → x
    ; cong = λ eq → eq
    ; homo = λ x y → AbelianGroup.refl G
    }
  ; _∘_ = λ {G} {H} {I} f g →
    let module G = AbelianGroup G
        module H = AbelianGroup H
        module I = AbelianGroup I
        module f = AbelianGroupHomomorphism f
        module g = AbelianGroupHomomorphism g
        open SR I.setoid
    in record
      { ⟦_⟧ = λ x → f.⟦ g.⟦ x ⟧ ⟧ 
      ; cong = λ eq → f.cong (g.cong eq)
      ; homo = λ x y → begin
        f.⟦ g.⟦ x G.∙ y ⟧ ⟧             ≈⟨ f.cong (g.homo x y) ⟩
        f.⟦ g.⟦ x ⟧ H.∙ g.⟦ y ⟧ ⟧       ≈⟨ f.homo g.⟦ x ⟧ g.⟦ y ⟧ ⟩
        f.⟦ g.⟦ x ⟧ ⟧ I.∙ f.⟦ g.⟦ y ⟧ ⟧ ∎
      }
  ; assoc = λ {G} {H} {I} {J} {f} {g} {h} x → AbelianGroup.refl J
  ; sym-assoc = λ {G} {H} {I} {J} {f} {g} {h} x → AbelianGroup.refl J
  ; identityˡ = λ {A} {B} {f} x → AbelianGroup.refl B
  ; identityʳ = λ {A} {B} {f} x → AbelianGroup.refl B
  ; identity² = λ {A} x → AbelianGroup.refl A
  ; equiv = λ {A} {B} → record
    { refl = λ x → AbelianGroup.refl B
    ; sym = λ eq x → AbelianGroup.sym B (eq x)
    ; trans = λ eq₁ eq₂ x → AbelianGroup.trans B (eq₁ x) (eq₂ x)
    }
  ; ∘-resp-≈ = λ {A} {B} {C} {f} {g} {h} {i} eq₁ eq₂ x → 
    let module C = AbelianGroup C
        module f = AbelianGroupHomomorphism f
        module g = AbelianGroupHomomorphism g
        module h = AbelianGroupHomomorphism h
        module i = AbelianGroupHomomorphism i
        open SR C.setoid
    in begin
      f.⟦ h.⟦ x ⟧ ⟧ ≈⟨ f.cong (eq₂ x) ⟩
      f.⟦ i.⟦ x ⟧ ⟧ ≈⟨ eq₁ i.⟦ x ⟧ ⟩
      g.⟦ i.⟦ x ⟧ ⟧ ∎
  }

--------------------------------------------------------------------------------
-- Helper for creating abelian groups

private

  record IsAbelianGroupHelper {c ℓ} {A : Set c} (_≈_ : Rel A ℓ) (_∙_ : Op₂ A) (ε : A) (_⁻¹ : Op₁ A) : Set (c ⊔ ℓ) where
    open Define _≈_

    field
      isEquivalence : IsEquivalence _≈_
      ∙-cong        : Congruent₂ _∙_
      ⁻¹-cong       : Congruent₁ _⁻¹
      assoc         : Associative _∙_
      identityˡ     : LeftIdentity ε _∙_
      inverseˡ      : LeftInverse ε _⁻¹ _∙_
      comm          : Commutative _∙_

  record AbelianGroupHelper (c ℓ : Level) : Set (suc (c ⊔ ℓ)) where
    field
      Carrier       : Set c
      _≈_           : Rel Carrier ℓ
      _∙_           : Op₂ Carrier
      ε             : Carrier
      _⁻¹           : Op₁ Carrier

    open Define _≈_

    field
      isEquivalence : IsEquivalence _≈_
      ∙-cong        : Congruent₂ _∙_
      ⁻¹-cong       : Congruent₁ _⁻¹
      assoc         : Associative _∙_
      identityˡ     : LeftIdentity ε _∙_
      inverseˡ      : LeftInverse ε _⁻¹ _∙_
      comm          : Commutative _∙_

isAbGroupHelper : ∀ {c ℓ} {A : Set c} {_≈_ : Rel A ℓ} {_∙_ : Op₂ A} {ε : A} {_⁻¹ : Op₁ A}
                  → IsAbelianGroupHelper _≈_ _∙_ ε _⁻¹
                  → IsAbelianGroup _≈_ _∙_ ε _⁻¹
isAbGroupHelper {_≈_ = _≈_} {_∙_ = _∙_} {ε = ε} {_⁻¹ = _⁻¹} helper = record
  { isGroup = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = isEquivalence
          ; ∙-cong = ∙-cong
          }
        ; assoc = assoc
        }
      ; identity = identityˡ , (λ x → trans (comm x ε) (identityˡ x))
      }
    ; inverse = inverseˡ , (λ x → trans (comm x (x ⁻¹)) (inverseˡ x))
    ; ⁻¹-cong = ⁻¹-cong
    }
  ; comm = comm
  }
  where
    open IsAbelianGroupHelper helper
    open IsEquivalence isEquivalence

abGroupHelper : ∀ {c ℓ} → AbelianGroupHelper c ℓ → AbelianGroup c ℓ
abGroupHelper helper = record
 { Carrier = Carrier
 ; _≈_ = _≈_
 ; _∙_ = _∙_
 ; ε = ε
 ; _⁻¹ = _⁻¹
 ; isAbelianGroup = record
   { isGroup = record
     { isMonoid = record
       { isSemigroup = record
         { isMagma = record
           { isEquivalence = isEquivalence
           ; ∙-cong = ∙-cong
           }
         ; assoc = assoc
         }
       ; identity = identityˡ , (λ x → trans (comm x ε) (identityˡ x))
       }
     ; inverse = inverseˡ , (λ x → trans (comm x (x ⁻¹)) (inverseˡ x))
     ; ⁻¹-cong = ⁻¹-cong
     }
   ; comm = comm
   }
 }
  where
    open AbelianGroupHelper helper
    open IsEquivalence isEquivalence

module _ {c ℓ} (G : AbelianGroup c ℓ) where
  open AbelianGroup G

  subgroup : ∀ {p}
             → (P : Carrier → Set p)
             → (∀ x y → P x → P y → P (x ∙ y))
             → P ε
             → (∀ x → P x → P (x ⁻¹))
             → AbelianGroup (c ⊔ p) ℓ 
  subgroup P ∙-closed ε-closed ⁻¹-closed = abGroupHelper record
    { Carrier = Σ Carrier P
    ; _≈_ = λ { (x , _) (y , _) → x ≈ y } 
    ; _∙_ = λ { (x , px) (y , py) → (x ∙ y) , (∙-closed x y px py) }
    ; ε = ε , ε-closed
    ; _⁻¹ = λ { (x , px) → x ⁻¹ , ⁻¹-closed x px }
    ; isEquivalence = record
      { refl = refl
      ; sym = sym
      ; trans = trans
      }
    ; ∙-cong = ∙-cong
    ; ⁻¹-cong = ⁻¹-cong
    ; assoc = λ { (x , _) (y , _) (z , _) → assoc x y z }
    ; identityˡ = λ { (x , _) → identityˡ x }
    ; inverseˡ = λ { (x , _) → inverseˡ x }
    ; comm = λ { (x , _) (y , _) → comm x y }
    }

  -- TODO This is mono/injective
  subgroup-inj : ∀ {p}
               → {P : Carrier → Set p}
               → {∙-closed : ∀ x y → P x → P y → P (x ∙ y)}
               → {ε-closed : P ε}
               → {⁻¹-closed : ∀ x → P x → P (x ⁻¹)}
               → AbelianGroupHomomorphism (subgroup P ∙-closed ε-closed ⁻¹-closed) G
  subgroup-inj = record
    { ⟦_⟧ = proj₁
    ; cong = λ eq → eq
    ; homo = λ x y → refl
    }

-- FIXME: Finish this stuff

  -- We don't ever want these proofs about quotient equality expanding, as they cause
  -- goals to balloon in size
  -- abstract
    -- quot-refl : ∀ {x} → ⟦⟧
    -- quot-refl : ∀ {x} → Quot x x
    -- quot-refl {x = x} = quot H.ε $ begin
    --   ⟦ inj ⟧ H.ε  ≈⟨ ε-homo inj ⟩
    --   G.ε          ≈˘⟨ G.inverseʳ x ⟩
    --   x G.∙ x G.⁻¹ ∎

    -- quot-sym : ∀ {x y} → Quot x y → Quot y x
    -- quot-sym {x = x} {y = y} (quot witness element) = quot (witness H.⁻¹) $ begin
    --   ⟦ inj ⟧ (witness H.⁻¹)   ≈⟨ ⁻¹-homo inj witness ⟩
    --   ⟦ inj ⟧ witness G.⁻¹     ≈⟨ G.⁻¹-cong element ⟩
    --   (x G.∙ y G.⁻¹) G.⁻¹      ≈⟨ ⁻¹-anti-homo-∙ G x (y G.⁻¹) ⟩
    --   (y G.⁻¹) G.⁻¹ G.∙ x G.⁻¹ ≈⟨ {!!} ⟩
    --   y G.∙ x G.⁻¹ ∎

  -- quotient : AbelianGroup c (c ⊔ ℓ)
  -- quotient = abGroupHelper record
  --   { Carrier = G.Carrier
  --   ; _≈_ = Quot
  --   ; _∙_ = G._∙_
  --   ; ε = G.ε
  --   ; _⁻¹ = G._⁻¹
  --   ; isEquivalence = record
  --     { refl = {!!}
  --     ; sym = {!!}
  --     ; trans = {!!}
  --     }
  --   ; ∙-cong = {!!}
  --   ; ⁻¹-cong = {!!}
  --   ; assoc = {!!}
  --   ; identityˡ = {!!}
  --   ; inverseˡ = {!!}
  --   ; comm = {!!}
  --   }
