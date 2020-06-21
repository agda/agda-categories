{-# OPTIONS --without-K --safe #-}
module Categories.Category.Instance.FamilyOfSetoids where

-- The Category of "Families of Setoids"
-- This fits into this library much better than the Families of Sets

-- This particular formalization should be considered alpha, i.e. its
-- names will change once things settle.

open import Level
open import Relation.Binary
  using (Rel; Setoid; module Setoid; Reflexive; Symmetric; Transitive)
open import Function.Base renaming (id to idf; _∘_ to _⊚_)
open import Function.Equality
open import Function.Inverse using (_InverseOf_)
import Relation.Binary.Reasoning.Setoid as SetoidR

open import Categories.Category

module _ {a b c d : Level} where
  record Fam : Set (suc (a ⊔ b ⊔ c ⊔ d)) where
    constructor fam
    open Setoid using () renaming (Carrier to ∣_∣; _≈_ to _≈≈_)
    field
      U : Setoid a b
    open Setoid U hiding (Carrier)
    field
      T : ∣ U ∣ → Setoid c d
      reindex : {x y : ∣ U ∣} (P : x ≈ y) → T y ⟶ T x

      -- the following coherence laws are needed to make _≃_ below an equivalence
      reindex-refl : {x : ∣ U ∣} {bx : ∣ T x ∣} → _≈≈_ (T x) (reindex refl ⟨$⟩ bx) bx
      reindex-sym : {x y : ∣ U ∣} → (p : x ≈ y) → (reindex (sym p)) InverseOf (reindex p)
      reindex-trans : {x y z : ∣ U ∣} {b : ∣ T z ∣} → (p : x ≈ y) → (q : y ≈ z) →
        Setoid._≈_ (T x) (reindex (trans p q) ⟨$⟩ b)
                         (reindex p ∘ reindex q ⟨$⟩ b)
  open Fam


  record Hom (B B′ : Fam) : Set (a ⊔ b ⊔ c ⊔ d) where
    constructor fhom
    open Setoid (U B) using (_≈_)
    field
      map : U B ⟶ U B′
      transport : (x : Setoid.Carrier (U B)) → T B x ⟶ T B′ (map ⟨$⟩ x)
      transport-coh : {x y : Setoid.Carrier (U B)} → (p : x ≈ y) →
        Setoid._≈_ (T B y ⇨ T B′ (map ⟨$⟩ x))
          (transport x ∘ reindex B p)
          (reindex B′ (Π.cong map p) ∘ transport y)

  record _≈≈_ {X Y} (F F′ : (Hom X Y)) : Set (a ⊔ b ⊔ c ⊔ d) where
    constructor feq
    open Hom
    open Setoid (U X) renaming (Carrier to A) hiding (refl; _≈_)
    open Setoid (U Y)
    -- the order below is chosen to simplify some of the later reasoning
    field
      g≈f : {x : A} → map F ⟨$⟩ x ≈ map F′ ⟨$⟩ x
      φ≈γ : {x : A} → let C = T X x
                          D = T Y (map F ⟨$⟩ x) in
            {bx : Setoid.Carrier C} → Setoid._≈_ D ((reindex Y g≈f ∘ transport F′ x) ⟨$⟩ bx) (transport F x ⟨$⟩ bx)

  fam-id : {A : Fam} → Hom A A
  fam-id {A} = fhom id (λ _ → id) λ p x≈y → Π.cong (reindex A p) x≈y
  comp : {A B C : Fam} → Hom B C → Hom A B → Hom A C
  comp {B = B} {C} (fhom map₀ trans₀ coh₀) (fhom map₁ trans₁ coh₁) =
    fhom (map₀ ∘ map₁) (λ x → trans₀ (map₁ ⟨$⟩ x) ∘ (trans₁ x))
         λ {a} {b} p {x} {y} x≈y →
           let open Setoid (T C (map₀ ∘ map₁ ⟨$⟩ a)) renaming (trans to _⟨≈⟩_) in
           Π.cong (trans₀ (map₁ ⟨$⟩ a)) (coh₁ p x≈y) ⟨≈⟩
           coh₀ (Π.cong map₁ p) (Setoid.refl (T B (map₁ ⟨$⟩ b)))

  ≈≈-refl : ∀ {A B} → Reflexive (_≈≈_ {A} {B})
  ≈≈-refl {B = B} = feq refl (reindex-refl B)
    where open Setoid (U B)

  ≈≈-sym : ∀ {A B} → Symmetric (_≈≈_ {A} {B})
  ≈≈-sym {A} {B} {F} {G} (feq g≈f φ≈γ) = feq (sym g≈f)
    λ {x} {bx} → Setoid.trans ( T B (map G ⟨$⟩ x) )
      (Π.cong (reindex B (sym g≈f)) (Setoid.sym (T B (map F ⟨$⟩ x)) φ≈γ))
      (left-inverse-of (reindex-sym B g≈f) (transport G x ⟨$⟩ bx))
    where
    open Setoid (U B) using (sym; Carrier)
    open Hom
    open _InverseOf_

  ≈≈-trans : ∀ {A B} → Transitive (_≈≈_ {A} {B})
  ≈≈-trans {A} {B} {F} {G} {H}  (feq ≈₁ t₁) (feq ≈₂ t₂) =
    feq (trans ≈₁ ≈₂) (λ {x} {bx} →
      let open Setoid (T B (Hom.map F ⟨$⟩ x)) renaming (trans to _⟨≈⟩_) in
      reindex-trans B ≈₁ ≈₂ ⟨≈⟩ (Π.cong (reindex B ≈₁) t₂ ⟨≈⟩ t₁))
    where
    open Setoid (U B) using (trans)

  comp-resp-≈≈ : {A B C : Fam} {f h : Hom B C} {g i : Hom A B} →
      f ≈≈ h → g ≈≈ i → comp f g ≈≈ comp h i
  comp-resp-≈≈ {A} {B} {C} {f} {h} {g} {i} (feq f≈h t-f≈h) (feq g≈i t-g≈i) =
    feq (trans (Π.cong (map f) g≈i) f≈h)
        λ {x} → let open Setoid (T C (map (comp f g) ⟨$⟩ x)) renaming (trans to _⟨≈⟩_; sym to ≈sym) in
        reindex-trans C (cong (map f) g≈i) f≈h ⟨≈⟩
        (Π.cong (reindex C (cong (map f) g≈i)) t-f≈h ⟨≈⟩
        (≈sym (transport-coh {B} {C} f g≈i (Setoid.refl (T B (map i ⟨$⟩ x)))) ⟨≈⟩
        Π.cong (transport f (map g ⟨$⟩ x)) t-g≈i))
    where
    open _≈≈_
    open Setoid (U C)
    open Hom

  Cat : Category (suc (a ⊔ b ⊔ c ⊔ d)) (a ⊔ b ⊔ c ⊔ d) (a ⊔ b ⊔ c ⊔ d)
  Cat = record
    { Obj = Fam
    ; _⇒_ = Hom
    ; _≈_ = _≈≈_
    ; id = fam-id
    ; _∘_ = comp
    ; assoc     = λ {_} {_} {_} {_} {f} {g} {h} → assoc′ {f = f} {g} {h}
    ; sym-assoc = λ {_} {_} {_} {_} {f} {g} {h} → ≈≈-sym (assoc′ {f = f} {g} {h})
    ; identityˡ = λ {_} {B} → feq (Setoid.refl (U B)) (reindex-refl B)
    ; identityʳ = λ {_} {B} → feq (Setoid.refl (U B)) (reindex-refl B)
    ; identity² = λ {A} → feq (Setoid.refl (U A)) (reindex-refl A)
    ; equiv = λ {A} {B} → let open Setoid (U B) in record
      { refl = ≈≈-refl
      ; sym = ≈≈-sym
      ; trans = ≈≈-trans
      }
    ; ∘-resp-≈ = comp-resp-≈≈
    }
    where
    open _InverseOf_
    assoc′ : {A B C D : Fam} {f : Hom A B} {g : Hom B C} {h : Hom C D} →
      comp (comp h g) f ≈≈ comp h (comp g f)
    assoc′ {D = D} = feq (Setoid.refl (U D)) (reindex-refl D)

  open Category Cat public

FamilyOfSetoids : ∀ a b c d → Category (suc (a ⊔ b ⊔ c ⊔ d)) (a ⊔ b ⊔ c ⊔ d) (a ⊔ b ⊔ c ⊔ d)
FamilyOfSetoids a b c d = Cat {a} {b} {c} {d}
