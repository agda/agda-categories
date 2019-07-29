module Categories.Category.Instance.FamilyOfSets where

-- The Category of "Families of Sets"
open import Level
open import Relation.Binary using (Rel)
open import Data.Product
open import Relation.Binary.PropositionalEquality as ≡
open import Function renaming (id to idf; _∘_ to _⊚_)
import Relation.Binary.Reasoning.Setoid as SetoidR

open import Categories.Category

module _ {a b : Level} where
  record Fam : Set (suc a ⊔ suc b) where
      field
        U : Set a
        T : U → Set b
  open Fam public

  record Hom (A B : Fam) : Set (a ⊔ b) where
    field
      f : U A → U B
      φ : (x : U A) → T A x → T B (f x)

  record _≡Fam_ {X Y} (f g : (Hom X Y)) : Set (a ⊔ b) where
      field
        f≡g : {x : _} → Hom.f f x ≡ Hom.f g x
        φ≡γ : {x : _} {bx : _} → Hom.φ f x bx ≡ subst (T Y) (sym (f≡g {x})) (Hom.φ g x bx)

  module Eq = _≡Fam_

  Cat : Category (suc a ⊔ suc b) (a ⊔ b) (a ⊔ b)
  Cat = record
    { Obj = Fam
    ; _⇒_ = Hom
    ; _≈_ = _≡Fam_
    ; id = record { f = idf ; φ = λ _ → idf }
    ; _∘_ = λ H I → record { f = Hom.f H ⊚ Hom.f I ; φ = λ ua → Hom.φ H (Hom.f I ua) ⊚ Hom.φ I ua }
    ; assoc = record { f≡g = refl ; φ≡γ = refl }
    ; identityˡ = record { f≡g = refl ; φ≡γ = refl }
    ; identityʳ = record { f≡g = refl ; φ≡γ = refl }
    ; equiv = λ {A} {B} → record
      { refl = record { f≡g = refl ; φ≡γ = refl }
      ; sym = λ {i} {j} i≡j → record
        { f≡g = sym (Eq.f≡g i≡j)
        ; φ≡γ = λ {x} {bx} →
          let open SetoidR (setoid (T B (Hom.f j x) )) in
          let eq = sym (Eq.f≡g i≡j) in begin
          Hom.φ j x bx                                          ≈⟨ sym (subst-sym-subst eq) ⟩
          subst (T B) (sym eq) (subst (T B) eq (Hom.φ j x bx))  ≈⟨ cong (subst (T B) (sym eq)) (sym (Eq.φ≡γ i≡j)) ⟩
          subst (T B) (sym eq) (Hom.φ i x bx) ∎
        }
      ; trans = λ {i} {j} {k} i≡j j≡k → record
        { f≡g = trans (Eq.f≡g i≡j) (Eq.f≡g j≡k)
        ; φ≡γ = λ {x} {bx} →
          let eq₁ = Eq.f≡g i≡j in
          let eq₂ = Eq.f≡g j≡k in
          let eq₃ = Eq.φ≡γ i≡j in
          let y = Hom.φ i x bx in
          let z = Hom.φ j x bx in
          let w = Hom.φ k x bx in
          let open SetoidR (setoid (T B (Hom.f i _))) in
          begin
          y                                               ≈⟨ eq₃ ⟩
          subst (T B) (sym eq₁) z                         ≈⟨ cong (subst (T B) (sym eq₁)) (Eq.φ≡γ j≡k) ⟩
          subst (T B) (sym eq₁) (subst (T B) (sym eq₂) w) ≈⟨ subst-subst (sym eq₂) ⟩
          subst (T B) (trans (sym eq₂) (sym eq₁)) w       ≈⟨ cong (λ z → subst (T B) z w) (trans-sym-comm eq₂ eq₁) ⟩
          subst (T B) (sym (trans eq₁ eq₂)) w  ∎
        }
      }
    ; ∘-resp-≈ = λ {A} {B} {C} {ff} {hh} {g} {i} f≡h g≡i → record
      { f≡g = trans (Eq.f≡g f≡h) (cong (Hom.f hh) (Eq.f≡g g≡i))
      ; φ≡γ = λ {x} {bx} →
        let eq₁ = Eq.f≡g f≡h in
        let eq₂ = Eq.f≡g g≡i in
        let eq₃ = Eq.φ≡γ f≡h in
        let eq₄ = Eq.φ≡γ g≡i in
        let y = Hom.φ i x bx in
        let z = Hom.φ g x bx in
        let ix = Hom.f i x in
        let gx = Hom.f g x in
        let φgx = Hom.φ g x bx in
        let φhy = Hom.φ hh ix y in
        let ST₁ {z} x = subst (T C) (sym (eq₁ {z})) x in
        let ST₂ {z} x = subst (T B) (sym (eq₂ {z})) x in
        let open SetoidR (setoid (T C _)) in
        begin
        Hom.φ ff (Hom.f g x) z                                        ≈⟨ eq₃ {gx} {φgx} ⟩
        ST₁ (Hom.φ hh gx φgx)                                         ≈⟨ cong (λ q → ST₁ (Hom.φ hh gx q)) eq₄ ⟩
        ST₁ (Hom.φ hh gx (ST₂ y))                                     ≈⟨ cong ST₁ (subst-app (T B) (Hom.φ hh) (sym eq₂)) ⟩
        ST₁ (subst (T C) (cong (Hom.f hh) (sym eq₂)) φhy)             ≈⟨ subst-subst (cong (Hom.f hh) (sym eq₂)) ⟩
        subst (T C) (trans (cong (Hom.f hh) (sym eq₂)) (sym eq₁)) φhy ≈⟨ cong (λ z → subst (T C) (trans z (sym eq₁)) φhy) (cong-sym-comm eq₂) ⟩
        subst (T C) (trans (sym (cong (Hom.f hh) eq₂)) (sym eq₁)) φhy ≈⟨ cong (λ z → subst (T C) z φhy) (trans-sym-comm (cong (Hom.f hh) eq₂) eq₁) ⟩
        subst (T C) (sym (trans eq₁ (cong (Hom.f hh) eq₂))) φhy       ∎

      }
    }
    where
      -- this stuff needs to be moved out of here, and likely into stdlib
      trans-sym-comm : {z : Level} {Z : Set z} {a b c : Z} (eq₁ : b ≡ a) (eq₂ : c ≡ b)
        → trans (sym eq₁) (sym eq₂) ≡ sym (trans eq₂ eq₁)
      trans-sym-comm refl refl = refl
      cong-sym-comm : {a b : Level} {A : Set a} {B : Set b} {f : A → B} {x y : A} (eq : x ≡ y) → cong f (sym eq) ≡ sym (cong f eq)
      cong-sym-comm refl = refl
      -- this is almost like subst-application from stdlib
      subst-app : ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂}
                    (B₁ : A₁ → Set b₁) {B₂ : A₂ → Set b₂}
                    {f : A₁ → A₂} {x₁ x₂ : A₁} {y : B₁ x₁}
                    (g : ∀ x → B₁ x → B₂ (f x)) (eq : x₁ ≡ x₂) →
                    g x₂ (subst B₁ eq y) ≡ subst B₂ (cong f eq) (g x₁ y)
      subst-app _ _ refl = refl

  open Category Cat public

FamilyOfSets : ∀ a b → Category (suc a ⊔ suc b) (a ⊔ b) (a ⊔ b)
FamilyOfSets a b = Cat {a} {b}
