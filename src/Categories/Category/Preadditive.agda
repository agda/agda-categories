{-# OPTIONS --without-K --safe #-}

module Categories.Category.Preadditive where

open import Level

open import Algebra.Structures
open import Algebra.Bundles
import Algebra.Properties.AbelianGroup as AbGroupₚ renaming (⁻¹-injective to -‿injective)
open import Algebra.Core

open import Categories.Category

import Categories.Morphism.Reasoning as MR

record Preadditive {o ℓ e} (𝒞 : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  open Category 𝒞
  open HomReasoning
  open MR 𝒞

  infixl 7 _+_

  field
    _+_ : ∀ {A B} → Op₂ (A ⇒ B)
    0H   : ∀ {A B} → A ⇒ B
    neg : ∀ {A B} → Op₁ (A ⇒ B)
    HomIsAbGroup : ∀ (A B : Obj) → IsAbelianGroup (_≈_ {A} {B}) _+_ 0H neg
    +-resp-∘ : ∀ {A B C D} {f g : B ⇒ C} {h : A ⇒ B} {k : C ⇒ D} → k ∘ (f + g) ∘ h ≈ (k ∘ f ∘ h) + (k ∘ g ∘ h)

  HomAbGroup : ∀ (A B : Obj) → AbelianGroup ℓ e
  HomAbGroup A B = record
    { Carrier = A ⇒ B
    ; _≈_ = _≈_
    ; _∙_ = _+_
    ; ε = 0H
    ; _⁻¹ = neg
    ; isAbelianGroup = HomIsAbGroup A B
    }

  module HomAbGroup {A B : Obj} = IsAbelianGroup (HomIsAbGroup A B)
    using ()
    renaming
    (assoc to +-assoc
    ; identityˡ to +-identityˡ
    ; identityʳ to +-identityʳ
    ; inverseˡ to -‿inverseˡ
    ; inverseʳ to -‿inverseʳ
    ; comm to +-comm
    ; ∙-cong to +-cong
    ; ∙-congˡ to +-congˡ
    ; ∙-congʳ to +-congʳ
    ; ⁻¹-cong to -‿cong
    )
  module HomAbGroupₚ {A B : Obj} = AbGroupₚ (HomAbGroup A B)

  open HomAbGroup public

  +-resp-∘ˡ : ∀ {A B C} {f g : A ⇒ B} {h : B ⇒ C} → h ∘ (f + g) ≈ (h ∘ f) + (h ∘ g)
  +-resp-∘ˡ {f = f} {g = g} {h = h} = begin
    h ∘ (f + g)             ≈˘⟨ ∘-resp-≈ʳ identityʳ ⟩
    h ∘ (f + g) ∘ id        ≈⟨ +-resp-∘ ⟩
    h ∘ f ∘ id + h ∘ g ∘ id ≈⟨ +-cong (∘-resp-≈ʳ identityʳ) (∘-resp-≈ʳ identityʳ) ⟩
    h ∘ f + h ∘ g           ∎

  +-resp-∘ʳ : ∀ {A B C} {h : A ⇒ B} {f g : B ⇒ C} → (f + g) ∘ h ≈ (f ∘ h) + (g ∘ h)
  +-resp-∘ʳ {h = h} {f = f} {g = g} = begin
    (f + g) ∘ h             ≈˘⟨ identityˡ ⟩
    id ∘ (f + g) ∘ h        ≈⟨ +-resp-∘ ⟩
    id ∘ f ∘ h + id ∘ g ∘ h ≈⟨ +-cong identityˡ identityˡ ⟩
    f ∘ h + g ∘ h ∎

  0-resp-∘ : ∀ {A B C} {f : B ⇒ C} {g : A ⇒ B} → f ∘ 0H ∘ g ≈ 0H
  0-resp-∘ {f = f} {g = g} = begin
    f ∘ 0H ∘ g                                       ≈˘⟨ +-identityʳ (f ∘ 0H ∘ g) ⟩
    (f ∘ 0H ∘ g + 0H)                                ≈˘⟨ +-congˡ (-‿inverseʳ (f ∘ 0H ∘ g)) ⟩
    (f ∘ 0H ∘ g) + ((f ∘ 0H ∘ g) + neg (f ∘ 0H ∘ g)) ≈˘⟨ +-assoc (f ∘ 0H ∘ g) (f ∘ 0H ∘ g) (neg (f ∘ 0H ∘ g)) ⟩
    (f ∘ 0H ∘ g) + (f ∘ 0H ∘ g) + neg (f ∘ 0H ∘ g)   ≈˘⟨ +-congʳ +-resp-∘ ⟩
    (f ∘ (0H + 0H) ∘ g) + neg (f ∘ 0H ∘ g)           ≈⟨ +-congʳ (refl⟩∘⟨ +-identityʳ 0H ⟩∘⟨refl) ⟩
    (f ∘ 0H ∘ g) + neg (f ∘ 0H ∘ g)                  ≈⟨ -‿inverseʳ (f ∘ 0H ∘ g) ⟩
    0H ∎

  0-resp-∘ˡ : ∀ {A B} {f : A ⇒ B} → 0H ∘ f ≈ 0H {A} {B}
  0-resp-∘ˡ {f = f} = begin
    0H ∘ f      ≈˘⟨ identityˡ ⟩
    id ∘ 0H ∘ f ≈⟨ 0-resp-∘ ⟩
    0H ∎

  0-resp-∘ʳ : ∀ {A B} {f : A ⇒ B} → f ∘ 0H ≈ 0H {A} {B}
  0-resp-∘ʳ {f = f} = begin
    f ∘ 0H      ≈˘⟨ ∘-resp-≈ʳ identityʳ ⟩
    f ∘ 0H ∘ id ≈⟨ 0-resp-∘  ⟩
    0H ∎
