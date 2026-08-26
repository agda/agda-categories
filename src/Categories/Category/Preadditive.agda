{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Preadditive {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level
open import Function using (_$_)

open import Algebra.Structures
open import Algebra.Bundles
import Algebra.Properties.AbelianGroup as AbGroupₚ renaming (⁻¹-injective to -‿injective)
open import Algebra.Core

open import Categories.Morphism.Reasoning 𝒞

open Category 𝒞
open HomReasoning

private
  variable
    A B C D X : Obj
    f g h : A ⇒ B

record Preadditive : Set (o ⊔ ℓ ⊔ e) where

  infixl 7 _+_
  infixl 6 _-_
  infix  8 -_

  field
    _+_ : ∀ {A B} → Op₂ (A ⇒ B)
    0H   : ∀ {A B} → A ⇒ B
    -_ : ∀ {A B} → Op₁ (A ⇒ B)
    HomIsAbGroup : ∀ (A B : Obj) → IsAbelianGroup (_≈_ {A} {B}) _+_ 0H -_
    +-resp-∘ : ∀ {A B C D} {f g : B ⇒ C} {h : A ⇒ B} {k : C ⇒ D} → k ∘ (f + g) ∘ h ≈ (k ∘ f ∘ h) + (k ∘ g ∘ h)

  _-_ : ∀ {A B} → Op₂ (A ⇒ B)
  f - g = f + - g

  HomAbGroup : ∀ (A B : Obj) → AbelianGroup ℓ e
  HomAbGroup A B = record
    { Carrier = A ⇒ B
    ; _≈_ = _≈_
    ; _∙_ = _+_
    ; ε = 0H
    ; _⁻¹ = -_
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
  open HomAbGroupₚ public

  -------------------------------------------------------------------------------- 
  -- Reasoning Combinators

  +-elimˡ : f ≈ 0H → f + g ≈ g
  +-elimˡ {f = f} {g = g} eq = +-congʳ eq ○ +-identityˡ g

  +-introˡ : f ≈ 0H → g ≈ f + g
  +-introˡ eq = ⟺ (+-elimˡ eq)

  +-elimʳ : g ≈ 0H → f + g ≈ f
  +-elimʳ {g = g} {f = f} eq = +-congˡ eq ○ +-identityʳ f

  +-introʳ : g ≈ 0H → f ≈ f + g
  +-introʳ eq = ⟺ (+-elimʳ eq)

  --------------------------------------------------------------------------------
  -- Properties of _+_

  +-resp-∘ˡ : ∀ {f g : A ⇒ B} {h : B ⇒ C} → h ∘ (f + g) ≈ (h ∘ f) + (h ∘ g)
  +-resp-∘ˡ {f = f} {g = g} {h = h} = begin
    h ∘ (f + g)             ≈˘⟨ ∘-resp-≈ʳ identityʳ ⟩
    h ∘ (f + g) ∘ id        ≈⟨ +-resp-∘ ⟩
    h ∘ f ∘ id + h ∘ g ∘ id ≈⟨ +-cong (∘-resp-≈ʳ identityʳ) (∘-resp-≈ʳ identityʳ) ⟩
    h ∘ f + h ∘ g           ∎

  +-resp-∘ʳ : ∀ {h : A ⇒ B} {f g : B ⇒ C} → (f + g) ∘ h ≈ (f ∘ h) + (g ∘ h)
  +-resp-∘ʳ {h = h} {f = f} {g = g} = begin
    (f + g) ∘ h             ≈˘⟨ identityˡ ⟩
    id ∘ (f + g) ∘ h        ≈⟨ +-resp-∘ ⟩
    id ∘ f ∘ h + id ∘ g ∘ h ≈⟨ +-cong identityˡ identityˡ ⟩
    f ∘ h + g ∘ h           ∎

  --------------------------------------------------------------------------------
  -- Properties of 0

  0-resp-∘ : ∀ {f : C ⇒ D} {g : A ⇒ B} → f ∘ 0H {B} {C} ∘ g ≈ 0H
  0-resp-∘ {f = f} {g = g} = begin
    f ∘ 0H ∘ g                                   ≈˘⟨ +-identityʳ (f ∘ 0H ∘ g) ⟩
    (f ∘ 0H ∘ g + 0H)                            ≈˘⟨ +-congˡ (-‿inverseʳ (f ∘ 0H ∘ g)) ⟩
    (f ∘ 0H ∘ g) + ((f ∘ 0H ∘ g) - (f ∘ 0H ∘ g)) ≈˘⟨ +-assoc (f ∘ 0H ∘ g) (f ∘ 0H ∘ g) (- (f ∘ 0H ∘ g)) ⟩
    (f ∘ 0H ∘ g) + (f ∘ 0H ∘ g) - (f ∘ 0H ∘ g)   ≈˘⟨ +-congʳ +-resp-∘ ⟩
    (f ∘ (0H + 0H) ∘ g) - (f ∘ 0H ∘ g)           ≈⟨ +-congʳ (refl⟩∘⟨ +-identityʳ 0H ⟩∘⟨refl) ⟩
    (f ∘ 0H ∘ g) - (f ∘ 0H ∘ g)                  ≈⟨ -‿inverseʳ (f ∘ 0H ∘ g) ⟩
    0H                                           ∎

  0-resp-∘ˡ : ∀ {A B C} {f : A ⇒ B} → 0H ∘ f ≈ 0H {A} {C}
  0-resp-∘ˡ {f = f} = begin
    0H ∘ f      ≈˘⟨ identityˡ ⟩
    id ∘ 0H ∘ f ≈⟨ 0-resp-∘ ⟩
    0H          ∎

  0-resp-∘ʳ : f ∘ 0H ≈ 0H {A} {C}
  0-resp-∘ʳ {f = f} = begin
    f ∘ 0H      ≈˘⟨ refl⟩∘⟨ identityʳ ⟩
    f ∘ 0H ∘ id ≈⟨ 0-resp-∘ ⟩
    0H          ∎

  --------------------------------------------------------------------------------
  -- Properties of -_

  -‿resp-∘ : f ∘ (- g) ∘ h ≈ - (f ∘ g ∘ h) 
  -‿resp-∘ {f = f} {g = g} {h = h} = inverseˡ-unique (f ∘ (- g) ∘ h) (f ∘ g ∘ h) $ begin
    (f ∘ (- g) ∘ h) + (f ∘ g ∘ h) ≈˘⟨ +-resp-∘ ⟩
    f ∘ (- g + g) ∘ h             ≈⟨ refl⟩∘⟨ -‿inverseˡ g ⟩∘⟨refl ⟩
    f ∘ 0H ∘ h                    ≈⟨ 0-resp-∘ ⟩
    0H                            ∎

  -‿resp-∘ˡ : (- f) ∘ g ≈ - (f ∘ g)
  -‿resp-∘ˡ {f = f} {g = g} = begin
    (- f) ∘ g      ≈˘⟨ identityˡ ⟩
    id ∘ (- f) ∘ g ≈⟨ -‿resp-∘ ⟩
    - (id ∘ f ∘ g) ≈⟨ -‿cong identityˡ ⟩
    - (f ∘ g) ∎

  -‿resp-∘ʳ : f ∘ (- g) ≈ - (f ∘ g)
  -‿resp-∘ʳ {f = f} {g = g} = begin
    f ∘ (- g)      ≈˘⟨ refl⟩∘⟨ identityʳ ⟩
    f ∘ (- g) ∘ id ≈⟨ -‿resp-∘ ⟩
    - (f ∘ g ∘ id) ≈⟨ -‿cong (refl⟩∘⟨ identityʳ) ⟩
    - (f ∘ g) ∎

  -‿idˡ : (- id) ∘ f ≈ - f 
  -‿idˡ {f = f} = begin
    (- id) ∘ f      ≈˘⟨ identityˡ ⟩
    id ∘ (- id) ∘ f ≈⟨ -‿resp-∘ ⟩
    - (id ∘ id ∘ f) ≈⟨ -‿cong (identityˡ ○ identityˡ) ⟩
    - f             ∎

  neg-id-∘ʳ : f ∘ (- id) ≈ - f 
  neg-id-∘ʳ {f = f} = begin
    f ∘ (- id)      ≈˘⟨ refl⟩∘⟨ identityʳ ⟩
    f ∘ (- id) ∘ id ≈⟨ -‿resp-∘ ⟩
    - (f ∘ id ∘ id) ≈⟨ -‿cong (pullˡ identityʳ ○ identityʳ) ⟩
    - f             ∎

