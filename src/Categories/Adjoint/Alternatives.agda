{-# OPTIONS --without-K --safe #-}

module Categories.Adjoint.Alternatives where

open import Level

open import Categories.Adjoint
open import Categories.Category
open import Categories.Functor renaming (id to idF)
open import Categories.NaturalTransformation

import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level
    C D   : Category o ℓ e

  record FromUnit (L : Functor C D) (R : Functor D C) : Set (levelOfTerm L ⊔ levelOfTerm R) where
    private
      module C = Category C
      module D = Category D
      module L = Functor L
      module R = Functor R

    field
      unit : NaturalTransformation idF (R ∘F L)

    module unit = NaturalTransformation unit

    field
      θ       : ∀ {X Y} → C [ X , R.₀ Y ] → D [ L.₀ X , Y ]
      commute : ∀ {X Y} (g : C [ X , R.₀ Y ]) → g C.≈ R.₁ (θ g) C.∘ unit.η X
      unique  : ∀ {X Y} {f : D [ L.₀ X , Y ]} {g : C [ X , R.₀ Y ]} →
                  g C.≈ R.₁ f C.∘ unit.η X → θ g D.≈ f

    module _ where
      open C.HomReasoning
      open MR C

      θ-natural : ∀ {X Y Z} (f : D [ Y , Z ]) (g : C [ X , R.₀ Y ]) → θ (R.₁ f C.∘ g) D.≈ θ (R.₁ f) D.∘ L.₁ g
      θ-natural {X} {Y} f g = unique eq
        where eq : R.₁ f C.∘ g C.≈ R.₁ (θ (R.₁ f) D.∘ L.₁ g) C.∘ unit.η X
              eq = begin
                R.₁ f C.∘ g                                      ≈⟨ commute (R.₁ f) ⟩∘⟨refl ⟩
                (R.₁ (θ (R.₁ f)) C.∘ unit.η (R.F₀ Y)) C.∘ g    ≈⟨ C.assoc ⟩
                R.₁ (θ (R.₁ f)) C.∘ unit.η (R.₀ Y) C.∘ g       ≈⟨ pushʳ (unit.commute g) ⟩
                (R.₁ (θ (R.₁ f)) C.∘ R.₁ (L.₁ g)) C.∘ unit.η X ≈˘⟨ R.homomorphism ⟩∘⟨refl ⟩
                R.₁ (θ (R.₁ f) D.∘ L.₁ g) C.∘ unit.η X         ∎
  
      θ-cong : ∀ {X Y} {f g : C [ X , R.₀ Y ]} → f C.≈ g → θ f D.≈ θ g
      θ-cong eq = unique (eq ○ commute _)

    θ-natural′ : ∀ {X Y} (g : C [ X , R.₀ Y ]) → θ g D.≈ θ C.id D.∘ L.₁ g
    θ-natural′ g = θ-cong (introˡ R.identity) ○ θ-natural D.id g ○ D.∘-resp-≈ˡ (θ-cong R.identity)
      where open D.HomReasoning
            open MR C

    counit : NaturalTransformation (L ∘F R) idF
    counit = ntHelper record
      { η       = λ d → θ C.id
      ; commute = λ f → begin
        θ C.id D.∘ L.₁ (R.₁ f) ≈˘⟨ θ-natural′ (R.₁ f) ⟩
        θ (R.₁ f)              ≈⟨ unique (CH.⟺ (MR.cancelʳ C (CH.⟺ (commute C.id))) CH.○ CH.⟺ (C.∘-resp-≈ˡ R.homomorphism)) ⟩
        f D.∘ θ C.id           ∎
      }
      where open D.HomReasoning
            module CH = C.HomReasoning

    unique′ : ∀ {X Y} {f g : D [ L.₀ X , Y ]} (h : C [ X , R.₀ Y ]) →
                h C.≈ R.₁ f C.∘ unit.η X →
                h C.≈ R.₁ g C.∘ unit.η X → f D.≈ g
    unique′ _ eq₁ eq₂ = ⟺ (unique eq₁) ○ unique eq₂
      where open D.HomReasoning

    zig : ∀ {A} → θ C.id D.∘ L.F₁ (unit.η A) D.≈ D.id
    zig {A} = unique′ (unit.η A)
                      (commute (unit.η A) ○ (C.∘-resp-≈ˡ (R.F-resp-≈ (θ-natural′ (unit.η A)))))
                      (introˡ R.identity)
      where open C.HomReasoning
            open MR C

fromUnit : ∀ {L : Functor C D} {R : Functor D C} → FromUnit L R → L ⊣ R
fromUnit {C = C} {D = D} {L} {R} L⊣R = record
  { unit   = unit
  ; counit = counit
  ; zig    = zig
  ; zag    = C.Equiv.sym (commute C.id)
  }
  where module C = Category C
        module D = Category D
        module L = Functor L
        module R = Functor R
        open FromUnit L⊣R
