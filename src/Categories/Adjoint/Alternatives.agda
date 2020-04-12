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

  module _ (L : Functor C D) (R : Functor D C) where
    private
      module C = Category C
      module D = Category D
      module L = Functor L
      module R = Functor R

    record FromUnit : Set (levelOfTerm L ⊔ levelOfTerm R) where
  
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

      L⊣R : L ⊣ R
      L⊣R = record
        { unit   = unit
        ; counit = counit
        ; zig    = zig
        ; zag    = C.Equiv.sym (commute C.id)
        }

    record FromCounit : Set (levelOfTerm L ⊔ levelOfTerm R) where
  
      field
        counit : NaturalTransformation (L ∘F R) idF
  
      module counit = NaturalTransformation counit
  
      field
        θ       : ∀ {X Y} → D [ L.₀ X , Y ] → C [ X , R.₀ Y ]
        commute : ∀ {X Y} (g : D [ L.₀ X , Y ]) → g D.≈ counit.η Y D.∘ L.₁ (θ g)
        unique  : ∀ {X Y} {f : C [ X , R.₀ Y ]} {g : D [ L.₀ X , Y ]} →
                    g D.≈ counit.η Y D.∘ L.₁ f → θ g C.≈ f

      module _ where
        open D.HomReasoning
        open MR D
  
        θ-natural : ∀ {X Y Z} (f : C [ X , Y ]) (g : D [ L.₀ Y , Z ]) → θ (g D.∘ L.₁ f) C.≈ R.₁ g C.∘ θ (L.₁ f)
        θ-natural {X} {Y} {Z} f g = unique eq
          where eq : g D.∘ L.₁ f D.≈ counit.η Z D.∘ L.₁ (R.₁ g C.∘ θ (L.₁ f))
                eq = begin
                  g D.∘ L.₁ f                                     ≈⟨ pushʳ (commute (L.₁ f)) ⟩
                  (g D.∘ counit.η (L.F₀ Y)) D.∘ L.F₁ (θ (L.F₁ f)) ≈⟨ pushˡ (counit.sym-commute g) ⟩
                  counit.η Z D.∘ L.₁ (R.₁ g) D.∘ L.₁ (θ (L.₁ f))  ≈˘⟨ refl⟩∘⟨ L.homomorphism ⟩
                  counit.η Z D.∘ L.₁ (R.₁ g C.∘ θ (L.₁ f))        ∎
    
        θ-cong : ∀ {X Y} {f g : D [ L.₀ X , Y ]} → f D.≈ g → θ f C.≈ θ g
        θ-cong eq = unique (eq ○ commute _)
  
      θ-natural′ : ∀ {X Y} (g : D [ L.₀ X , Y ]) → θ g C.≈ R.₁ g C.∘ θ D.id
      θ-natural′ g = θ-cong (introʳ L.identity) ○ θ-natural C.id g ○ C.∘-resp-≈ʳ (θ-cong L.identity)
        where open C.HomReasoning
              open MR D

      unit : NaturalTransformation idF (R ∘F L)
      unit = ntHelper record
        { η       = λ _ → θ D.id
        ; commute = λ f → begin
          θ D.id C.∘ f           ≈˘⟨ unique (DH.⟺ (cancelˡ (DH.⟺ (commute D.id))) DH.○ D.∘-resp-≈ʳ (DH.⟺ L.homomorphism)) ⟩
          θ (L.₁ f)              ≈⟨ θ-natural′ (L.₁ f) ⟩
          R.₁ (L.₁ f) C.∘ θ D.id ∎
        }
        where open C.HomReasoning
              module DH = D.HomReasoning
              open MR D
        
      unique′ : ∀ {X Y} {f g : C [ X , R.₀ Y ]} (h : D [ L.₀ X , Y ]) →
                  h D.≈ counit.η Y D.∘ L.₁ f →
                  h D.≈ counit.η Y D.∘ L.₁ g →
                  f C.≈ g
      unique′ _ eq₁ eq₂ = ⟺ (unique eq₁) ○ unique eq₂
        where open C.HomReasoning
      
      zag : ∀ {B} → R.F₁ (counit.η B) C.∘ θ D.id C.≈ C.id
      zag {B} = unique′ (counit.η B)
                        (⟺ (cancelʳ (⟺ (commute D.id))) ○ pushˡ (counit.sym-commute (counit.η B)) ○ D.∘-resp-≈ʳ (⟺ L.homomorphism))
                        (introʳ L.identity)
        where open D.HomReasoning
              open MR D

      L⊣R : L ⊣ R
      L⊣R = record
        { unit   = unit
        ; counit = counit
        ; zig    = D.Equiv.sym (commute D.id)
        ; zag    = zag
        }

module _ {L : Functor C D} {R : Functor D C} where

  fromUnit : FromUnit L R → L ⊣ R
  fromUnit = FromUnit.L⊣R
  
  fromCounit : FromCounit L R → L ⊣ R
  fromCounit = FromCounit.L⊣R
