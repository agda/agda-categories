{-# OPTIONS --without-K --safe #-}

module Categories.Adjoint.Equivalence where

open import Level

open import Categories.Adjoint
open import Categories.Category
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Properties
open import Categories.NaturalTransformation.NaturalIsomorphism as ≃ using (_≃_; NaturalIsomorphism)
open import Categories.NaturalTransformation.NaturalIsomorphism.Properties
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level
    C D E : Category o ℓ e

record ⊣Equivalence (L : Functor C D) (R : Functor D C) : Set (levelOfTerm L ⊔ levelOfTerm R) where
  field
    unit   : idF ≃ (R ∘F L)
    counit : (L ∘F R) ≃ idF

  module unit = NaturalIsomorphism unit
  module counit = NaturalIsomorphism counit

  private
    module C = Category C
    module D = Category D
    module L = Functor L
    module R = Functor R
    module ℱ = Functor

  field
    zig : ∀ {A : C.Obj} → counit.⇒.η (L.F₀ A) D.∘ L.F₁ (unit.⇒.η A) D.≈ D.id

  zag : ∀ {B : D.Obj} → R.F₁ (counit.⇒.η B) C.∘ unit.⇒.η (R.F₀ B) C.≈ C.id
  zag {B} = F≃id⇒id (≃.sym unit) helper
    where open C
          open HomReasoning
          helper : R.F₁ (L.F₁ (R.F₁ (counit.⇒.η B) ∘ unit.⇒.η (R.F₀ B))) ≈ id
          helper = begin
            R.F₁ (L.F₁ (R.F₁ (counit.⇒.η B) ∘ unit.⇒.η (R.F₀ B)))               ≈⟨ ℱ.homomorphism (R ∘F L) ⟩
            R.F₁ (L.F₁ (R.F₁ (counit.⇒.η B))) ∘ R.F₁ (L.F₁ (unit.⇒.η (R.F₀ B))) ≈˘⟨ R.F-resp-≈ (F≃id-comm₁ counit) ⟩∘⟨refl ⟩
            R.F₁ (counit.⇒.η (L.F₀ (R.F₀ B))) ∘ R.F₁ (L.F₁ (unit.⇒.η (R.F₀ B))) ≈˘⟨ R.homomorphism ⟩
            R.F₁ (counit.⇒.η (L.F₀ (R.F₀ B)) D.∘ L.F₁ (unit.⇒.η (R.F₀ B)))      ≈⟨ R.F-resp-≈ zig ⟩
            R.F₁ D.id                                                           ≈⟨ R.identity ⟩
            id                                                                  ∎

  L⊣R : L ⊣ R
  L⊣R = record
    { unit   = unit.F⇒G
    ; counit = counit.F⇒G
    ; zig    = zig
    ; zag    = zag
    }

  module L⊣R = Adjoint L⊣R
  open L⊣R hiding (unit; counit; zig; zag) public

  R⊣L : R ⊣ L
  R⊣L = record
    { unit   = counit.F⇐G
    ; counit = unit.F⇐G
    ; zig    = λ {X} →
      let open C.HomReasoning
          open MR C
      in begin
        unit.⇐.η (R.F₀ X) C.∘ R.F₁ (counit.⇐.η X)
          ≈˘⟨ elimʳ zag ⟩
        (unit.⇐.η (R.F₀ X) C.∘ R.F₁ (counit.⇐.η X)) C.∘ (R.F₁ (counit.⇒.η X) C.∘ unit.⇒.η (R.F₀ X))
          ≈⟨ center ([ R ]-resp-∘ (counit.iso.isoˡ _) ○ R.identity) ⟩
        unit.⇐.η (R.F₀ X) C.∘ C.id C.∘ unit.⇒.η (R.F₀ X)
          ≈⟨ refl⟩∘⟨ C.identityˡ ⟩
        unit.⇐.η (R.F₀ X) C.∘ unit.⇒.η (R.F₀ X)
          ≈⟨ unit.iso.isoˡ _ ⟩
        C.id
          ∎
    ; zag    = λ {X} →
      let open D.HomReasoning
          open MR D
      in begin
        L.F₁ (unit.⇐.η X) D.∘ counit.⇐.η (L.F₀ X)
          ≈˘⟨ elimʳ zig ⟩
        (L.F₁ (unit.⇐.η X) D.∘ counit.⇐.η (L.F₀ X)) D.∘ counit.⇒.η (L.F₀ X) D.∘ L.F₁ (unit.⇒.η X)
          ≈⟨ center (counit.iso.isoˡ _) ⟩
        L.F₁ (unit.⇐.η X) D.∘ D.id D.∘ L.F₁ (unit.⇒.η X)
          ≈⟨ refl⟩∘⟨ D.identityˡ ⟩
        L.F₁ (unit.⇐.η X) D.∘ L.F₁ (unit.⇒.η X)
          ≈⟨ ([ L ]-resp-∘ (unit.iso.isoˡ _)) ○ L.identity ⟩
        D.id
          ∎
    }

  module R⊣L = Adjoint R⊣L
