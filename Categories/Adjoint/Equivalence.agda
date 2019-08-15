{-# OPTIONS --without-K --safe #-}

module Categories.Adjoint.Equivalence where

open import Level

open import Categories.Adjoint
open import Categories.Category
open import Categories.Functor renaming (id to idF)
open import Categories.NaturalTransformation.NaturalIsomorphism as ≃ using (_≃_; NaturalIsomorphism)
open import Categories.NaturalTransformation.NaturalIsomorphism.Properties

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

  open Adjoint L⊣R hiding (unit; counit; zig; zag) public

