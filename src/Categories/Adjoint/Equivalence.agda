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

infix 5 _⊣⊢_

record _⊣⊢_ (L : Functor C D) (R : Functor D C) : Set (levelOfTerm L ⊔ levelOfTerm R) where
  field
    unit   : idF ≃ (R ∘F L)
    counit : (L ∘F R) ≃ idF

  module unit   = NaturalIsomorphism unit
  module counit = NaturalIsomorphism counit

  private
    module C = Category C
    module D = Category D
    module L = Functor L
    module R = Functor R

  field
    zig : ∀ {A : C.Obj} → counit.⇒.η (L.₀ A) D.∘ L.₁ (unit.⇒.η A) D.≈ D.id
    zag : ∀ {B : D.Obj} → R.₁ (counit.⇒.η B) C.∘ unit.⇒.η (R.₀ B) C.≈ C.id

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
        unit.⇐.η (R.₀ X) C.∘ R.₁ (counit.⇐.η X)
          ≈˘⟨ elimʳ zag ⟩
        (unit.⇐.η (R.₀ X) C.∘ R.₁ (counit.⇐.η X)) C.∘ (R.₁ (counit.⇒.η X) C.∘ unit.⇒.η (R.₀ X))
          ≈⟨ center ([ R ]-resp-∘ (counit.iso.isoˡ _) ○ R.identity) ⟩
        unit.⇐.η (R.₀ X) C.∘ C.id C.∘ unit.⇒.η (R.₀ X)
          ≈⟨ refl⟩∘⟨ C.identityˡ ⟩
        unit.⇐.η (R.₀ X) C.∘ unit.⇒.η (R.₀ X)
          ≈⟨ unit.iso.isoˡ _ ⟩
        C.id
          ∎
    ; zag    = λ {X} →
      let open D.HomReasoning
          open MR D
      in begin
        L.₁ (unit.⇐.η X) D.∘ counit.⇐.η (L.₀ X)
          ≈˘⟨ elimʳ zig ⟩
        (L.₁ (unit.⇐.η X) D.∘ counit.⇐.η (L.₀ X)) D.∘ counit.⇒.η (L.₀ X) D.∘ L.₁ (unit.⇒.η X)
          ≈⟨ center (counit.iso.isoˡ _) ⟩
        L.₁ (unit.⇐.η X) D.∘ D.id D.∘ L.₁ (unit.⇒.η X)
          ≈⟨ refl⟩∘⟨ D.identityˡ ⟩
        L.₁ (unit.⇐.η X) D.∘ L.₁ (unit.⇒.η X)
          ≈⟨ ([ L ]-resp-∘ (unit.iso.isoˡ _)) ○ L.identity ⟩
        D.id
          ∎
    }

  module R⊣L = Adjoint R⊣L

private

  record WithZig (L : Functor C D) (R : Functor D C) : Set (levelOfTerm L ⊔ levelOfTerm R) where
    field
      unit   : idF ≃ (R ∘F L)
      counit : (L ∘F R) ≃ idF
  
    module unit   = NaturalIsomorphism unit
    module counit = NaturalIsomorphism counit
  
    private
      module C = Category C
      module D = Category D
      module L = Functor L
      module R = Functor R
      module ℱ = Functor
  
    field
      zig : ∀ {A : C.Obj} → counit.⇒.η (L.₀ A) D.∘ L.₁ (unit.⇒.η A) D.≈ D.id

    zag : ∀ {B : D.Obj} → R.₁ (counit.⇒.η B) C.∘ unit.⇒.η (R.₀ B) C.≈ C.id
    zag {B} = F≃id⇒id (≃.sym unit) helper
      where open C
            open HomReasoning
            helper : R.₁ (L.₁ (R.₁ (counit.⇒.η B) ∘ unit.⇒.η (R.₀ B))) ≈ id
            helper = begin
              R.₁ (L.₁ (R.₁ (counit.⇒.η B) ∘ unit.⇒.η (R.₀ B)))             ≈⟨ ℱ.homomorphism (R ∘F L) ⟩
              R.₁ (L.₁ (R.₁ (counit.⇒.η B))) ∘ R.₁ (L.₁ (unit.⇒.η (R.₀ B))) ≈˘⟨ R.F-resp-≈ (F≃id-comm₁ counit) ⟩∘⟨refl ⟩
              R.₁ (counit.⇒.η (L.₀ (R.₀ B))) ∘ R.₁ (L.₁ (unit.⇒.η (R.₀ B))) ≈⟨ [ R ]-resp-∘ zig ⟩
              R.₁ D.id                                                      ≈⟨ R.identity ⟩
              id                                                            ∎

  record WithZag (L : Functor C D) (R : Functor D C) : Set (levelOfTerm L ⊔ levelOfTerm R) where
    field
      unit   : idF ≃ (R ∘F L)
      counit : (L ∘F R) ≃ idF
  
    module unit   = NaturalIsomorphism unit
    module counit = NaturalIsomorphism counit
  
    private
      module C = Category C
      module D = Category D
      module L = Functor L
      module R = Functor R
      module ℱ = Functor
  
    field
      zag : ∀ {B : D.Obj} → R.₁ (counit.⇒.η B) C.∘ unit.⇒.η (R.₀ B) C.≈ C.id

    zig : ∀ {A : C.Obj} → counit.⇒.η (L.₀ A) D.∘ L.₁ (unit.⇒.η A) D.≈ D.id
    zig {A} = F≃id⇒id counit helper
      where open D
            open HomReasoning
            helper : L.₁ (R.₁ (counit.⇒.η (L.₀ A) ∘ L.₁ (unit.⇒.η A))) ≈ id
            helper = begin
              L.₁ (R.₁ (counit.⇒.η (L.₀ A) ∘ L.₁ (unit.⇒.η A)))               ≈⟨ ℱ.homomorphism (L ∘F R) ⟩
              (L.₁ (R.₁ (counit.⇒.η (L.₀ A))) ∘ L.₁ (R.₁ (L.₁ (unit.⇒.η A)))) ≈˘⟨ refl⟩∘⟨ L.F-resp-≈ (F≃id-comm₂ (≃.sym unit)) ⟩
              L.₁ (R.₁ (counit.⇒.η (L.₀ A))) ∘ L.₁ (unit.⇒.η (R.₀ (L.₀ A)))   ≈⟨ [ L ]-resp-∘ zag ⟩
              L.F₁ C.id                                                       ≈⟨ L.identity ⟩
              id                                                              ∎

module _ {L : Functor C D} {R : Functor D C} where

  withZig : WithZig L R → L ⊣⊢ R
  withZig LR = record
    { unit   = unit
    ; counit = counit
    ; zig    = zig
    ; zag    = zag
    }
    where open WithZig LR

  withZag : WithZag L R → L ⊣⊢ R
  withZag LR = record
    { unit   = unit
    ; counit = counit
    ; zig    = zig
    ; zag    = zag
    }
    where open WithZag LR
