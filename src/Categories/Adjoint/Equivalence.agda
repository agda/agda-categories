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
    o ℓ e    : Level
    o′ ℓ′ e′ : Level
    C D E    : Category o ℓ e

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

  op₁ : R.op ⊣⊢ L.op
  op₁ = record
    { unit   = counit.op
    ; counit = unit.op
    ; zig    = zag
    ; zag    = zig
    }

  zag⁻¹ : {B : D.Obj} → unit.⇐.η (R.F₀ B) C.∘ R.F₁ (counit.⇐.η B) C.≈ C.id
  zag⁻¹ {B} = begin
    unit.⇐.η (R.₀ B) C.∘ R.₁ (counit.⇐.η B)   ≈˘⟨ flip-fromʳ unit.FX≅GX zag ⟩∘⟨refl ⟩
    R.₁ (counit.⇒.η B) C.∘ R.₁ (counit.⇐.η B) ≈⟨ [ R ]-resp-∘ (counit.iso.isoʳ B) ⟩
    R.₁ D.id                                  ≈⟨ R.identity ⟩
    C.id                                      ∎
    where open C.HomReasoning
          open MR C

  zig⁻¹ : {A : C.Obj} → L.F₁ (unit.⇐.η A) D.∘ counit.⇐.η (L.F₀ A) D.≈ D.id
  zig⁻¹ {A} = begin
      L.₁ (unit.⇐.η A) D.∘ counit.⇐.η (L.₀ A) ≈˘⟨ refl⟩∘⟨ flip-fromˡ counit.FX≅GX zig ⟩
      L.₁ (unit.⇐.η A) D.∘ L.₁ (unit.⇒.η A)   ≈⟨ [ L ]-resp-∘ (unit.iso.isoˡ A) ⟩
      L.₁ C.id                                ≈⟨ L.identity ⟩
      D.id                                    ∎
      where open D.HomReasoning
            open MR D

  op₂ : R ⊣⊢ L
  op₂ = record
    { unit   = ≃.sym counit
    ; counit = ≃.sym unit
    ; zig    = zag⁻¹
    ; zag    = zig⁻¹
    }

  L⊣R : L ⊣ R
  L⊣R = record
    { unit   = unit.F⇒G
    ; counit = counit.F⇒G
    ; zig    = zig
    ; zag    = zag
    }

  module L⊣R = Adjoint L⊣R
  open L⊣R hiding (unit; counit; zig; zag; op) public

  R⊣L : R ⊣ L
  R⊣L = record
    { unit   = counit.F⇐G
    ; counit = unit.F⇐G
    ; zig    = zag⁻¹
    ; zag    = zig⁻¹
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

id⊣⊢id : idF {C = C} ⊣⊢ idF
id⊣⊢id {C = C} = record
  { unit   = ≃.sym ≃.unitor²
  ; counit = ≃.unitor²
  ; zig    = identity²
  ; zag    = identity²
  }
  where open Category C

record ⊣Equivalence (C : Category o ℓ e) (D : Category o′ ℓ′ e′) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  field
    L    : Functor C D
    R    : Functor D C
    L⊣⊢R : L ⊣⊢ R

  module L    = Functor L
  module R    = Functor R
  module L⊣⊢R = _⊣⊢_ L⊣⊢R

  open L⊣⊢R public

refl : ⊣Equivalence C C
refl = record
  { L    = idF
  ; R    = idF
  ; L⊣⊢R = id⊣⊢id
  }

sym : ⊣Equivalence C D → ⊣Equivalence D C
sym e = record
  { L    = R
  ; R    = L
  ; L⊣⊢R = op₂
  }
  where open ⊣Equivalence e

-- trans : ⊣Equivalence C D → ⊣Equivalence D E → ⊣Equivalence C E
-- trans e e′ = record
--   { L    = e′.L ∘F e.L
--   ; R    = e.R ∘F e′.R
--   ; L⊣⊢R = {!!}
--   }
--   where module e  = ⊣Equivalence e
--         module e′ = ⊣Equivalence e′
