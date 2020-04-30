{-# OPTIONS --without-K --safe #-}

module Categories.Adjoint.Equivalence where

open import Level

open import Categories.Adjoint
open import Categories.Adjoint.TwoSided
open import Categories.Category.Core using (Category)
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Properties
open import Categories.NaturalTransformation using (ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism as ≃ using (_≃_; NaturalIsomorphism)
open import Categories.NaturalTransformation.NaturalIsomorphism.Properties
import Categories.Morphism.Reasoning as MR

open import Relation.Binary using (Setoid; IsEquivalence)

private
  variable
    o ℓ e o′ ℓ′ e′ : Level
    C D E    : Category o ℓ e

id⊣⊢id : idF {C = C} ⊣⊢ idF
id⊣⊢id {C = C} = record
  { unit   = ≃.sym ≃.unitor²
  ; counit = ≃.unitor²
  ; zig    = identity²
  ; zag    = identity²
  }
  where open Category C

module _ {L : Functor C D} {R : Functor D C} {L′ : Functor D E} {R′ : Functor E D}
         (L⊣⊢R : L ⊣⊢ R) (L′⊣⊢R′ : L′ ⊣⊢ R′) where
  private
    module C   = Category C
    module D   = Category D
    module E   = Category E
    module L   = Functor L
    module R   = Functor R
    module L′  = Functor L′
    module R′  = Functor R′
    module ⊣⊢₁ = _⊣⊢_ L⊣⊢R
    module ⊣⊢₂ = _⊣⊢_ L′⊣⊢R′

    unit : idF ≃ (R ∘F R′) ∘F L′ ∘F L
    unit = record
      { F⇒G = ntHelper record
        { η       = λ c → R.₁ (⊣⊢₂.unit.⇒.η (L.₀ c)) ∘ ⊣⊢₁.unit.⇒.η c
        ; commute = λ {x} {y} f → begin
          (R.₁ (⊣⊢₂.unit.⇒.η (L.₀ y)) ∘ ⊣⊢₁.unit.⇒.η y) ∘ f
            ≈⟨ pullʳ (⊣⊢₁.unit.⇒.commute f) ⟩
          R.₁ (⊣⊢₂.unit.⇒.η (L.₀ y)) ∘ R.₁ (L.₁ f) ∘ ⊣⊢₁.unit.⇒.η x
            ≈⟨ pullˡ ([ R ]-resp-square (⊣⊢₂.unit.⇒.commute (L.₁ f))) ⟩
          (R.₁ (R′.₁ (L′.₁ (L.₁ f))) ∘ R.₁ (⊣⊢₂.unit.⇒.η (L.₀ x))) ∘ ⊣⊢₁.unit.⇒.η x
            ≈⟨ assoc ⟩
          R.₁ (R′.₁ (L′.₁ (L.₁ f))) ∘ R.₁ (⊣⊢₂.unit.⇒.η (L.₀ x)) ∘ ⊣⊢₁.unit.⇒.η x
            ∎
        }
      ; F⇐G = ntHelper record
        { η       = λ c → ⊣⊢₁.unit.⇐.η c ∘ R.₁ (⊣⊢₂.unit.⇐.η (L.₀ c))
        ; commute = λ {x} {y} f → begin
          (⊣⊢₁.unit.⇐.η y ∘ R.₁ (⊣⊢₂.unit.⇐.η (L.₀ y))) ∘ R.₁ (R′.₁ (L′.₁ (L.₁ f)))
            ≈⟨ pullʳ ([ R ]-resp-square (⊣⊢₂.unit.⇐.commute (L.₁ f))) ⟩
          ⊣⊢₁.unit.⇐.η y ∘ R.₁ (L.₁ f) ∘ R.₁ (⊣⊢₂.unit.⇐.η (L.₀ x))
            ≈⟨ pullˡ (⊣⊢₁.unit.⇐.commute f) ⟩
          (f ∘ ⊣⊢₁.unit.⇐.η x) ∘ R.₁ (⊣⊢₂.unit.⇐.η (L.₀ x))
            ≈⟨ assoc ⟩
          f ∘ ⊣⊢₁.unit.⇐.η x ∘ R.₁ (⊣⊢₂.unit.⇐.η (L.₀ x))
            ∎
        }
      ; iso = λ c → record
        { isoˡ = begin
          (⊣⊢₁.unit.⇐.η c ∘ R.₁ (⊣⊢₂.unit.⇐.η (L.₀ c))) ∘ R.₁ (⊣⊢₂.unit.⇒.η (L.₀ c)) ∘ ⊣⊢₁.unit.⇒.η c
            ≈⟨ center ([ R ]-resp-∘ (⊣⊢₂.unit.iso.isoˡ (L.₀ c))) ⟩
          ⊣⊢₁.unit.⇐.η c ∘ R.₁ D.id ∘ ⊣⊢₁.unit.⇒.η c
            ≈⟨ refl⟩∘⟨ elimˡ R.identity ⟩
          ⊣⊢₁.unit.⇐.η c ∘ ⊣⊢₁.unit.⇒.η c
            ≈⟨ ⊣⊢₁.unit.iso.isoˡ c ⟩
          id
            ∎
        ; isoʳ = begin
          (R.₁ (⊣⊢₂.unit.⇒.η (L.₀ c)) ∘ ⊣⊢₁.unit.⇒.η c) ∘ ⊣⊢₁.unit.⇐.η c ∘ R.₁ (⊣⊢₂.unit.⇐.η (L.₀ c))
            ≈⟨ center (⊣⊢₁.unit.iso.isoʳ c) ⟩
          R.₁ (⊣⊢₂.unit.⇒.η (L.₀ c)) ∘ id ∘ R.₁ (⊣⊢₂.unit.⇐.η (L.₀ c))
            ≈⟨ refl⟩∘⟨ identityˡ ⟩
          R.₁ (⊣⊢₂.unit.⇒.η (L.₀ c)) ∘ R.₁ (⊣⊢₂.unit.⇐.η (L.₀ c))
            ≈⟨ [ R ]-resp-∘ (⊣⊢₂.unit.iso.isoʳ (L.₀ c)) ⟩
          R.₁ D.id
            ≈⟨ R.identity ⟩
          id
            ∎
        }
      }
      where open C
            open HomReasoning
            open MR C

    module unit = NaturalIsomorphism unit

    counit : (L′ ∘F L) ∘F R ∘F R′ ≃ idF
    counit = record
      { F⇒G = ntHelper record
        { η       = λ e → ⊣⊢₂.counit.⇒.η e ∘ L′.₁ (⊣⊢₁.counit.⇒.η (R′.₀ e))
        ; commute = λ {x} {y} f → begin
          (⊣⊢₂.counit.⇒.η y ∘ L′.₁ (⊣⊢₁.counit.⇒.η (R′.₀ y))) ∘ L′.₁ (L.₁ (R.₁ (R′.₁ f)))
            ≈⟨ pullʳ ([ L′ ]-resp-square (⊣⊢₁.counit.⇒.commute (R′.₁ f))) ⟩
          ⊣⊢₂.counit.⇒.η y ∘ L′.₁ (R′.₁ f) ∘ L′.₁ (⊣⊢₁.counit.⇒.η (R′.₀ x))
            ≈⟨ pullˡ (⊣⊢₂.counit.⇒.commute f) ⟩
          (f ∘ ⊣⊢₂.counit.⇒.η x) ∘ L′.₁ (⊣⊢₁.counit.⇒.η (R′.₀ x))
            ≈⟨ assoc ⟩
          f ∘ ⊣⊢₂.counit.⇒.η x ∘ L′.₁ (⊣⊢₁.counit.⇒.η (R′.₀ x))
            ∎
        }
      ; F⇐G = ntHelper record
        { η       = λ e → L′.₁ (⊣⊢₁.counit.⇐.η (R′.₀ e)) ∘ ⊣⊢₂.counit.⇐.η e
        ; commute = λ {x} {y} f → begin
          (L′.₁ (⊣⊢₁.counit.⇐.η (R′.₀ y)) ∘ ⊣⊢₂.counit.⇐.η y) ∘ f
            ≈⟨ pullʳ (⊣⊢₂.counit.⇐.commute f) ⟩
          L′.₁ (⊣⊢₁.counit.⇐.η (R′.₀ y)) ∘ L′.₁ (R′.₁ f) ∘ ⊣⊢₂.counit.⇐.η x
            ≈⟨ pullˡ ([ L′ ]-resp-square (⊣⊢₁.counit.⇐.commute (R′.₁ f))) ⟩
          (L′.₁ (L.₁ (R.₁ (R′.₁ f))) ∘ L′.₁ (⊣⊢₁.counit.⇐.η (R′.₀ x))) ∘ ⊣⊢₂.counit.⇐.η x
            ≈⟨ assoc ⟩
          L′.₁ (L.₁ (R.₁ (R′.₁ f))) ∘ L′.₁ (⊣⊢₁.counit.⇐.η (R′.₀ x)) ∘ ⊣⊢₂.counit.⇐.η x
            ∎
        }
      ; iso = λ e → record
        { isoˡ = begin
          (L′.₁ (⊣⊢₁.counit.⇐.η (R′.₀ e)) ∘ ⊣⊢₂.counit.⇐.η e) ∘ ⊣⊢₂.counit.⇒.η e ∘ L′.₁ (⊣⊢₁.counit.⇒.η (R′.₀ e))
            ≈⟨ center (⊣⊢₂.counit.iso.isoˡ e) ⟩
          L′.₁ (⊣⊢₁.counit.⇐.η (R′.₀ e)) ∘ id ∘ L′.₁ (⊣⊢₁.counit.⇒.η (R′.₀ e))
            ≈⟨ refl⟩∘⟨ identityˡ ⟩
          L′.₁ (⊣⊢₁.counit.⇐.η (R′.₀ e)) ∘ L′.₁ (⊣⊢₁.counit.⇒.η (R′.₀ e))
            ≈⟨ [ L′ ]-resp-∘ (⊣⊢₁.counit.iso.isoˡ (R′.₀ e)) ⟩
          L′.₁ D.id
            ≈⟨ L′.identity ⟩
          id
            ∎
        ; isoʳ = begin
          (⊣⊢₂.counit.⇒.η e ∘ L′.₁ (⊣⊢₁.counit.⇒.η (R′.₀ e))) ∘ L′.₁ (⊣⊢₁.counit.⇐.η (R′.₀ e)) ∘ ⊣⊢₂.counit.⇐.η e
            ≈⟨ center ([ L′ ]-resp-∘ (⊣⊢₁.counit.iso.isoʳ (R′.₀ e))) ⟩
          ⊣⊢₂.counit.⇒.η e ∘ L′.₁ D.id ∘ ⊣⊢₂.counit.⇐.η e
            ≈⟨ refl⟩∘⟨ elimˡ L′.identity ⟩
          ⊣⊢₂.counit.⇒.η e ∘ ⊣⊢₂.counit.⇐.η e
            ≈⟨ ⊣⊢₂.counit.iso.isoʳ e ⟩
          id
            ∎
        }
      }
      where open E
            open HomReasoning
            open MR E

    module counit = NaturalIsomorphism counit

    zig : ∀ {c} → counit.⇒.η (L′.₀ (L.₀ c)) E.∘ L′.₁ (L.₁ (unit.⇒.η c)) E.≈ E.id
    zig {c} = begin
      counit.⇒.η (L′.₀ (L.₀ c)) ∘ L′.₁ (L.₁ (unit.⇒.η c))
        ≈⟨ refl⟩∘⟨ Functor.homomorphism (L′ ∘F L) ⟩
      counit.⇒.η (L′.₀ (L.₀ c)) ∘ L′.₁ (L.₁ (R.₁ (⊣⊢₂.unit.⇒.η (L.₀ c)))) ∘ L′.₁ (L.₁ (⊣⊢₁.unit.⇒.η c))
        ≈⟨ center ([ L′ ]-resp-square (⊣⊢₁.counit.⇒.commute (⊣⊢₂.unit.⇒.η (L.₀ c)))) ⟩
      ⊣⊢₂.counit.⇒.η (L′.₀ (L.₀ c)) ∘ (L′.₁ (⊣⊢₂.unit.⇒.η (L.₀ c)) ∘ L′.₁ (⊣⊢₁.counit.⇒.η (L.₀ c))) ∘ L′.₁ (L.₁ (⊣⊢₁.unit.⇒.η c))
        ≈⟨ pull-first ⊣⊢₂.zig ⟩
      id ∘ L′.₁ (⊣⊢₁.counit.⇒.η (L.₀ c)) ∘ L′.₁ (L.₁ (⊣⊢₁.unit.⇒.η c))
        ≈⟨ elimʳ (([ L′ ]-resp-∘ ⊣⊢₁.zig) ○ L′.identity) ⟩
      id
        ∎
      where open E
            open HomReasoning
            open MR E

  _∘⊣⊢_ : (L′ ∘F L) ⊣⊢ (R ∘F R′)
  _∘⊣⊢_ = withZig record
    { unit   = unit
    ; counit = counit
    ; zig    = zig
    }

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

trans : ⊣Equivalence C D → ⊣Equivalence D E → ⊣Equivalence C E
trans e e′ = record
  { L    = e′.L ∘F e.L
  ; R    = e.R ∘F e′.R
  ; L⊣⊢R = e.L⊣⊢R ∘⊣⊢ e′.L⊣⊢R
  }
  where module e  = ⊣Equivalence e
        module e′ = ⊣Equivalence e′

isEquivalence : ∀ {o ℓ e} → IsEquivalence (⊣Equivalence {o} {ℓ} {e})
isEquivalence = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }

setoid : ∀ o ℓ e → Setoid _ _
setoid o ℓ e = record
  { Carrier       = Category o ℓ e
  ; _≈_           = ⊣Equivalence
  ; isEquivalence = isEquivalence
  }
