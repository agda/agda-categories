{-# OPTIONS --without-K --safe #-}

module Categories.Adjoint.TwoSided.Compose where

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
    o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ : Level

_∘⊣⊢_ : {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {E : Category o″ ℓ″ e″}
        {L : Functor C D} {R : Functor D C} {L′ : Functor D E} {R′ : Functor E D}
        (L⊣⊢R : L ⊣⊢ R) (L′⊣⊢R′ : L′ ⊣⊢ R′) → (L′ ∘F L) ⊣⊢ (R ∘F R′)
_∘⊣⊢_ {C = C} {D} {E} {L} {R} {L′} {R′} L⊣⊢R L′⊣⊢R′ = withZig record
  { unit   = unit
  ; counit = counit
  ; zig    = zig
  }
  where
  private
    module C   = Category C using (_∘_; id; assoc; identityˡ; module HomReasoning)
    module D   = Category D using (id)
    module E   = Category E using (_∘_; id; _≈_; assoc; identityˡ; module HomReasoning)
    module L   = Functor L using (₀; ₁)
    module R   = Functor R using (₀; ₁; identity)
    module L′  = Functor L′ using (₀; ₁; identity)
    module R′  = Functor R′ using (₀; ₁)
    module ⊣⊢₁ = _⊣⊢_ L⊣⊢R using (zig; module unit; module counit)
    module ⊣⊢₂ = _⊣⊢_ L′⊣⊢R′ using (zig; module unit; module counit)

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

    module unit = NaturalIsomorphism unit using (module ⇒)

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

    module counit = NaturalIsomorphism counit using (module ⇒)

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
