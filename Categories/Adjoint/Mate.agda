{-# OPTIONS --without-K --safe #-}

-- the usual notion of mate is defined by a square between hom set(oid)s,
-- but due to explicit universe level, a different definition is used.
module Categories.Adjoint.Mate where

open import Level
open import Data.Product using (Σ; _,_)
open import Function.Equality using (Π; _⟶_; _⇨_) renaming (_∘_ to _∙_)
open import Relation.Binary using (Setoid; IsEquivalence)

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Functor
open import Categories.Functor.Hom
open import Categories.NaturalTransformation renaming (id to idN)
open import Categories.Adjoint
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level
    C D : Category o ℓ e
    L L′ R R′ : Functor C D

record Mate {L : Functor C D}
            (L⊣R : L ⊣ R) (L′⊣R′ : L′ ⊣ R′)
            (α : NaturalTransformation L L′)
            (β : NaturalTransformation R′ R) : Set (levelOfTerm L⊣R ⊔ levelOfTerm L′⊣R′) where
  private
    module L⊣R   = Adjoint L⊣R
    module L′⊣R′ = Adjoint L′⊣R′
    module D = Category D
  
  field
    commute₁ : (R ∘ˡ α) ∘ᵥ L⊣R.unit ≃ (β ∘ʳ L′) ∘ᵥ L′⊣R′.unit
    commute₂ : L⊣R.counit ∘ᵥ L ∘ˡ β ≃ L′⊣R′.counit ∘ᵥ (α ∘ʳ R′)

record HaveMate {L L′ : Functor C D} {R R′ : Functor D C}
                (L⊣R : L ⊣ R) (L′⊣R′ : L′ ⊣ R′) : Set (levelOfTerm L⊣R ⊔ levelOfTerm L′⊣R′) where
  field
    α    : NaturalTransformation L L′
    β    : NaturalTransformation R′ R
    mate : Mate L⊣R L′⊣R′ α β

  module α = NaturalTransformation α
  module β = NaturalTransformation β
  open Mate mate public

-- show that the commutative diagram implies natural isomorphism
module _ {L L′ : Functor C D} {R R′ : Functor D C}
         {L⊣R : L ⊣ R} {L′⊣R′ : L′ ⊣ R′}
         {α : NaturalTransformation L L′}
         {β : NaturalTransformation R′ R}
         (mate : Mate L⊣R L′⊣R′ α β) where

  open Mate mate
  open Functor
  module C     = Category C
  module D     = Category D
  module α     = NaturalTransformation α
  module β     = NaturalTransformation β
  module L⊣R   = Adjoint L⊣R
  module L′⊣R′ = Adjoint L′⊣R′

  -- there are two squares to show
  module _ {X : C.Obj} {Y : D.Obj} where
    open Setoid (L′⊣R′.Hom[L-,-].F₀ (X , Y) ⇨ L⊣R.Hom[-,R-].F₀ (X , Y))
    open C hiding (_≈_)
    open MR C
    open C.HomReasoning
    module DH = D.HomReasoning

    mate-commute₁ : F₁ Hom[ C ][-,-] (C.id , β.η Y) ∙ L′⊣R′.Hom-inverse.to {X} {Y}
                  ≈ L⊣R.Hom-inverse.to {X} {Y} ∙ F₁ Hom[ D ][-,-] (α.η X , D.id)
    mate-commute₁ {f} {g} f≈g = begin
      β.η Y ∘ (F₁ R′ f ∘ L′⊣R′.unit.η X) ∘ C.id  ≈⟨ refl⟩∘⟨ identityʳ ⟩
      β.η Y ∘ F₁ R′ f ∘ L′⊣R′.unit.η X           ≈⟨ pullˡ (β.commute f) ⟩
      (F₁ R f ∘ β.η (F₀ L′ X)) ∘ L′⊣R′.unit.η X  ≈˘⟨ pushʳ commute₁ ⟩
      F₁ R f ∘ F₁ R (α.η X) ∘ L⊣R.unit.η X       ≈˘⟨ pushˡ (homomorphism R) ⟩
      F₁ R (f D.∘ α.η X) ∘ L⊣R.unit.η X          ≈⟨ F-resp-≈ R (D.∘-resp-≈ˡ f≈g DH.○ DH.⟺ D.identityˡ) ⟩∘⟨refl ⟩
      F₁ R (D.id D.∘ g D.∘ α.η X) ∘ L⊣R.unit.η X ∎

  module _ {X : C.Obj} {Y : D.Obj} where
    open Setoid (L′⊣R′.Hom[-,R-].F₀ (X , Y) ⇨ L⊣R.Hom[L-,-].F₀ (X , Y))
    open D hiding (_≈_)
    open MR D
    open D.HomReasoning
    module CH = C.HomReasoning

    mate-commute₂ : F₁ Hom[ D ][-,-] (α.η X , D.id) ∙ L′⊣R′.Hom-inverse.from {X} {Y}
                  ≈ L⊣R.Hom-inverse.from {X} {Y} ∙ F₁ Hom[ C ][-,-] (C.id , β.η Y)
    mate-commute₂ {f} {g} f≈g = begin
      D.id ∘ (L′⊣R′.counit.η Y ∘ F₁ L′ f) ∘ α.η X  ≈⟨ identityˡ ⟩
      (L′⊣R′.counit.η Y ∘ F₁ L′ f) ∘ α.η X         ≈˘⟨ pushʳ (α.commute f) ⟩
      L′⊣R′.counit.η Y ∘ α.η (F₀ R′ Y) ∘ F₁ L f    ≈˘⟨ pushˡ commute₂ ⟩
      (L⊣R.counit.η Y ∘ F₁ L (β.η Y)) ∘ F₁ L f     ≈˘⟨ pushʳ (homomorphism L) ⟩
      L⊣R.counit.η Y ∘ F₁ L (β.η Y C.∘ f)          ≈⟨ refl⟩∘⟨ F-resp-≈ L (C.∘-resp-≈ʳ (f≈g CH.○ CH.⟺ C.identityʳ)) ⟩
      L⊣R.counit.η Y ∘ F₁ L (β.η Y C.∘ g C.∘ C.id) ∎
