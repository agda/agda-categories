{-# OPTIONS --without-K --safe #-}

-- the usual notion of mate is defined by two isomorphisms between hom set(oid)s are natural,
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
open import Categories.NaturalTransformation.Equivalence using (_≃_)
open import Categories.Adjoint
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level
    C D : Category o ℓ e
    L L′ R R′ : Functor C D


-- this notion of mate can be seen in MacLane in which this notion is shown equivalent to the
-- definition via naturally isomorphic hom setoids.
record Mate {L : Functor C D}
            (L⊣R : L ⊣ R) (L′⊣R′ : L′ ⊣ R′)
            (α : NaturalTransformation L L′)
            (β : NaturalTransformation R′ R) : Set (levelOfTerm L⊣R ⊔ levelOfTerm L′⊣R′) where
  private
    module L⊣R   = Adjoint L⊣R
    module L′⊣R′ = Adjoint L′⊣R′
    module C = Category C
    module D = Category D

  field
    commute₁ : (R ∘ˡ α) ∘ᵥ L⊣R.unit ≃ (β ∘ʳ L′) ∘ᵥ L′⊣R′.unit
    commute₂ : L⊣R.counit ∘ᵥ L ∘ˡ β ≃ L′⊣R′.counit ∘ᵥ (α ∘ʳ R′)

  -- there are two equivalent commutative diagram
  open NaturalTransformation renaming (commute to η-commute)
  open Functor
  module _ where
    open D
    open HomReasoning
    open MR D

    commute₃ : ∀ {X} → L⊣R.counit.η (F₀ L′ X) ∘ F₁ L (η β (F₀ L′ X)) ∘ F₁ L (L′⊣R′.unit.η X) ≈ η α X
    commute₃ {X} = begin
      L⊣R.counit.η (F₀ L′ X) ∘ F₁ L (η β (F₀ L′ X)) ∘ F₁ L (L′⊣R′.unit.η X)
        ≈˘⟨ refl⟩∘⟨ homomorphism L ⟩
      L⊣R.counit.η (F₀ L′ X) ∘ F₁ L (η β (F₀ L′ X) C.∘ L′⊣R′.unit.η X)
        ≈˘⟨ refl⟩∘⟨ F-resp-≈ L commute₁ ⟩
      L⊣R.counit.η (F₀ L′ X) ∘ F₁ L (F₁ R (η α X) C.∘ L⊣R.unit.η X)
        ≈⟨ L⊣R.RLadjunct≈id ⟩
      η α X
        ∎

  module _ where
    open C
    open HomReasoning
    open MR C

    commute₄ : ∀ {X} → F₁ R (L′⊣R′.counit.η X) ∘ F₁ R (η α (F₀ R′ X)) ∘ L⊣R.unit.η (F₀ R′ X) ≈ η β X
    commute₄ {X} = begin
      F₁ R (L′⊣R′.counit.η X) ∘ F₁ R (η α (F₀ R′ X)) ∘ L⊣R.unit.η (F₀ R′ X)
        ≈˘⟨ pushˡ (homomorphism R) ⟩
      F₁ R (L′⊣R′.counit.η X D.∘ η α (F₀ R′ X)) ∘ L⊣R.unit.η (F₀ R′ X)
        ≈˘⟨ F-resp-≈ R commute₂ ⟩∘⟨refl ⟩
      F₁ R (L⊣R.counit.η X D.∘ F₁ L (η β X)) ∘ L⊣R.unit.η (F₀ R′ X)
        ≈⟨ L⊣R.LRadjunct≈id ⟩
      η β X
         ∎

record HaveMate {L L′ : Functor C D} {R R′ : Functor D C}
                (L⊣R : L ⊣ R) (L′⊣R′ : L′ ⊣ R′) : Set (levelOfTerm L⊣R ⊔ levelOfTerm L′⊣R′) where
  field
    α    : NaturalTransformation L L′
    β    : NaturalTransformation R′ R
    mate : Mate L⊣R L′⊣R′ α β

  module α = NaturalTransformation α
  module β = NaturalTransformation β
  open Mate mate public

-- show that the commutative diagram implies natural isomorphism between homsetoids.
-- the problem is that two homsetoids live in two universe level, in a situation similar to the definition
-- of adjoint via naturally isomorphic homsetoids.
module _ {L L′ : Functor C D} {R R′ : Functor D C}
         {L⊣R : L ⊣ R} {L′⊣R′ : L′ ⊣ R′}
         {α : NaturalTransformation L L′}
         {β : NaturalTransformation R′ R}
         (mate : Mate L⊣R L′⊣R′ α β) where
  private
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

-- alternatively, if commute₃ and commute₄ are shown, then a Mate can be constructed.

module _ {L L′ : Functor C D} {R R′ : Functor D C}
         {L⊣R : L ⊣ R} {L′⊣R′ : L′ ⊣ R′}
         {α : NaturalTransformation L L′}
         {β : NaturalTransformation R′ R} where
  private
    open Functor
    module C     = Category C
    module D     = Category D
    module α     = NaturalTransformation α
    module β     = NaturalTransformation β
    module L⊣R   = Adjoint L⊣R
    module L′⊣R′ = Adjoint L′⊣R′

  module _ (commute₃ : ∀ {X} → L⊣R.counit.η (F₀ L′ X) D.∘ F₁ L (β.η (F₀ L′ X)) D.∘ F₁ L (L′⊣R′.unit.η X) D.≈ α.η X) where
    open C
    open HomReasoning

    commute₁ : ∀ {X} → F₁ R (α.η X) ∘ L⊣R.unit.η X ≈ β.η (F₀ L′ X) ∘ L′⊣R′.unit.η X
    commute₁ {X} = begin
      F₁ R (α.η X) ∘ L⊣R.unit.η X
        ≈˘⟨ F-resp-≈ R commute₃ ⟩∘⟨refl ⟩
      F₁ R (L⊣R.counit.η (F₀ L′ X) D.∘ F₁ L (β.η (F₀ L′ X)) D.∘ F₁ L (L′⊣R′.unit.η X)) ∘ L⊣R.unit.η X
        ≈˘⟨ F-resp-≈ R (D.∘-resp-≈ʳ (homomorphism L)) ⟩∘⟨refl ⟩
      F₁ R (L⊣R.counit.η (F₀ L′ X) D.∘ F₁ L (β.η (F₀ L′ X) ∘ L′⊣R′.unit.η X)) ∘ L⊣R.unit.η X
        ≈⟨ L⊣R.LRadjunct≈id ⟩
      β.η (F₀ L′ X) ∘ L′⊣R′.unit.η X
        ∎

  module _ (commute₄ : ∀ {X} → F₁ R (L′⊣R′.counit.η X) C.∘ F₁ R (α.η (F₀ R′ X)) C.∘ L⊣R.unit.η (F₀ R′ X) C.≈ β.η X) where
    open D
    open HomReasoning
    open MR C

    commute₂ : ∀ {X} → L⊣R.counit.η X ∘ F₁ L (β.η X) ≈ L′⊣R′.counit.η X ∘ α.η (F₀ R′ X)
    commute₂ {X} = begin
      L⊣R.counit.η X ∘ F₁ L (β.η X)
        ≈˘⟨ refl⟩∘⟨ F-resp-≈ L commute₄ ⟩
      L⊣R.counit.η X ∘ F₁ L (F₁ R (L′⊣R′.counit.η X) C.∘ F₁ R (α.η (F₀ R′ X)) C.∘ L⊣R.unit.η (F₀ R′ X))
        ≈˘⟨ refl⟩∘⟨ F-resp-≈ L (pushˡ (homomorphism R)) ⟩
      L⊣R.counit.η X ∘ F₁ L (F₁ R (L′⊣R′.counit.η X ∘ α.η (F₀ R′ X)) C.∘ L⊣R.unit.η (F₀ R′ X))
        ≈⟨ L⊣R.RLadjunct≈id ⟩
      L′⊣R′.counit.η X ∘ α.η (F₀ R′ X)
        ∎


  mate′ : (∀ {X} → L⊣R.counit.η (F₀ L′ X) D.∘ F₁ L (β.η (F₀ L′ X)) D.∘ F₁ L (L′⊣R′.unit.η X) D.≈ α.η X) →
          (∀ {X} → F₁ R (L′⊣R′.counit.η X) C.∘ F₁ R (α.η (F₀ R′ X)) C.∘ L⊣R.unit.η (F₀ R′ X) C.≈ β.η X) →
          Mate L⊣R L′⊣R′ α β
  mate′ commute₃ commute₄ = record
    { commute₁ = commute₁ commute₃
    ; commute₂ = commute₂ commute₄
    }
