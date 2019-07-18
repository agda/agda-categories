{-# OPTIONS --without-K --safe #-}
module Categories.NaturalTransformation.Dinatural where

open import Level
open import Data.Product

open import Categories.Category
open import Categories.NaturalTransformation as NT hiding (_∘ʳ_)
open import Categories.Functor
open import Categories.Functor.Bifunctor
open import Categories.Category.Product
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level
    C D E : Category o ℓ e

record DinaturalTransformation (F G : Bifunctor (Category.op C) C D) : Set (levelOfTerm C ⊔ levelOfTerm D) where
  private
    module C = Category C
    module D = Category D
    module F = Functor F
    module G = Functor G

  open D hiding (op)
  open HomReasoning
  open Commutation

  field
    α       : ∀ X → D [ F.F₀ (X , X) , G.F₀ (X , X) ]
    commute : ∀ {X Y} (f : C [ X , Y ]) →
                [ F.F₀ (Y , X) ⇒ G.F₀ (X , Y) ]⟨
                  F.F₁ (f , C.id)             ⇒⟨ F.F₀ (X , X) ⟩
                  α X                         ⇒⟨ G.F₀ (X , X) ⟩
                  G.F₁ (C.id , f)
                ≈ F.F₁ (C.id , f)             ⇒⟨ F.F₀ (Y , Y) ⟩
                  α Y                         ⇒⟨ G.F₀ (Y , Y) ⟩
                  G.F₁ (f , C.id)
                ⟩

  op : DinaturalTransformation G.op F.op
  op = record
    { α       = α
    ; commute = λ f → assoc ○ ⟺ (commute f) ○ ⟺ assoc
    }

module _ {F G H : Bifunctor (Category.op C) C D} where
  private
    module C = Category C
  open Category D
  open HomReasoning
  open Functor
  open MR D

  infixr 9 _<∘_
  infixl 9 _∘>_

  _<∘_ : NaturalTransformation G H → DinaturalTransformation F G → DinaturalTransformation F H
  θ <∘ β = record
    { α       = λ X → η (X , X) ∘ α X
    ; commute = λ {X Y} f → begin
      F₁ H (C.id , f) ∘ (η (X , X) ∘ α X) ∘ F₁ F (f , C.id)   ≈˘⟨ pushˡ (pushˡ (θ.commute (C.id , f))) ⟩
      ((η (X , Y) ∘ F₁ G (C.id , f)) ∘ α X) ∘ F₁ F (f , C.id) ≈⟨ assoc ○ pullʳ (β.commute f) ⟩
      η (X , Y) ∘ F₁ G (f , C.id) ∘ α Y ∘ F₁ F (C.id , f)     ≈⟨ pullˡ (θ.commute (f , C.id)) ○ pullʳ (⟺ assoc) ⟩
      F₁ H (f , C.id) ∘ (η (Y , Y) ∘ α Y) ∘ F₁ F (C.id , f)   ∎
    }
    where module θ = NaturalTransformation θ
          module β = DinaturalTransformation β
          open θ
          open β

  _∘>_ : DinaturalTransformation G H → NaturalTransformation F G → DinaturalTransformation F H
  β ∘> θ = record
    { α       = λ X → α X ∘ η (X , X)
    ; commute = λ {X Y} f → begin
      F₁ H (C.id , f) ∘ (α X ∘ η (X , X)) ∘ F₁ F (f , C.id) ≈⟨ refl⟩∘⟨ pullʳ (θ.commute (f , C.id)) ⟩
      F₁ H (C.id , f) ∘ α X ∘ F₁ G (f , C.id) ∘ η (Y , X)   ≈˘⟨ assoc ○ ∘-resp-≈ʳ assoc ⟩
      (F₁ H (C.id , f) ∘ α X ∘ F₁ G (f , C.id)) ∘ η (Y , X) ≈⟨ β.commute f ⟩∘⟨refl ⟩
      (F₁ H (f , C.id) ∘ α Y ∘ F₁ G (C.id , f)) ∘ η (Y , X) ≈˘⟨ pushʳ (assoc ○ pushʳ (θ.commute (C.id , f))) ⟩
      F₁ H (f , C.id) ∘ (α Y ∘ η (Y , Y)) ∘ F₁ F (C.id , f) ∎
    }
    where module θ = NaturalTransformation θ
          module β = DinaturalTransformation β
          open θ
          open β

module _ {F G : Bifunctor (Category.op C) C D} where
  private
    module C = Category C
  open Category D
  open HomReasoning
  open Functor
  open MR D

  infixl 9 _∘ʳ_

  _∘ʳ_ : ∀ {E : Category o ℓ e} →
           DinaturalTransformation F G → (K : Functor E C) → DinaturalTransformation (F ∘F ((Functor.op K) ⁂ K)) (G ∘F ((Functor.op K) ⁂ K))
  _∘ʳ_ {E = E} β K = record
    { α       = λ X → α (F₀ K X)
    ; commute = λ {X Y} f → begin
      F₁ G (F₁ K E.id , F₁ K f) ∘ α (F₀ K X) ∘ F₁ F (F₁ K f , F₁ K E.id)
        ≈⟨ F-resp-≈ G (identity K , C.Equiv.refl) ⟩∘⟨ refl ⟩∘⟨ F-resp-≈ F (C.Equiv.refl , identity K) ⟩
      F₁ G (C.id , F₁ K f) ∘ α (F₀ K X) ∘ F₁ F (F₁ K f , C.id)
        ≈⟨ commute (F₁ K f) ⟩
      F₁ G (F₁ K f , C.id) ∘ α (F₀ K Y) ∘ F₁ F (C.id , F₁ K f)
        ≈˘⟨ F-resp-≈ G (C.Equiv.refl , identity K) ⟩∘⟨ refl ⟩∘⟨ F-resp-≈ F (identity K , C.Equiv.refl) ⟩
      F₁ G (F₁ K f , F₁ K E.id) ∘ α (F₀ K Y) ∘ F₁ F (F₁ K E.id , F₁ K f)
        ∎
    }
    where module β = DinaturalTransformation β
          module E = Category E
          open β
          
