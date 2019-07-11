{-# OPTIONS --without-K --safe #-}
module Categories.NaturalTransformation.Dinatural where

open import Level
open import Data.Product

open import Categories.Category
open import Categories.NaturalTransformation as NT hiding (_∘ʳ_)
open import Categories.Functor
open import Categories.Functor.Bifunctor
open import Categories.Category.Product
import Categories.Square as Square

private
  variable
    o ℓ e : Level
    C D E : Category o ℓ e
    F G H : Bifunctor (Category.op C) C D

record DinaturalTransformation (F G : Bifunctor (Category.op C) C D) : Set (levelOf C ⊔ levelOf D) where
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


-- https://github.com/agda/agda/issues/3912

-- _<∘_ : NaturalTransformation G H → DinaturalTransformation F G → DinaturalTransformation F H
-- _<∘_ = {!!}

-- _∘>_ : DinaturalTransformation G H → NT.NaturalTransformation F G → DinaturalTransformation F H
-- _∘>_ = {!!}

-- _∘ʳ_ : DinaturalTransformation F G → (K : Functor E C) → DinaturalTransformation (F ∘F ((Functor.op K) ⁂ K)) (G ∘F ((Functor.op K) ⁂ K))
-- _∘ʳ_ = {!!}
