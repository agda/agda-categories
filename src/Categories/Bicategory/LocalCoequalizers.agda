{-# OPTIONS --without-K --safe #-}

open import Categories.Bicategory

module Categories.Bicategory.LocalCoequalizers {o ℓ e t} (𝒞 : Bicategory o ℓ e t)  where

open import Categories.Diagram.Coequalizer
open import Level
open import Categories.Functor.Properties
import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞
open import Categories.Functor

postCompFunc : {A B C : Obj} → B ⇒₁ C → Functor (hom A B) (hom A C)
postCompFunc = _⊚-

preCompFunc : {A B C : Obj} → A ⇒₁ B → Functor (hom B C) (hom A C)
preCompFunc = -⊚_

record LocalCoequalizers : Set (o ⊔ ℓ ⊔ e ⊔ t) where
  field
    localCoequalizers : (A B : Obj) → Coequalizers (hom A B)
    precompPreservesCoequalizer : {A B C : Obj} → (f : A ⇒₁ B)
      → PreservesCoequalizers (preCompFunc {A} {B} {C} f)
    postcompPreservesCoequalizer : {A B C : Obj} → (f : B ⇒₁ C)
      → PreservesCoequalizers (postCompFunc {A} {B} {C} f)
      
  precompCoequalizer : {A B C : Obj} → {X Y : B ⇒₁ C} {α β : X ⇒₂ Y}
                                   → Coequalizer (hom B C) α β
                                   → (f : A ⇒₁ B)
                                   → Coequalizer (hom A C) (α ◁ f) (β ◁ f)
  precompCoequalizer coeq f = record
    { obj = Coequalizer.obj coeq ∘₁ f
    ; arr = Coequalizer.arr coeq ◁ f
    ; isCoequalizer = precompPreservesCoequalizer f {coeq = coeq}
    }

  postcompCoequalizer : {A B C : Obj} → {X Y : A ⇒₁ B} {α β : X ⇒₂ Y}
                                   → Coequalizer (hom A B) α β
                                   → (f : B ⇒₁ C)
                                   → Coequalizer (hom A C) (f ▷ α) (f ▷ β)
  postcompCoequalizer coeq f = record
    { obj = f ∘₁ Coequalizer.obj coeq
    ; arr = f ▷ Coequalizer.arr coeq
    ; isCoequalizer = postcompPreservesCoequalizer f {coeq = coeq}
    }
