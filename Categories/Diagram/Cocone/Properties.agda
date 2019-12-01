{-# OPTIONS --without-K --safe #-}

module Categories.Diagram.Cocone.Properties where

open import Level

open import Categories.Category
open import Categories.Functor
open import Categories.Functor.Properties
open import Categories.NaturalTransformation
open import Categories.Diagram.Cone.Properties
open import Categories.Diagram.Duality

import Categories.Diagram.Cocone as Coc
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level
    C D J : Category o ℓ e

module _ {F : Functor J C} (G : Functor C D) where
  private
    module C = Category C
    module D = Category D
    module F = Functor F
    module G = Functor G
    module CF = Coc F
    GF = G ∘F F
    module CGF = Coc GF

  F-map-Cocone : CF.Cocone → CGF.Cocone
  F-map-Cocone K = record
    { coapex = record
      { ψ       = λ X → G.F₁ (ψ X)
      ; commute = λ f → [ G ]-resp-∘ (commute f)
      }
    }
    where open CF.Cocone K

  F-map-Cocone⇒ : ∀ {K K′} (f : CF.Cocone⇒ K K′) → CGF.Cocone⇒ (F-map-Cocone K) (F-map-Cocone K′)
  F-map-Cocone⇒ f = record
    { arr     = G.F₁ arr
    ; commute = [ G ]-resp-∘ commute
    }
    where open CF.Cocone⇒ f


module _ {F G : Functor J C} (α : NaturalTransformation F G) where
  private
    module α  = NaturalTransformation α
    module CF = Coc F
    module CG = Coc G
    
  nat-map-Cocone : CG.Cocone → CF.Cocone
  nat-map-Cocone K = coCone⇒Cocone C (nat-map-Cone α.op (Cocone⇒coCone C K))

  nat-map-Cocone⇒ : ∀ {K K′} (f : CG.Cocone⇒ K K′) → CF.Cocone⇒ (nat-map-Cocone K) (nat-map-Cocone K′)
  nat-map-Cocone⇒ f = coCone⇒⇒Cocone⇒ C (nat-map-Cone⇒ α.op (Cocone⇒⇒coCone⇒ C f))
