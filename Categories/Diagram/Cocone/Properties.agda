{-# OPTIONS --without-K --safe #-}

module Categories.Diagram.Cocone.Properties where

open import Level

open import Categories.Category
open import Categories.Functor
open import Categories.Functor.Properties
import Categories.Diagram.Cocone as Coc

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

  F-map-Cone⇒ : ∀ {K K′} (f : CF.Cocone⇒ K K′) → CGF.Cocone⇒ (F-map-Cocone K) (F-map-Cocone K′)
  F-map-Cone⇒ f = record
    { arr     = G.F₁ arr
    ; commute = [ G ]-resp-∘ commute
    }
    where open CF.Cocone⇒ f
