{-# OPTIONS --without-K --safe #-}

module Categories.Diagram.Cone.Properties where

open import Level

open import Categories.Category
open import Categories.Functor
open import Categories.Functor.Properties
import Categories.Diagram.Cone as Con

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
    module CF = Con F
    GF = G ∘F F
    module CGF = Con GF

  F-map-Cone : CF.Cone → CGF.Cone
  F-map-Cone K = record
    { apex = record
      { ψ       = λ X → G.F₁ (ψ X)
      ; commute = λ f → [ G ]-resp-∘ (commute f)
      }
    }
    where open CF.Cone K

  F-map-Cone⇒ : ∀ {K K′} (f : CF.Cone⇒ K K′) → CGF.Cone⇒ (F-map-Cone K) (F-map-Cone K′)
  F-map-Cone⇒ f = record
    { arr     = G.F₁ arr
    ; commute = [ G ]-resp-∘ commute
    }
    where open CF.Cone⇒ f
