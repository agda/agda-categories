{-# OPTIONS --without-K --safe #-}

module Categories.Diagram.Cocone.Properties where

open import Level

open import Categories.Category
open import Categories.Functor
open import Categories.Functor.Properties
open import Categories.NaturalTransformation
open import Categories.Diagram.Cone.Properties using (F-map-Coneʳ; F-map-Cone⇒ʳ; nat-map-Cone; nat-map-Cone⇒)
open import Categories.Diagram.Duality
open import Categories.Category.Construction.Cocones using (Cocones)

import Categories.Diagram.Cocone as Coc
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level
    C D J J′ : Category o ℓ e

module _ {F : Functor J C} (G : Functor C D) where
  private
    module C = Category C
    module D = Category D
    module F = Functor F
    module G = Functor G
    module CF = Coc F
    GF = G ∘F F
    module CGF = Coc GF

  F-map-Coconeˡ : CF.Cocone → CGF.Cocone
  F-map-Coconeˡ K = record
    { coapex = record
      { ψ       = λ X → G.F₁ (ψ X)
      ; commute = λ f → [ G ]-resp-∘ (commute f)
      }
    }
    where open CF.Cocone K

  F-map-Cocone⇒ˡ : ∀ {K K′} (f : CF.Cocone⇒ K K′) → CGF.Cocone⇒ (F-map-Coconeˡ K) (F-map-Coconeˡ K′)
  F-map-Cocone⇒ˡ f = record
    { arr     = G.F₁ arr
    ; commute = [ G ]-resp-∘ commute
    }
    where open CF.Cocone⇒ f

  mapˡ : Functor (Cocones F) (Cocones (G ∘F F))
  mapˡ = record
    { F₀ = F-map-Coconeˡ
    ; F₁ =  F-map-Cocone⇒ˡ
    ; identity = G.identity
    ; homomorphism = G.homomorphism
    ; F-resp-≈ = G.F-resp-≈
    }

module _ {F : Functor J C} (G : Functor J′ J) where
  private
    module C   = Category C
    module J′  = Category J′
    module F   = Functor F
    module G   = Functor G
    module CF  = Coc F
    FG = F ∘F G
    module CFG = Coc FG

  F-map-Coconeʳ : CF.Cocone → CFG.Cocone
  F-map-Coconeʳ K = coCone⇒Cocone C (F-map-Coneʳ G.op (Cocone⇒coCone C K))

  F-map-Cocone⇒ʳ : ∀ {K K′} (f : CF.Cocone⇒ K K′) → CFG.Cocone⇒ (F-map-Coconeʳ K) (F-map-Coconeʳ K′)
  F-map-Cocone⇒ʳ f = coCone⇒⇒Cocone⇒ C (F-map-Cone⇒ʳ G.op (Cocone⇒⇒coCone⇒ C f))

  mapʳ : Functor (Cocones F) (Cocones (F ∘F G))
  mapʳ = record
    { F₀ = F-map-Coconeʳ
    ; F₁ = F-map-Cocone⇒ʳ
    ; identity = C.Equiv.refl
    ; homomorphism = C.Equiv.refl
    ; F-resp-≈ = λ f≈g → f≈g
    }


module _ {F G : Functor J C} (α : NaturalTransformation F G) where
  private
    module C  = Category C
    module α  = NaturalTransformation α
    module CF = Coc F
    module CG = Coc G

  nat-map-Cocone : CG.Cocone → CF.Cocone
  nat-map-Cocone K = coCone⇒Cocone C (nat-map-Cone α.op (Cocone⇒coCone C K))

  nat-map-Cocone⇒ : ∀ {K K′} (f : CG.Cocone⇒ K K′) → CF.Cocone⇒ (nat-map-Cocone K) (nat-map-Cocone K′)
  nat-map-Cocone⇒ f = coCone⇒⇒Cocone⇒ C (nat-map-Cone⇒ α.op (Cocone⇒⇒coCone⇒ C f))

  nat-map : Functor (Cocones G) (Cocones F)
  nat-map = record
    { F₀ = nat-map-Cocone
    ; F₁ = nat-map-Cocone⇒
    ; identity = C.Equiv.refl
    ; homomorphism = C.Equiv.refl
    ; F-resp-≈ = λ f≈g → f≈g
    }
