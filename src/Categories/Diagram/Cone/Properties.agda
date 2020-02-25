{-# OPTIONS --without-K --safe #-}

module Categories.Diagram.Cone.Properties where

open import Level

open import Categories.Category
open import Categories.Functor
open import Categories.Functor.Properties
open import Categories.NaturalTransformation
import Categories.Diagram.Cone as Con
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
    module CF = Con F
    GF = G ∘F F
    module CGF = Con GF

  F-map-Coneˡ : CF.Cone → CGF.Cone
  F-map-Coneˡ K = record
    { apex = record
      { ψ       = λ X → G.F₁ (ψ X)
      ; commute = λ f → [ G ]-resp-∘ (commute f)
      }
    }
    where open CF.Cone K

  F-map-Cone⇒ˡ : ∀ {K K′} (f : CF.Cone⇒ K K′) → CGF.Cone⇒ (F-map-Coneˡ K) (F-map-Coneˡ K′)
  F-map-Cone⇒ˡ f = record
    { arr     = G.F₁ arr
    ; commute = [ G ]-resp-∘ commute
    }
    where open CF.Cone⇒ f

module _ {F : Functor J C} (G : Functor J′ J) where
  private
    module C   = Category C
    module J′  = Category J′
    module F   = Functor F
    module G   = Functor G
    module CF  = Con F
    FG = F ∘F G
    module CFG = Con FG

  F-map-Coneʳ : CF.Cone → CFG.Cone
  F-map-Coneʳ K = record
    { apex = record
      { ψ       = λ j → ψ (G.F₀ j)
      ; commute = λ f → commute (G.F₁ f)
      }
    }
    where open CF.Cone K

  F-map-Cone⇒ʳ : ∀ {K K′} (f : CF.Cone⇒ K K′) → CFG.Cone⇒ (F-map-Coneʳ K) (F-map-Coneʳ K′)
  F-map-Cone⇒ʳ f = record
    { arr     = arr
    ; commute = commute
    }
    where open CF.Cone⇒ f

module _ {F G : Functor J C} (α : NaturalTransformation F G) where
  private
    module C  = Category C
    module J  = Category J
    module F  = Functor F
    module G  = Functor G
    module α  = NaturalTransformation α
    module CF = Con F
    module CG = Con G
    open C
    open HomReasoning
    open MR C

  nat-map-Cone : CF.Cone → CG.Cone
  nat-map-Cone K = record
    { apex = record
      { ψ       = λ j → α.η j C.∘ ψ j
      ; commute = λ {X Y} f → begin
        G.F₁ f ∘ α.η X ∘ ψ X ≈˘⟨ pushˡ (α.commute f) ⟩
        (α.η Y ∘ F.F₁ f) ∘ ψ X ≈⟨ pullʳ (commute f) ⟩
        α.η Y ∘ ψ Y ∎
      }
    }
    where open CF.Cone K

  nat-map-Cone⇒ : ∀ {K K′} (f : CF.Cone⇒ K K′) → CG.Cone⇒ (nat-map-Cone K) (nat-map-Cone K′)
  nat-map-Cone⇒ {K} {K′} f = record
    { arr     = arr
    ; commute = pullʳ commute
    }
    where open CF.Cone⇒ f
