{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Cocontinuous where

open import Level
open import Data.Product using (Σ)

open import Categories.Category
open import Categories.Functor
import Categories.Category.Construction.Cocones as Coc
import Categories.Diagram.Cocone.Properties as Cocₚ
import Categories.Diagram.Colimit as Col
import Categories.Morphism as Mor

private
  variable
    o ℓ e : Level
    C D E J : Category o ℓ e

-- G preserves the colimit of F.
CoimitPreserving : (G : Functor C D) {F : Functor J C} (L : Col.Colimit F) → Set _
CoimitPreserving {C = C} {D = D} G {F} L = Σ (Col.Colimit (G ∘F F)) λ L′ → G.F₀ (Col.Colimit.coapex L) ≅ Col.Colimit.coapex L′
  where module F = Functor F
        module G = Functor G
        open Mor D

-- cocontinuous functors preserves all colimits.
Cocontinuous : ∀ (o ℓ e : Level) (G : Functor C D) → Set _
Cocontinuous {C = C} o ℓ e G = ∀ {J : Category o ℓ e} {F : Functor J C} (L : Col.Colimit F) → CoimitPreserving G L
