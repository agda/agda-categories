{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Continuous where

open import Level
open import Data.Product using (Σ)

open import Categories.Category
open import Categories.Functor
import Categories.Category.Construction.Cones as Con
import Categories.Diagram.Cone.Properties as Conₚ
import Categories.Diagram.Limit as Lim
import Categories.Morphism as Mor

private
  variable
    o ℓ e : Level
    C D E J : Category o ℓ e

-- G preserves the limit of F.
LimitPreserving : (G : Functor C D) {F : Functor J C} (L : Lim.Limit F) → Set _
LimitPreserving {C = C} {D = D} G {F} L = Σ (Lim.Limit (G ∘F F)) λ L′ → G.F₀ (Lim.Limit.apex L) ≅ Lim.Limit.apex L′
  where module F = Functor F
        module G = Functor G
        open Mor D

-- continuous functors preserves all limits.
Continuous : ∀ o ℓ e (G : Functor C D) → Set _
Continuous {C = C} o ℓ e G = ∀ {J : Category o ℓ e} {F : Functor J C} (L : Lim.Limit F) → LimitPreserving G L
