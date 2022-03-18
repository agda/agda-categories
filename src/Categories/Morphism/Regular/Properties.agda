{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core

module Categories.Morphism.Regular.Properties {o ℓ e} (𝒞 : Category o ℓ e) where

open import Categories.Morphism 𝒞
open import Categories.Morphism.Regular 𝒞
open import Categories.Diagram.Equalizer 𝒞
open import Categories.Diagram.Equalizer.Properties 𝒞
open import Categories.Diagram.Coequalizer.Properties 𝒞

open Category 𝒞

private
  variable
    A B : Obj
    f g : A ⇒ B

Section⇒RegularMono : f SectionOf g → RegularMono f
Section⇒RegularMono {f = f} {g = g} g∘f≈id = record
  { g = id
  ; h = f ∘ g
  ; equalizer = section-equalizer g∘f≈id
  }

Retract⇒RegularEpi : f RetractOf g → RegularEpi f
Retract⇒RegularEpi {f = f} {g = g} f∘g≈id = record
  { h = g ∘ f
  ; g = id
  ; coequalizer = retract-coequalizer f∘g≈id
  }
