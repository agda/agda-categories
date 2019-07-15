{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Diagram.Duality {o ℓ e} (C : Category o ℓ e) where

open Category C

open import Categories.Diagram.Equalizer op
open import Categories.Diagram.Coequalizer C
open import Categories.Diagram.Pullback op
open import Categories.Diagram.Pushout C

private
  variable
    A B : Obj
    f g : A ⇒ B

Coequalizer⇒coEqualizer : Coequalizer f g → Equalizer f g
Coequalizer⇒coEqualizer coe = record
  { arr       = arr
  ; equality  = equality
  ; equalize  = coequalize
  ; universal = universal
  ; unique    = unique
  }
  where open Coequalizer coe

coEqualizer⇒Coequalizer : Equalizer f g → Coequalizer f g
coEqualizer⇒Coequalizer e = record
  { arr        = arr
  ; equality   = equality
  ; coequalize = equalize
  ; universal  = universal
  ; unique     = unique
  }
  where open Equalizer e

coPullback⇒Pushout : Pullback f g → Pushout f g
coPullback⇒Pushout p = record
  { i₁              = p₁
  ; i₂              = p₂
  ; commute         = commute
  ; universal       = universal
  ; unique          = unique
  ; universal∘i₁≈h₁ = p₁∘universal≈h₁
  ; universal∘i₂≈h₂ = p₂∘universal≈h₂
  }
  where open Pullback p

Pushout⇒coPullback : Pushout f g → Pullback f g
Pushout⇒coPullback p = record
  { p₁              = i₁
  ; p₂              = i₂
  ; commute         = commute
  ; universal       = universal
  ; unique          = unique
  ; p₁∘universal≈h₁ = universal∘i₁≈h₁
  ; p₂∘universal≈h₂ = universal∘i₂≈h₂
  }
  where open Pushout p
