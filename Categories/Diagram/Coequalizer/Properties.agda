{-# OPTIONS --without-K --safe #-}

open import Categories.Category
import Categories.Diagram.Coequalizer as Coe

-- we use duality to prove properties about coequalizer
module Categories.Diagram.Coequalizer.Properties
  {o ℓ e} {C : Category o ℓ e} {A B : Category.Obj C}
  {f g : C [ A , B ]} (coe : Coe.Coequalizer C f g) where

open Category C
open Coe C
open Coequalizer coe

open import Categories.Morphism C
open import Categories.Diagram.Equalizer op
open import Categories.Diagram.Duality C

private
  equalizer : Equalizer f g
  equalizer = Coequalizer⇒coEqualizer coe

open Equalizer equalizer
  using (unique′; equality-∘; unique-diagram)
  renaming ( id-equalize      to id-coequalize
           ; equalize-resp-≈  to coequalize-resp-≈
           ; equalize-resp-≈′ to coequalize-resp-≈′
           )
  public

Coequalizer⇒Epi : Epi arr
Coequalizer⇒Epi = Equalizer⇒Mono equalizer
