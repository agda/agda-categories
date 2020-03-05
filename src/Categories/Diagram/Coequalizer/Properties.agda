{-# OPTIONS --without-K --safe #-}

open import Categories.Category

-- we use duality to prove properties about coequalizer
module Categories.Diagram.Coequalizer.Properties {o ℓ e} (C : Category o ℓ e) where

open Category C

open import Categories.Diagram.Coequalizer C
open import Categories.Morphism C
open import Categories.Diagram.Equalizer op
open import Categories.Diagram.Duality C

private
  variable
    A B : Obj
    f g : A ⇒ B

module _ (coe : Coequalizer f g) where
  open Coequalizer coe

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
  
