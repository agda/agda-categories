{-# OPTIONS --without-K --safe #-}

open import Categories.Category

--  obtain free properties from duality
module Categories.Diagram.Pushout.Properties {o ℓ e} (C : Category o ℓ e) where

open Category C

open import Data.Product using (∃; _,_)

open import Categories.Morphism C
open import Categories.Morphism.Properties C
open import Categories.Morphism.Duality C
open import Categories.Object.Coproduct C
open import Categories.Object.Duality C
open import Categories.Diagram.Coequalizer C
open import Categories.Diagram.Pushout C
open import Categories.Diagram.Duality C
open import Categories.Diagram.Pullback op as P′ using (Pullback)

private
  variable
    A B : Obj
    f g h i : A ⇒ B

module _ (p : Pushout f g) where
  open Pushout p

  private
    pullback : Pullback f g
    pullback = Pushout⇒coPullback p
  
  open Pullback pullback
    using (unique′; id-unique; unique-diagram)
    public
  
  swap : Pushout g f
  swap = coPullback⇒Pushout (P′.swap pullback)
  
  glue : Pushout h i₁ → Pushout (h ∘ f) g
  glue p = coPullback⇒Pushout (P′.glue pullback (Pushout⇒coPullback p))
  
  unglue : Pushout (h ∘ f) g → Pushout h i₁
  unglue p = coPullback⇒Pushout (P′.unglue pullback (Pushout⇒coPullback p))

  Pushout-resp-Epi : Epi g → Epi i₁
  Pushout-resp-Epi epi = P′.Pullback-resp-Mono pullback epi

  Pushout-resp-Iso : Iso g h → ∃ λ j → Iso i₁ j
  Pushout-resp-Iso iso with P′.Pullback-resp-Iso pullback (Iso⇒op-Iso (Iso-swap iso))
  ... | j , record { isoˡ = isoˡ ; isoʳ = isoʳ } = j , record { isoˡ = isoʳ ; isoʳ = isoˡ }

Coproduct×Coequalizer⇒Pushout : (cp : Coproduct A B) →
                                Coequalizer (Coproduct.i₁ cp ∘ f) (Coproduct.i₂ cp ∘ g) →
                                Pushout f g
Coproduct×Coequalizer⇒Pushout cp coe =
  coPullback⇒Pushout (P′.Product×Equalizer⇒Pullback (coproduct→product cp)
                                                    (Coequalizer⇒coEqualizer coe))

Coproduct×Pushout⇒Coequalizer : (cp : Coproduct A B) →
                                Pushout f g →
                                Coequalizer (Coproduct.i₁ cp ∘ f) (Coproduct.i₂ cp ∘ g)
Coproduct×Pushout⇒Coequalizer cp p =
  coEqualizer⇒Coequalizer (P′.Product×Pullback⇒Equalizer (coproduct→product cp)
                                                         (Pushout⇒coPullback p))



