{-# OPTIONS --without-K --safe #-}

open import Categories.Category

--  obtain free properties from duality
module Categories.Diagram.Pushout.Properties {o ℓ e} (C : Category o ℓ e) where

open Category C

open import Data.Product using (∃; _,_)

open import Categories.Category.Cocartesian C using (Cocartesian)
open import Categories.Morphism C using (_≅_; Epi; Iso)
open import Categories.Morphism.Properties C using (Iso-swap)
open import Categories.Morphism.Duality C using (op-≅⇒≅; Iso⇒op-Iso)
open import Categories.Object.Initial C using (Initial)
open import Categories.Object.Terminal op using (Terminal)
open import Categories.Object.Coproduct C using (Coproduct)
open import Categories.Object.Duality C
open import Categories.Diagram.Coequalizer C using (Coequalizer)
open import Categories.Diagram.Pushout C using (Pushout)
open import Categories.Diagram.Duality C
open import Categories.Diagram.Pullback op as P′ using (Pullback)
open import Categories.Diagram.Pullback.Properties op

private
  variable
    A B X Y : Obj
    f g h i : A ⇒ B

module _ (p : Pushout f g) where
  open Pushout p

  private
    pullback : Pullback f g
    pullback = Pushout⇒coPullback p

  open Pullback pullback
    using (unique′; id-unique; unique-diagram)
    public

  up-to-iso : (p′ : Pushout f g) → Pushout.Q p ≅ Pushout.Q p′
  up-to-iso p′ = op-≅⇒≅ (P′.up-to-iso (Pushout⇒coPullback p) (Pushout⇒coPullback p′))

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
  coPullback⇒Pushout (P′.Product×Equalizer⇒Pullback (Coproduct⇒coProduct cp)
                                                    (Coequalizer⇒coEqualizer coe))

Coproduct×Pushout⇒Coequalizer : (cp : Coproduct A B) →
                                Pushout f g →
                                Coequalizer (Coproduct.i₁ cp ∘ f) (Coproduct.i₂ cp ∘ g)
Coproduct×Pushout⇒Coequalizer cp p =
  coEqualizer⇒Coequalizer (P′.Product×Pullback⇒Equalizer (Coproduct⇒coProduct cp)
                                                         (Pushout⇒coPullback p))

module _ (i : Initial) where
  open Initial i
  private
    t : Terminal
    t = ⊥⇒op⊤ i

  pushout-⊥⇒coproduct : Pushout (¡ {X}) (¡ {Y}) → Coproduct X Y
  pushout-⊥⇒coproduct p = coProduct⇒Coproduct (pullback-⊤⇒product t (Pushout⇒coPullback p))

  coproduct⇒pushout-⊥ : Coproduct X Y → Pushout (¡ {X}) (¡ {Y})
  coproduct⇒pushout-⊥ c = coPullback⇒Pushout (product⇒pullback-⊤ t (Coproduct⇒coProduct c))

pushout-resp-≈ : Pushout f g → f ≈ h → g ≈ i → Pushout h i
pushout-resp-≈ p eq eq′ = coPullback⇒Pushout (pullback-resp-≈ (Pushout⇒coPullback p) eq eq′)

module _ (pushouts : ∀ {X Y Z} (f : X ⇒ Y) (g : X ⇒ Z) → Pushout f g)
         (cocartesian : Cocartesian) where
  open Cocartesian cocartesian
  open Dual

  pushout×cocartesian⇒coequalizer : Coequalizer f g
  pushout×cocartesian⇒coequalizer = coEqualizer⇒Coequalizer
    (pullback×cartesian⇒equalizer (λ f g → Pushout⇒coPullback (pushouts f g)) op-cartesian)
