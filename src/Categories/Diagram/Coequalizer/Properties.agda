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
  

open import Categories.Diagram.KernelPair C
open import Categories.Morphism.Regular C
open import Categories.Diagram.Pullback C

import Relation.Binary.Reasoning.Setoid as SR

open Pullback 

-- a regular epi is a coequalizer of its kernel pair
regular-is-coeq-kp : {A B : Obj} (f : A ⇒ B) → RegularEpi f → (kp : KernelPair f) → IsCoequalizer (p₁ kp) (p₂ kp) f
regular-is-coeq-kp {A} {B} f record { C = D ; h = h ; g = g ; coequalizer = coeq } kp = record
  { equality   = IsPullback.commute (isPullback kp)
  ; coequalize = λ {_}{u} u∘p₁≈u∘p₂ → IsCoequalizer.coequalize coeq (u∘h≈u∘g u u∘p₁≈u∘p₂)
  ; universal  = IsCoequalizer.universal coeq
  ; unique     = λ u≈w∘f → IsCoequalizer.unique coeq u≈w∘f
  }

  where

    u∘h≈u∘g : {X : Obj} → (u : A ⇒ X) → u ∘ (p₁ kp) ≈ u ∘ (p₂ kp) → u ∘ h ≈ u ∘ g
    u∘h≈u∘g {X} u u∘p₁≈u∘p₂ =
      begin
        u ∘ h ≈˘⟨ refl⟩∘⟨ p₁∘universal≈h₁ kp ⟩
        u ∘ (p₁ kp  ∘ IsPullback.universal (isPullback kp) (IsCoequalizer.equality coeq))  ≈˘⟨ assoc ⟩
        (u ∘ p₁ kp) ∘ IsPullback.universal (isPullback kp) (IsCoequalizer.equality coeq)   ≈⟨ u∘p₁≈u∘p₂ ⟩∘⟨refl ⟩
        (u ∘ p₂ kp) ∘ IsPullback.universal (isPullback kp) (IsCoequalizer.equality coeq)   ≈⟨ assoc ⟩
        u ∘ (p₂ kp  ∘ IsPullback.universal (isPullback kp) (IsCoequalizer.equality coeq))  ≈⟨ refl⟩∘⟨ p₂∘universal≈h₂ kp ⟩
        u ∘ g  ∎

        where
          module C = Category C using (id; module HomReasoning)
          open C.HomReasoning
