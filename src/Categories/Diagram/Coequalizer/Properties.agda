{-# OPTIONS --without-K --safe #-}

open import Categories.Category

-- we use duality to prove properties about coequalizer
module Categories.Diagram.Coequalizer.Properties {o ℓ e} (C : Category o ℓ e) where

open Category C

open import Categories.Diagram.Coequalizer C using (Coequalizer; IsCoequalizer; Coequalizer⇒Epi; up-to-iso)
open import Categories.Morphism C
import Categories.Morphism.Reasoning as MR
open import Categories.Diagram.Equalizer op hiding (up-to-iso)
open import Categories.Diagram.Equalizer.Properties op
open import Categories.Diagram.Duality C
open import Categories.Diagram.KernelPair C
open import Categories.Diagram.Pullback C hiding (up-to-iso)
open import Categories.Morphism.Regular C


import Relation.Binary.Reasoning.Setoid as SR

open Pullback hiding (universal; unique)

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
    using (unique′; unique-diagram)
    renaming ( id-equalize      to id-coequalize
             ; equalize-resp-≈  to coequalize-resp-≈
             ; equalize-resp-≈′ to coequalize-resp-≈′
             )
    public

-- a regular epi is a coequalizer of its kernel pair
regular-is-coeq-kp : {A B : Obj} (f : A ⇒ B) → RegularEpi f → (kp : KernelPair f) → IsCoequalizer (p₁ kp) (p₂ kp) f
regular-is-coeq-kp {A} {B} f record { C = D ; h = h ; g = g ; coequalizer = coeq } kp = record
  { equality   = IsPullback.commute (isPullback kp)
  ; coequalize = λ {_}{u} u∘p₁≈u∘p₂ → coequalize (u∘h≈u∘g u u∘p₁≈u∘p₂)
  ; universal  = universal
  ; unique     = unique
  }

  where
    open IsCoequalizer coeq
    pb-univ : D ⇒ P kp
    pb-univ = IsPullback.universal (isPullback kp) equality

    u∘h≈u∘g : {X : Obj} → (u : A ⇒ X) → u ∘ (p₁ kp) ≈ u ∘ (p₂ kp) → u ∘ h ≈ u ∘ g
    u∘h≈u∘g {X} u u∘p₁≈u∘p₂ = begin
      u ∘ h                   ≈˘⟨ refl⟩∘⟨ p₁∘universal≈h₁ kp ⟩
      u ∘ (p₁ kp  ∘ pb-univ)  ≈⟨ pullˡ u∘p₁≈u∘p₂ ⟩
      (u ∘ p₂ kp) ∘ pb-univ   ≈⟨ pullʳ (p₂∘universal≈h₂ kp) ⟩
      u ∘ g                   ∎
      where
        open Category.HomReasoning C
        open MR C

retract-coequalizer : ∀ {X Y} {f : Y ⇒ X} {g : X ⇒ Y} → f RetractOf g → IsCoequalizer (g ∘ f) id f
retract-coequalizer f∘g≈id = IscoEqualizer⇒IsCoequalizer (section-equalizer f∘g≈id)

-- split coequalizer are coequalizer --
splitCoequalizer⇒Coequalizer : {A B C : Obj} {f g : A ⇒ B} {e : B ⇒ C}
                               (t : B ⇒ A) (s : C ⇒ B)
                               (eq : e ∘ f ≈ e ∘ g)
                               (tisSection : f ∘ t ≈ id)
                               (sisSection : e ∘ s ≈ id)
                               (sq : s ∘ e ≈ g ∘ t)
                               → IsCoequalizer f g e
splitCoequalizer⇒Coequalizer {f = f} {g} {e} t s eq tisSection sisSection sq = record
  { equality = eq
  ; coequalize = λ {T} {h} _ → h ∘ s
  ; universal = λ {T} {h} {h∘f≈h∘g} → begin
    h           ≈⟨ ⟺ identityʳ ⟩
    h ∘ id      ≈⟨ refl⟩∘⟨ ⟺ tisSection ⟩
    h ∘ f ∘ t   ≈⟨ sym-assoc ⟩
    (h ∘ f) ∘ t ≈⟨ h∘f≈h∘g ⟩∘⟨refl ⟩
    (h ∘ g) ∘ t ≈⟨ assoc ⟩
    h ∘ g ∘ t   ≈⟨ refl⟩∘⟨ ⟺ sq ⟩
    h ∘ s ∘ e   ≈⟨ sym-assoc ⟩
    (h ∘ s) ∘ e ∎
  ; unique = λ {C} {h} {i} {h∘f≈h∘g} h≈i∘e → begin
    i ≈⟨ ⟺ identityʳ ⟩
    i ∘ id ≈⟨ refl⟩∘⟨ ⟺ sisSection ⟩
    i ∘ e ∘ s ≈⟨ sym-assoc ⟩
    (i ∘ e) ∘ s ≈⟨ ⟺ h≈i∘e ⟩∘⟨refl ⟩
    h ∘ s ∎
  }
  where
    open HomReasoning

splitCoequalizer⇒Coequalizer-sym : {A B C : Obj} {f g : A ⇒ B} {e : B ⇒ C}
                               (t : B ⇒ A) (s : C ⇒ B)
                               (eq : e ∘ f ≈ e ∘ g)
                               (tisSection : g ∘ t ≈ id)
                               (sisSection : e ∘ s ≈ id)
                               (sq : s ∘ e ≈ f ∘ t)
                               → IsCoequalizer f g e
splitCoequalizer⇒Coequalizer-sym {f = f} {g} {e} t s eq tisSection sisSection sq = record
  { equality = eq
  ; coequalize = λ {T} {h} _ → h ∘ s
  ; universal = λ {T} {h} {h∘f≈h∘g} → begin
    h           ≈⟨ ⟺ identityʳ ⟩
    h ∘ id      ≈⟨ refl⟩∘⟨ ⟺ tisSection ⟩
    h ∘ g ∘ t   ≈⟨ sym-assoc ⟩
    (h ∘ g) ∘ t ≈⟨ ⟺ h∘f≈h∘g ⟩∘⟨refl ⟩
    (h ∘ f) ∘ t ≈⟨ assoc ⟩
    h ∘ f ∘ t   ≈⟨ refl⟩∘⟨ ⟺ sq ⟩
    h ∘ s ∘ e   ≈⟨ sym-assoc ⟩
    (h ∘ s) ∘ e ∎
  ; unique = λ {C} {h} {i} {h∘f≈h∘g} h≈i∘e → begin
    i ≈⟨ ⟺ identityʳ ⟩
    i ∘ id ≈⟨ refl⟩∘⟨ ⟺ sisSection ⟩
    i ∘ e ∘ s ≈⟨ sym-assoc ⟩
    (i ∘ e) ∘ s ≈⟨ ⟺ h≈i∘e ⟩∘⟨refl ⟩
    h ∘ s ∎
  }
  where
    open HomReasoning
