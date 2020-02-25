{-# OPTIONS --without-K --safe #-}
open import Categories.Category

-- Equalizers in a Category C
module Categories.Diagram.Equalizer {o ℓ e} (C : Category o ℓ e) where

open Category C
open HomReasoning

open import Level
open import Data.Product as Σ
open import Function using (_$_)
open import Categories.Morphism C
open import Categories.Morphism.Reasoning C

private
  variable
    A B X : Obj
    h i j k : A ⇒ B

record Equalizer (f g : A ⇒ B) : Set (o ⊔ ℓ ⊔ e) where
  field
    {obj} : Obj
    arr   : obj ⇒ A

    equality  : f ∘ arr ≈ g ∘ arr
    equalize  : ∀ {h : X ⇒ A} → f ∘ h ≈ g ∘ h → X ⇒ obj
    universal : ∀ {eq : f ∘ h ≈ g ∘ h} → h ≈ arr ∘ equalize eq
    unique    : ∀ {eq : f ∘ h ≈ g ∘ h} → h ≈ arr ∘ i → i ≈ equalize eq

  unique′ : (eq eq′ : f ∘ h ≈ g ∘ h) → equalize eq ≈ equalize eq′
  unique′ eq eq′ = unique universal

  id-equalize : id ≈ equalize equality
  id-equalize = unique (sym identityʳ)

  equalize-resp-≈ : ∀ {eq : f ∘ h ≈ g ∘ h} {eq′ : f ∘ i ≈ g ∘ i} →
    h ≈ i → equalize eq ≈ equalize eq′
  equalize-resp-≈ {h = h} {i = i} {eq = eq} {eq′ = eq′} h≈i = unique $ begin
    i                 ≈˘⟨ h≈i ⟩
    h                 ≈⟨ universal ⟩
    arr ∘ equalize eq ∎

  equalize-resp-≈′ : (eq : f ∘ h ≈ g ∘ h) → (eq′ : f ∘ i ≈ g ∘ i) →
    h ≈ i → j ≈ equalize eq → k ≈ equalize eq′ → j ≈ k
  equalize-resp-≈′ {j = j} {k = k} eq eq′ h≈i eqj eqk = begin
    j            ≈⟨ eqj ⟩
    equalize eq  ≈⟨ equalize-resp-≈ h≈i ⟩
    equalize eq′ ≈˘⟨ eqk ⟩
    k            ∎

  equality-∘ : f ∘ arr ∘ h ≈ g ∘ arr ∘ h
  equality-∘ {h = h} = begin
    f ∘ arr ∘ h   ≈⟨ pullˡ equality ⟩
    (g ∘ arr) ∘ h ≈⟨ assoc ⟩
    g ∘ arr ∘ h   ∎

  unique-diagram : arr ∘ h ≈ arr ∘ i → h ≈ i
  unique-diagram {h = h} {i = i} eq = begin
    h                           ≈⟨ unique (sym eq) ⟩
    equalize (extendʳ equality) ≈˘⟨ unique refl ⟩
    i                           ∎

Equalizer⇒Mono : (e : Equalizer h i) → Mono (Equalizer.arr e)
Equalizer⇒Mono e f g eq =
  equalize-resp-≈′ equality-∘ equality-∘ eq (unique refl) (unique refl)
  where open Equalizer e
