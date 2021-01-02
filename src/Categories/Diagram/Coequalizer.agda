{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)

module Categories.Diagram.Coequalizer {o ℓ e} (𝒞 : Category o ℓ e) where

open Category 𝒞
open HomReasoning

open import Categories.Morphism.Reasoning 𝒞

open import Level
open import Function using (_$_)

private
  variable
    A B C : Obj
    f g h i j k : A ⇒ B

record Coequalizer (f g : A ⇒ B) : Set (o ⊔ ℓ ⊔ e) where
  field
    {obj} : Obj
    arr   : B ⇒ obj

    equality   : arr ∘ f ≈ arr ∘ g
    coequalize : {h : B ⇒ C} → h ∘ f ≈ h ∘ g → obj ⇒ C
    universal  : {h : B ⇒ C} {eq : h ∘ f ≈ h ∘ g} → h ≈ coequalize eq ∘ arr
    unique     : {h : B ⇒ C} {i : obj ⇒ C} {eq : h ∘ f ≈ h ∘ g} → h ≈ i ∘ arr → i ≈ coequalize eq

  unique′ : (eq eq′ : h ∘ f ≈ h ∘ g) → coequalize eq ≈ coequalize eq′
  unique′ eq eq′ = unique universal

  coequalize-resp-≈ : ∀ {eq :  h ∘ f ≈ h ∘ g} {eq′ : i ∘ f ≈ i ∘ g} →
    h ≈ i → coequalize eq ≈ coequalize eq′
  coequalize-resp-≈ {h = h} {i = i} {eq = eq} {eq′ = eq′} h≈i = unique $ begin
    i                   ≈˘⟨ h≈i ⟩
    h                   ≈⟨ universal ⟩
    coequalize eq ∘ arr ∎

  coequalize-resp-≈′ : (eq :  h ∘ f ≈ h ∘ g) → (eq′ : i ∘ f ≈ i ∘ g) →
    h ≈ i → j ≈ coequalize eq → k ≈ coequalize eq′ → j ≈ k
  coequalize-resp-≈′ {j = j} {k = k} eq eq′ h≈i eqj eqk = begin
    j              ≈⟨ eqj ⟩
    coequalize eq  ≈⟨ coequalize-resp-≈ h≈i ⟩
    coequalize eq′ ≈˘⟨ eqk ⟩
    k              ∎
