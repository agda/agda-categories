{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category.Core using (Category)
open import Categories.Object.Monoid using (IsMonoid)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Data.Product using (_,_)

import Categories.Category.Monoidal.Properties

-- Counital copy categories as described by Cockett & Lack in "Restriction categories III"

module Categories.Category.CounitalCopy {o ℓ e} (𝒞 : Category o ℓ e) where
  open Category 𝒞

  record CounitalCopy : Set (suc (o ⊔ ℓ ⊔ e)) where
    field
      monoidal : Monoidal 𝒞
      symmetric : Symmetric monoidal

    open Symmetric symmetric public
    open Categories.Category.Monoidal.Properties monoidal using (monoidal-Op)

    private
      σ : ∀ {X Y} → X ⊗₀ Y ⇒ Y ⊗₀ X
      σ {X} {Y} = braiding.⇒.η (X , Y)

    field
      isMonoid : ∀ X → IsMonoid (monoidal-Op) X


    Δ : ∀ {X} → X ⇒ X ⊗₀ X
    Δ {X} = IsMonoid.μ (isMonoid X)
    δ : ∀ {X} → X ⇒ unit
    δ {X} = IsMonoid.η (isMonoid X)

    field
      natural : ∀ {A B} {f : A ⇒ B} → Δ ∘ f ≈ (f ⊗₁ f) ∘ Δ
      inverse₁ : Δ {unit} ∘ unitorˡ.from ≈ id
      inverse₂ : unitorˡ.from ∘ Δ {unit} ≈ id
      cocommutative : ∀ {A} → σ ∘ Δ ≈ Δ {A}
      preserves : ∀ {X Y} → associator.to ∘ (id ⊗₁ associator.from) ∘ (id ⊗₁ ((σ ⊗₁ id) ∘ associator.to)) ∘ associator.from ∘ (Δ ⊗₁ Δ) ≈ Δ {X ⊗₀ Y}
    
    module _ {X : Obj} where
      open IsMonoid (isMonoid X) public hiding (μ; η) renaming (assoc to Δ-assoc; identityˡ to δ-identityˡ; identityʳ to δ-identityʳ)
