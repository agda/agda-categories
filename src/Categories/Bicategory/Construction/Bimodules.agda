{-# OPTIONS --without-K --safe --lossy-unification  #-}
-- lossy unification speeds up type checking by preventing Agda from unfolding all definitions

open import Categories.Bicategory
open import Categories.Bicategory.LocalCoequalizers

module Categories.Bicategory.Construction.Bimodules {o ℓ e t} {𝒞 : Bicategory o ℓ e t} {localCoeq : LocalCoequalizers 𝒞} where

open import Categories.Bicategory.Monad
open import Level

open import Categories.Bicategory.Monad.Bimodule
import Categories.Category.Construction.Bimodules
open Categories.Category.Construction.Bimodules {o} {ℓ} {e} {t} {𝒞} renaming (Bimodules to Bimodules₁)
import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞
open import Categories.Category


private
  module Bimodules₁ M₁ M₂ = Category (Bimodules₁ M₁ M₂)

open import Data.Product using (_,_)
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)
open import Categories.Morphism using (_≅_)
open import Categories.Bicategory.Construction.Bimodules.TensorproductOfBimodules using () renaming (Tensorproduct to infixr 30 _⊗₀_)
open import Categories.Bicategory.Construction.Bimodules.TensorproductOfHomomorphisms using () renaming (Tensorproduct to infixr 30 _⊗₁_)
open import Categories.Bicategory.Construction.Bimodules.Tensorproduct.Functorial {𝒞 = 𝒞} {localCoeq}
open import Categories.Bicategory.Construction.Bimodules.Tensorproduct.Associator {𝒞 = 𝒞} {localCoeq} using (associator-⊗)
open import Categories.Bicategory.Construction.Bimodules.Tensorproduct.Associator.Naturality {𝒞 = 𝒞} {localCoeq} using (α⇒-⊗-natural)
import Categories.Bicategory.Construction.Bimodules.Tensorproduct.Unitor {𝒞 = 𝒞} {localCoeq} as Unitor
open Unitor.Left-Unitor using (unitorˡ-⊗)
open Unitor.Right-Unitor using (unitorʳ-⊗)
import Categories.Bicategory.Construction.Bimodules.Tensorproduct.Unitor.Naturality {𝒞 = 𝒞} {localCoeq} as Unitor-Naturality
open Unitor-Naturality.Left-Unitor-natural using (λ⇒-⊗-natural)
open Unitor-Naturality.Right-Unitor-natural using (ρ⇒-⊗-natural)
open import Categories.Bicategory.Construction.Bimodules.Tensorproduct.Coherence.Pentagon {𝒞 = 𝒞} {localCoeq} using (pentagon-⊗)
open import Categories.Bicategory.Construction.Bimodules.Tensorproduct.Coherence.Triangle {𝒞 = 𝒞} {localCoeq} using (triangle-⊗)

Bimodules : Bicategory (o ⊔ ℓ ⊔ e) (ℓ ⊔ e) e (o ⊔ ℓ ⊔ e ⊔ t)
Bimodules = record
  { enriched = record
    { Obj = Monad 𝒞
    ; hom = Bimodules₁
    ; id = λ {M} → record
    { F₀ = λ _ → id-bimodule M
    ; F₁ = λ _ → Bimodules₁.id M M
    ; identity = hom.Equiv.refl
    ; homomorphism = hom.Equiv.sym (Bimodules₁.identity² M M)
    ; F-resp-≈ = λ _ → hom.Equiv.refl
    }
    ; ⊚ = record
      { F₀ = λ (B₂ , B₁) → B₂ ⊗₀ B₁
      ; F₁ = λ (h₂ , h₁) → h₂ ⊗₁ h₁
      ; identity = λ {(B₂ , B₁)} → Identity.⊗₁-resp-id₂ B₂ B₁
      ; homomorphism = λ {_} {_} {_} {(g₂ , g₁)} {(h₂ , h₁)} → Composition.⊗₁-distr-∘ᵥ h₂ h₁ g₂ g₁
      ; F-resp-≈ = λ {_} {_} {(h₂ , h₁)} {(h'₂ , h'₁)} (e₂ , e₁) → ≈Preservation.⊗₁-resp-≈ h₂ h'₂ h₁ h'₁ e₂ e₁
      }
    ; ⊚-assoc = niHelper record
      { η = λ ((B₃ , B₂) , B₁) → _≅_.from (associator-⊗ {B₃ = B₃} {B₂} {B₁})
      ; η⁻¹ = λ ((B₃ , B₂) , B₁) → _≅_.to (associator-⊗ {B₃ = B₃} {B₂} {B₁})
      ; commute = λ ((f₃ , f₂) , f₁) → α⇒-⊗-natural f₃ f₂ f₁
      ; iso = λ ((B₃ , B₂) , B₁) → _≅_.iso (associator-⊗ {B₃ = B₃} {B₂} {B₁})
      }
    ; unitˡ = niHelper record
      { η = λ (_ , B) → _≅_.from (unitorˡ-⊗ {B = B})
      ; η⁻¹ = λ (_ , B) → _≅_.to (unitorˡ-⊗ {B = B})
      ; commute = λ (_ , f) → λ⇒-⊗-natural f
      ; iso = λ (_ , B) → _≅_.iso (unitorˡ-⊗ {B = B})
      }
    ; unitʳ = niHelper record
      { η = λ (B , _) → _≅_.from (unitorʳ-⊗ {B = B})
      ; η⁻¹ = λ (B , _) → _≅_.to (unitorʳ-⊗ {B = B})
      ; commute = λ (f , _) → ρ⇒-⊗-natural f
      ; iso = λ (B , _) → _≅_.iso (unitorʳ-⊗ {B = B})
      }
    }
  ; triangle = λ {_} {_} {_} {B₁} {B₂} → triangle-⊗ {B₂ = B₂} {B₁}
  ; pentagon = λ {_} {_} {_} {_} {_} {B₁} {B₂} {B₃} {B₄} → pentagon-⊗ {B₄ = B₄} {B₃} {B₂} {B₁}
  }
