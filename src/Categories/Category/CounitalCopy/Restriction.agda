{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.CounitalCopy using (CounitalCopy)
open import Categories.Category.Restriction using (Restriction)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Data.Product using (_,_)

import Categories.Morphism.Reasoning as MR

module Categories.Category.CounitalCopy.Restriction {o ℓ e} {𝒞 : Category o ℓ e} (counitalCopy : CounitalCopy 𝒞) where
  open Category 𝒞
  open Equiv
  open MR 𝒞
  open HomReasoning
  open CounitalCopy counitalCopy
  open Symmetric symmetric
  restriction : Restriction 𝒞
  restriction = record
    { _↓ = λ {A} {B} f → unitorˡ.from ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ
    ; pidʳ = λ {A} {B} {f} → begin 
      f ∘ unitorˡ.from ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ         ≈⟨ extendʳ (sym unitorˡ-commute-from) ⟩ 
      unitorˡ.from ∘ (id ⊗₁ f) ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ ≈⟨ refl⟩∘⟨ (extendʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (id-comm-sym , id-comm) ○ ⊗.homomorphism)) ⟩ 
      unitorˡ.from ∘ (δ ⊗₁ id) ∘ (id ⊗₁ f) ∘ (f ⊗₁ id) ∘ Δ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identityˡ , identityʳ)) ⟩ 
      unitorˡ.from ∘ (δ ⊗₁ id) ∘ (f ⊗₁ f) ∘ Δ              ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ natural ⟩
      unitorˡ.from ∘ (δ ⊗₁ id) ∘ Δ ∘ f                     ≈⟨ refl⟩∘⟨ (pullˡ (sym δ-identityˡ)) ⟩ 
      unitorˡ.from ∘ unitorˡ.to ∘ f                        ≈⟨ cancelˡ unitorˡ.isoʳ ⟩ 
      f                                                    ∎
    ; ↓-comm = λ {A} {B} {C} {f} {g} → begin 
      (unitorˡ.from ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ) ∘ unitorˡ.from ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ Δ ≈⟨ {!   !} ⟩ 
      {!   !} ≈⟨ {!   !} ⟩ 
      {!   !} ≈⟨ {!   !} ⟩ 
      {!   !} ≈⟨ {!   !} ⟩ 
      (unitorˡ.from ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ Δ) ∘ unitorˡ.from ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ ∎
    ; ↓-denestʳ = λ {A} {B} {C} {f} {g} → {! begin ? ≈⟨ ? ⟩ ? ∎  !}
    ; ↓-skew-comm = λ {A} {B} {C} {g} {f} → begin 
      (unitorˡ.from ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ Δ) ∘ f                   ≈⟨ pullʳ (pullʳ (pullʳ natural)) ⟩ 
      unitorˡ.from ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ (f ⊗₁ f) ∘ Δ              ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identityˡ , identityʳ)) ⟩ 
      unitorˡ.from ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ (id ⊗₁ f) ∘ (f ⊗₁ id) ∘ Δ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (extendʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (id-comm , id-comm-sym) ○ ⊗.homomorphism)) ⟩ 
      unitorˡ.from ∘ (δ ⊗₁ id) ∘ (id ⊗₁ f) ∘ (g ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ ≈⟨ refl⟩∘⟨ (extendʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (id-comm , id-comm-sym) ○ ⊗.homomorphism)) ⟩  
      unitorˡ.from ∘ (id ⊗₁ f) ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ ≈⟨ extendʳ unitorˡ-commute-from ⟩ 
      f ∘ unitorˡ.from ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ         ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (refl , identity²)) ⟩ 
      f ∘ unitorˡ.from ∘ (δ ⊗₁ id) ∘ ((g ∘ f) ⊗₁ id) ∘ Δ               ∎
    ; ↓-cong = λ f≈g → refl⟩∘⟨ refl⟩∘⟨ ⊗.F-resp-≈ (f≈g , refl) ⟩∘⟨refl
    }