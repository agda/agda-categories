open import Categories.Category.Core using (Category)
open import Categories.Category.Copy using (TotalCopy)
open import Categories.Category.Restriction using (Restriction)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

import Categories.Morphism.Reasoning as MR

module Categories.Category.Copy.Restriction {o ℓ e} {𝒞 : Category o ℓ e} (totalCopy : TotalCopy 𝒞) where
  open Category 𝒞
  open Equiv
  open MR 𝒞
  open HomReasoning
  open TotalCopy totalCopy
  open Symmetric symmetric
  restriction : Restriction 𝒞
  restriction = record
    { _↓ = λ {A} {B} f → unitorˡ.from ∘ (counit ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ
    ; pidʳ = λ {A} {B} {f} → begin 
      f ∘ unitorˡ.from ∘ (counit ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ ≈⟨ extendʳ (sym unitorˡ-commute-from) ⟩ 
      unitorˡ.from ∘ (id ⊗₁ f) ∘ (counit ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ ≈⟨ refl⟩∘⟨ (extendʳ {!   !}) ⟩ 
      unitorˡ.from ∘ (counit ⊗₁ id) ∘ (id ⊗₁ f) ∘ (f ⊗₁ id) ∘ Δ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ {!   !} ⟩ 
      unitorˡ.from ∘ (counit ⊗₁ id) ∘ (f ⊗₁ f) ∘ Δ ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ natural ⟩
      unitorˡ.from ∘ (counit ⊗₁ id) ∘ Δ ∘ f ≈⟨ sym-assoc ○ cancelˡ (assoc ○ {!   !}) ⟩ 
      f ∎
    ; ↓-comm = λ {A} {B} {C} {f} {g} → begin 
      (unitorˡ.from ∘ (counit ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ) ∘ unitorˡ.from ∘ (counit ⊗₁ id) ∘ (g ⊗₁ id) ∘ Δ ≈⟨ {!   !} ⟩ 
      {!   !} ≈⟨ {!   !} ⟩ 
      {!   !} ≈⟨ {!   !} ⟩ 
      {!   !} ≈⟨ {!   !} ⟩ 
      (unitorˡ.from ∘ (counit ⊗₁ id) ∘ (g ⊗₁ id) ∘ Δ) ∘ unitorˡ.from ∘ (counit ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ ∎
    ; ↓-denestʳ = {!   !}
    ; ↓-skew-comm = {!   !}
    ; ↓-cong = {!   !}
    }