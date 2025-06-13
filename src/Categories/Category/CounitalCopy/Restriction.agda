{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.CounitalCopy using (CounitalCopy)
open import Categories.Category.Restriction using (Restriction)
open import Data.Product using (_,_)

import Categories.Morphism.Reasoning as MR
import Categories.Morphism as M

-- Counital copy categories admit a non trivial restriction structure.

module Categories.Category.CounitalCopy.Restriction {o ℓ e} {𝒞 : Category o ℓ e} (counitalCopy : CounitalCopy 𝒞) where
  open Category 𝒞
  open Equiv
  open M 𝒞
  open MR 𝒞
  open HomReasoning
  open CounitalCopy counitalCopy
  open import Categories.Category.Monoidal.Utilities monoidal
  open import Categories.Category.Monoidal.Properties monoidal
  open import Categories.Category.Monoidal.Braided.Properties braided

  private
    σ : ∀ {X Y} → X ⊗₀ Y ⇒ Y ⊗₀ X
    σ {X} {Y} = braiding.⇒.η (X , Y)

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
      (unitorˡ.from ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ) ∘ unitorˡ.from ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ Δ
        ≈⟨ ↓-comm' f g ⟩
      unitorˡ.from ∘ (unitorˡ.from ⊗₁ id) ∘ ((δ ⊗₁ δ) ⊗₁ id) ∘ ((g ⊗₁ f) ⊗₁ id) ∘ (Δ ⊗₁ id) ∘ Δ
        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (cocommutative , identity²)) ⟩
      unitorˡ.from ∘ (unitorˡ.from ⊗₁ id) ∘ ((δ ⊗₁ δ) ⊗₁ id) ∘ ((g ⊗₁ f) ⊗₁ id) ∘ (σ ⊗₁ id) ∘ (Δ ⊗₁ id) ∘ Δ
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ ((sym (braiding.⇒.commute _)) , refl) ○ ⊗.homomorphism) ⟩
      unitorˡ.from ∘ (unitorˡ.from ⊗₁ id) ∘ ((δ ⊗₁ δ) ⊗₁ id) ∘ (σ ⊗₁ id) ∘ ((f ⊗₁ g) ⊗₁ id) ∘ (Δ ⊗₁ id) ∘ Δ
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ ((sym (braiding.⇒.commute _)) , refl) ○ ⊗.homomorphism) ⟩
      unitorˡ.from ∘ (unitorˡ.from ⊗₁ id) ∘ (σ ⊗₁ id) ∘ ((δ ⊗₁ δ) ⊗₁ id) ∘ ((f ⊗₁ g) ⊗₁ id) ∘ (Δ ⊗₁ id) ∘ Δ
        ≈⟨ refl⟩∘⟨ (pullˡ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ ((braiding-coherence ○ sym coherence₃) , identity²))) ⟩
      unitorˡ.from ∘ (unitorˡ.from ⊗₁ id) ∘ ((δ ⊗₁ δ) ⊗₁ id) ∘ ((f ⊗₁ g) ⊗₁ id) ∘ (Δ ⊗₁ id) ∘ Δ
        ≈˘⟨ ↓-comm' g f ⟩
      (unitorˡ.from ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ Δ) ∘ unitorˡ.from ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ 
        ∎
    ; ↓-denestʳ = λ {A} {B} {C} {f} {g} → begin 
      unitorˡ.from ∘ (δ ⊗₁ id) ∘ ((g ∘ unitorˡ.from ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ) ⊗₁ id) ∘ Δ
        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ (pullˡ (sym ⊗.homomorphism) ○ pullˡ (sym ⊗.homomorphism) ○ pullˡ (sym ⊗.homomorphism) ○ pullˡ (sym ⊗.homomorphism) ○ ∘-resp-≈ˡ (⊗.F-resp-≈ ((assoc ○ assoc ○ assoc) , elimˡ (elimˡ (elimˡ identity²))))) ⟩ 
      unitorˡ.from ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ (unitorˡ.from ⊗₁ id) ∘ ((δ ⊗₁ id) ⊗₁ id) ∘ ((f ⊗₁ id) ⊗₁ id) ∘ (Δ ⊗₁ id) ∘ Δ
        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (sym-assoc ○ sym Δ-assoc) ⟩ 
      unitorˡ.from ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ (unitorˡ.from ⊗₁ id) ∘ ((δ ⊗₁ id) ⊗₁ id) ∘ ((f ⊗₁ id) ⊗₁ id) ∘ associator.to ∘ (id ⊗₁ Δ) ∘ Δ
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (sym assoc-commute-to ○ ∘-resp-≈ʳ (⊗.F-resp-≈ (refl , ⊗.identity))) ⟩ 
      unitorˡ.from ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ (unitorˡ.from ⊗₁ id) ∘ ((δ ⊗₁ id) ⊗₁ id) ∘ associator.to ∘ (f ⊗₁ id) ∘ (id ⊗₁ Δ) ∘ Δ
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (sym assoc-commute-to ○ ∘-resp-≈ʳ (⊗.F-resp-≈ (refl , ⊗.identity))) ⟩ 
      unitorˡ.from ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ (unitorˡ.from ⊗₁ id) ∘ associator.to ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ (id ⊗₁ Δ) ∘ Δ
        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ coherence₁ ⟩ 
      unitorˡ.from ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ unitorˡ.from ∘ associator.from ∘ associator.to ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ (id ⊗₁ Δ) ∘ Δ
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ associator.isoʳ ⟩
      unitorˡ.from ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ unitorˡ.from ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ (id ⊗₁ Δ) ∘ Δ
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (id-comm , id-comm-sym) ○ ⊗.homomorphism) ⟩ 
      unitorˡ.from ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ unitorˡ.from ∘ (δ ⊗₁ id) ∘ (id ⊗₁ Δ) ∘ (f ⊗₁ id) ∘ Δ
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (id-comm , id-comm-sym) ○ ⊗.homomorphism) ⟩ 
      unitorˡ.from ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ unitorˡ.from ∘ (id ⊗₁ Δ) ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ
        ≈˘⟨ pullʳ (pullʳ (pullʳ (extendʳ (sym unitorˡ-commute-from)))) ⟩ 
      (unitorˡ.from ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ Δ) ∘ unitorˡ.from ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ 
        ∎
    ; ↓-skew-comm = λ {A} {B} {C} {g} {f} → begin 
      (unitorˡ.from ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ Δ) ∘ f                   
        ≈⟨ pullʳ (pullʳ (pullʳ natural)) ⟩ 
      unitorˡ.from ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ (f ⊗₁ f) ∘ Δ              
        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identityˡ , identityʳ)) ⟩ 
      unitorˡ.from ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ (id ⊗₁ f) ∘ (f ⊗₁ id) ∘ Δ 
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (extendʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (id-comm , id-comm-sym) ○ ⊗.homomorphism)) ⟩ 
      unitorˡ.from ∘ (δ ⊗₁ id) ∘ (id ⊗₁ f) ∘ (g ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ 
        ≈⟨ refl⟩∘⟨ (extendʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (id-comm , id-comm-sym) ○ ⊗.homomorphism)) ⟩  
      unitorˡ.from ∘ (id ⊗₁ f) ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ 
        ≈⟨ extendʳ unitorˡ-commute-from ⟩ 
      f ∘ unitorˡ.from ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ         
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (refl , identity²)) ⟩ 
      f ∘ unitorˡ.from ∘ (δ ⊗₁ id) ∘ ((g ∘ f) ⊗₁ id) ∘ Δ               
        ∎
    ; ↓-cong = λ f≈g → refl⟩∘⟨ refl⟩∘⟨ ⊗.F-resp-≈ (f≈g , refl) ⟩∘⟨refl
    }
    where
      ↓-comm' : ∀ {A B C} (f : A ⇒ B) (g : A ⇒ C) → (unitorˡ.from ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ) ∘ unitorˡ.from ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ Δ ≈ unitorˡ.from ∘ (unitorˡ.from ⊗₁ id) ∘ ((δ ⊗₁ δ) ⊗₁ id) ∘ ((g ⊗₁ f) ⊗₁ id) ∘ (Δ ⊗₁ id) ∘ Δ
      ↓-comm' f g = begin 
        (unitorˡ.from ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ Δ) ∘ unitorˡ.from ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ Δ
          ≈⟨ pullʳ (pullʳ (pullʳ (extendʳ (sym unitorˡ-commute-from)))) ⟩ 
        unitorˡ.from ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ unitorˡ.from ∘ (id ⊗₁ Δ) ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ Δ
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (id-comm-sym , id-comm) ○ ⊗.homomorphism) ⟩
        unitorˡ.from ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ unitorˡ.from ∘ (δ ⊗₁ id) ∘ (id ⊗₁ Δ) ∘ (g ⊗₁ id) ∘ Δ
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (id-comm-sym , id-comm) ○ ⊗.homomorphism) ⟩
        unitorˡ.from ∘ (δ ⊗₁ id) ∘ (f ⊗₁ id) ∘ unitorˡ.from ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ (id ⊗₁ Δ) ∘ Δ
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (sym unitorˡ-commute-from) ⟩
        unitorˡ.from ∘ (δ ⊗₁ id) ∘ unitorˡ.from ∘ (id ⊗₁ (f ⊗₁ id)) ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ (id ⊗₁ Δ) ∘ Δ
          ≈⟨ refl⟩∘⟨ extendʳ (sym unitorˡ-commute-from) ⟩
        unitorˡ.from ∘ unitorˡ.from ∘ (id ⊗₁ (δ ⊗₁ id)) ∘ (id ⊗₁ (f ⊗₁ id)) ∘ (δ ⊗₁ id) ∘ (g ⊗₁ id) ∘ (id ⊗₁ Δ) ∘ Δ
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (id-comm-sym , id-comm) ○ ⊗.homomorphism) ⟩
        unitorˡ.from ∘ unitorˡ.from ∘ (id ⊗₁ (δ ⊗₁ id)) ∘ (δ ⊗₁ id) ∘ (id ⊗₁ (f ⊗₁ id)) ∘ (g ⊗₁ id) ∘ (id ⊗₁ Δ) ∘ Δ
          ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ associator.isoʳ ⟩
        unitorˡ.from ∘ unitorˡ.from ∘ (id ⊗₁ (δ ⊗₁ id)) ∘ (δ ⊗₁ id) ∘ (id ⊗₁ (f ⊗₁ id)) ∘ (g ⊗₁ id) ∘ associator.from ∘ associator.to ∘ (id ⊗₁ Δ) ∘ Δ
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (sym-assoc ○ sym Δ-assoc) ⟩
        unitorˡ.from ∘ unitorˡ.from ∘ (id ⊗₁ (δ ⊗₁ id)) ∘ (δ ⊗₁ id) ∘ (id ⊗₁ (f ⊗₁ id)) ∘ (g ⊗₁ id) ∘ associator.from ∘ (Δ ⊗₁ id) ∘ Δ
          ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (assoc-commute-from ○ ∘-resp-≈ˡ (⊗.F-resp-≈ (refl , ⊗.identity))) ⟩
        unitorˡ.from ∘ unitorˡ.from ∘ (id ⊗₁ (δ ⊗₁ id)) ∘ (δ ⊗₁ id) ∘ (id ⊗₁ (f ⊗₁ id)) ∘ associator.from ∘ ((g ⊗₁ id) ⊗₁ id) ∘ (Δ ⊗₁ id) ∘ Δ
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (sym assoc-commute-from) ⟩
        unitorˡ.from ∘ unitorˡ.from ∘ (id ⊗₁ (δ ⊗₁ id)) ∘ (δ ⊗₁ id) ∘ associator.from ∘ ((id ⊗₁ f) ⊗₁ id) ∘ ((g ⊗₁ id) ⊗₁ id) ∘ (Δ ⊗₁ id) ∘ Δ
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (pullˡ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identityˡ , identityʳ)) ○ extendʳ (sym assoc-commute-from)) ⟩ 
        unitorˡ.from ∘ unitorˡ.from ∘ associator.from ∘ ((δ ⊗₁ δ) ⊗₁ id) ∘ ((id ⊗₁ f) ⊗₁ id) ∘ ((g ⊗₁ id) ⊗₁ id) ∘ (Δ ⊗₁ id) ∘ Δ
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ ((sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identityˡ , identityʳ)) , identity²)) ⟩
        unitorˡ.from ∘ unitorˡ.from ∘ associator.from ∘ ((δ ⊗₁ δ) ⊗₁ id) ∘ ((g ⊗₁ f) ⊗₁ id) ∘ (Δ ⊗₁ id) ∘ Δ 
          ≈⟨ refl⟩∘⟨ (pullˡ coherence₁) ⟩
        unitorˡ.from ∘ (unitorˡ.from ⊗₁ id) ∘ ((δ ⊗₁ δ) ⊗₁ id) ∘ ((g ⊗₁ f) ⊗₁ id) ∘ (Δ ⊗₁ id) ∘ Δ
          ∎