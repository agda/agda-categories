{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Restriction using (Restriction)
open import Relation.Binary.Bundles using (Poset)
open import Relation.Binary.Structures using (IsPartialOrder)

import Categories.Morphism.Reasoning as MR

-- Every restriction category induces a partial order (the restriction order) on hom-sets

module Categories.Category.Restriction.Properties.Poset {o ℓ e} {𝒞 : Category o ℓ e} (R : Restriction 𝒞) where  
  open Category 𝒞
  open Restriction R
  open Equiv
  open HomReasoning
  open MR 𝒞 using (pullʳ; pullˡ)

  poset : (A B : Obj) → Poset ℓ e e
  poset A B = record 
    { Carrier = A ⇒ B 
    ; _≈_ = _≈_ 
    ; _≤_ = λ f g → f ≈ g ∘ f ↓
    ; isPartialOrder = record 
      { isPreorder = record 
        { isEquivalence = record 
          { refl = refl 
          ; sym = sym 
          ; trans = trans 
          } 
        ; reflexive = λ {x} {y} x≈y → begin 
          x       ≈˘⟨ pidʳ ⟩ 
          x ∘ x ↓ ≈⟨ x≈y ⟩∘⟨refl ⟩
          y ∘ x ↓ ∎
        ; trans = λ {i} {j} {k} i≈j∘i↓ j≈k∘j↓ → begin 
          i               ≈⟨ i≈j∘i↓ ⟩ 
          j ∘ i ↓         ≈⟨ j≈k∘j↓ ⟩∘⟨refl ⟩ 
          (k ∘ j ↓) ∘ i ↓ ≈⟨ pullʳ (sym ↓-denestʳ) ⟩ 
          k ∘ (j ∘ i ↓) ↓ ≈⟨ refl⟩∘⟨ ↓-cong (sym i≈j∘i↓) ⟩ 
          k ∘ i ↓         ∎ 
        } 
      ; antisym = λ {i} {j} i≈j∘i↓ j≈i∘j↓ → begin 
        i               ≈⟨ i≈j∘i↓ ⟩ 
        j ∘ i ↓         ≈⟨ j≈i∘j↓ ⟩∘⟨refl ⟩ 
        (i ∘ j ↓) ∘ i ↓ ≈⟨ pullʳ ↓-comm ⟩ 
        i ∘ i ↓ ∘ j ↓   ≈⟨ pullˡ pidʳ ⟩
        i ∘ j ↓         ≈˘⟨ j≈i∘j↓ ⟩
        j               ∎ 
      } 
    }
