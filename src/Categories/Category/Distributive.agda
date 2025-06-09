{-# OPTIONS --without-K --safe #-}

open import Level using (levelOfTerm)
open import Categories.Category.Core using (Category)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.Cocartesian using (Cocartesian)
import Categories.Morphism as M
import Categories.Morphism.Reasoning as MR

-- A distributive category is a cartesian, cocartesian category
-- where the canonical distributivity morphism is an iso
-- https://ncatlab.org/nlab/show/distributive+category

module Categories.Category.Distributive {o ℓ e} (𝒞 : Category o ℓ e) where
open Category 𝒞
open M 𝒞
open MR 𝒞
open HomReasoning

record Distributive : Set (levelOfTerm 𝒞) where
  field
    cartesian : Cartesian 𝒞
    cocartesian : Cocartesian 𝒞

  open Cartesian cartesian using (products)
  open BinaryProducts products
  open Cocartesian cocartesian

  distributeˡ : ∀ {A B C : Obj} → A × B + A × C ⇒ A × (B + C)
  distributeˡ = [ id ⁂ i₁ , id ⁂ i₂ ]

  field
    isIsoˡ : ∀ {A B C : Obj} → IsIso (distributeˡ {A} {B} {C})

  -- The following is then also an iso
  distributeʳ : ∀ {A B C : Obj} →  B × A + C × A ⇒ (B + C) × A
  distributeʳ = [ i₁ ⁂ id , i₂ ⁂ id ]

  isIsoʳ : ∀ {A B C : Obj} →  IsIso (distributeʳ {A} {B} {C})
  isIsoʳ {A} {B} {C} = record
    { inv = ((swap +₁ swap) ∘ inv) ∘ swap
    ; iso = record
      { isoˡ = begin
        (((swap +₁ swap) ∘ inv) ∘ swap) ∘ [ i₁ ⁂ id , i₂ ⁂ id ]                                       ≈⟨ ∘[] ⟩
        [ (((swap +₁ swap) ∘ inv) ∘ swap) ∘ (i₁ ⁂ id) , (((swap +₁ swap) ∘ inv) ∘ swap) ∘ (i₂ ⁂ id) ] ≈⟨ []-cong₂ (pullʳ swap∘⁂) (pullʳ swap∘⁂) ⟩
        [ ((swap +₁ swap) ∘ inv) ∘ (id ⁂ i₁) ∘ swap , ((swap +₁ swap) ∘ inv) ∘ (id ⁂ i₂) ∘ swap ]     ≈˘⟨ ∘[] ⟩
        ((swap +₁ swap) ∘ inv) ∘ [ (id ⁂ i₁) ∘ swap , (id ⁂ i₂) ∘ swap ]                              ≈˘⟨ refl⟩∘⟨ []∘+₁ ⟩
        ((swap +₁ swap) ∘ inv) ∘ [ (id ⁂ i₁) , (id ⁂ i₂) ] ∘ (swap +₁ swap)                           ≈⟨ cancelInner isoˡ ⟩
        (swap +₁ swap) ∘ (swap +₁ swap)                                                               ≈⟨ +₁∘+₁ ⟩
        (swap ∘ swap) +₁ (swap ∘ swap)                                                                ≈⟨ +₁-cong₂ swap∘swap swap∘swap ⟩
        (id +₁ id)                                                                                    ≈⟨ +-unique id-comm-sym id-comm-sym ⟩
        id                                                                                            ∎
      ; isoʳ = begin
        [ i₁ ⁂ id , i₂ ⁂ id ] ∘ ((swap +₁ swap) ∘ inv) ∘ swap  ≈⟨ pull-first []∘+₁ ⟩
        [ (i₁ ⁂ id) ∘ swap , (i₂ ⁂ id) ∘ swap ] ∘ inv ∘ swap   ≈˘⟨ []-cong₂ swap∘⁂ swap∘⁂ ⟩∘⟨refl ⟩
        [ swap ∘ (id ⁂ i₁) , swap ∘ (id ⁂ i₂) ] ∘ inv ∘ swap   ≈˘⟨ ∘[] ⟩∘⟨refl ⟩
        (swap ∘ [ (id ⁂ i₁) , (id ⁂ i₂) ]) ∘ inv ∘ swap        ≈⟨ cancelInner isoʳ  ⟩
        swap ∘ swap                                            ≈⟨ swap∘swap ⟩
        id                                                     ∎
      }
    }
    where
      open IsIso (isIsoˡ {A} {B} {C})

  -- The inverse is what one is usually interested in
  distributeˡ⁻¹ : ∀ {A B C : Obj} → A × (B + C) ⇒ A × B + A × C
  distributeˡ⁻¹ = IsIso.inv isIsoˡ

  distributeʳ⁻¹ : ∀ {A B C : Obj} → (B + C) × A ⇒ B × A + C × A
  distributeʳ⁻¹ = IsIso.inv isIsoʳ
