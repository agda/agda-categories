{-# OPTIONS --safe --without-K #-}

open import Categories.Category using (Category)

module Categories.Adjoint.Instance.Slice {o ℓ e} (C : Category o ℓ e) where

open import Categories.Adjoint using (_⊣_)
open import Categories.Category.Slice C using (SliceObj; Slice⇒; slicearr)
open import Categories.Functor.Slice C using (TotalSpace; ConstantFamily)
open import Categories.NaturalTransformation using (ntHelper)
open import Categories.Object.Product C

open Category C
open HomReasoning

open SliceObj
open Slice⇒

module _ {A : Obj} (product : ∀ {X} → Product X A) where

  private
    module product {X} = Product (product {X})
    open product

  TotalSpace⊣ConstantFamily : TotalSpace ⊣ ConstantFamily product
  TotalSpace⊣ConstantFamily = record
    { unit = ntHelper record
      { η = λ _ → slicearr project₂
      ; commute = λ {X} {Y} f → begin
        ⟨ id , arr Y ⟩ ∘ h f                            ≈⟨ ∘-distribʳ-⟨⟩ ⟩
        ⟨ id ∘ h f , arr Y ∘ h f ⟩                      ≈⟨ ⟨⟩-cong₂ identityˡ (△ f) ⟩
        ⟨ h f , arr X ⟩                                 ≈˘⟨ ⟨⟩-cong₂ identityʳ identityˡ ⟩
        ⟨ h f ∘ id , id ∘ arr X ⟩                       ≈˘⟨ [ product ⇒ product ]×∘⟨⟩ ⟩
        [ product ⇒ product ] h f × id ∘ ⟨ id , arr X ⟩ ∎
      }
    ; counit = ntHelper record
      { η = λ _ → π₁
      ; commute = λ _ → project₁
      }
    ; zig = project₁
    ; zag = begin
      [ product ⇒ product ] π₁ ×id ∘ ⟨ id , π₂ ⟩ ≈⟨ [ product ⇒ product ]×∘⟨⟩ ⟩
      ⟨ π₁ ∘ id , id ∘ π₂ ⟩                      ≈⟨ ⟨⟩-cong₂ identityʳ identityˡ ⟩
      ⟨ π₁ , π₂ ⟩                                ≈⟨ η ⟩
      id                                         ∎
    }
