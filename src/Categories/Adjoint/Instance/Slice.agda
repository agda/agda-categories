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

module _ {A : Obj} (product : ∀ {X} → Product A X) where

  private
    module product {X} = Product (product {X})
    open product

  TotalSpace⊣ConstantFamily : TotalSpace ⊣ ConstantFamily product
  TotalSpace⊣ConstantFamily = record
    { unit = ntHelper record
      { η = λ _ → slicearr project₁
      ; commute = λ {X} {Y} f → begin
        ⟨ arr Y , id ⟩ ∘ h f                            ≈⟨ ∘-distribʳ-⟨⟩ ⟩
        ⟨ arr Y ∘ h f , id ∘ h f ⟩                      ≈⟨ ⟨⟩-cong₂ (△ f) identityˡ ⟩
        ⟨ arr X , h f ⟩                                 ≈˘⟨ ⟨⟩-cong₂ identityˡ identityʳ ⟩
        ⟨ id ∘ arr X , h f ∘ id ⟩                       ≈˘⟨ [ product ⇒ product ]×∘⟨⟩ ⟩
        [ product ⇒ product ] id × h f ∘ ⟨ arr X , id ⟩ ∎
      }
    ; counit = ntHelper record
      { η = λ _ → π₂
      ; commute = λ _ → project₂
      }
    ; zig = project₂
    ; zag = begin
      [ product ⇒ product ]id× π₂ ∘ ⟨ π₁ , id ⟩ ≈⟨ [ product ⇒ product ]×∘⟨⟩ ⟩
      ⟨ id ∘ π₁ , π₂ ∘ id ⟩                     ≈⟨ ⟨⟩-cong₂ identityˡ identityʳ ⟩
      ⟨ π₁ , π₂ ⟩                               ≈⟨ η ⟩
      id                                        ∎
    }
