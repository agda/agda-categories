{-# OPTIONS --safe --without-K #-}

open import Categories.Category using (Category)

module Categories.Adjoint.Instance.Slice {o ℓ e} (C : Category o ℓ e) where

open import Categories.Adjoint using (_⊣_)
open import Categories.Category.Slice C using (SliceObj; Slice⇒; slicearr)
open import Categories.Functor.Slice C using (Forgetful; Free)
open import Categories.NaturalTransformation using (ntHelper)
open import Categories.Object.Product C

open Category C
open HomReasoning

open SliceObj
open Slice⇒

module _ {A : Obj} (product : ∀ {X} → Product A X) where

  Forgetful⊣Free : Forgetful ⊣ Free product
  Forgetful⊣Free = record
    { unit = ntHelper record
      { η = λ _ → slicearr (Product.project₁ product)
      ; commute = λ {X} {Y} f → begin
        [ product ]⟨ arr Y , id ⟩ ∘ h f                            ≈⟨ [ product ]⟨⟩∘ ⟩
        [ product ]⟨ arr Y ∘ h f , id ∘ h f ⟩                      ≈⟨ Product.⟨⟩-cong₂ product (△ f) identityˡ ⟩
        [ product ]⟨ arr X , h f ⟩                                 ≈˘⟨ Product.⟨⟩-cong₂ product identityˡ identityʳ ⟩
        [ product ]⟨ id ∘ arr X , h f ∘ id ⟩                       ≈˘⟨ [ product ⇒ product ]×∘⟨⟩ ⟩
        [ product ⇒ product ] id × h f ∘ [ product ]⟨ arr X , id ⟩ ∎
      }
    ; counit = ntHelper record
      { η = λ _ → Product.π₂ product
      ; commute = λ _ → Product.project₂ product
      }
    ; zig = Product.project₂ product
    ; zag = begin
      [ product ⇒ product ]id× [ product ]π₂ ∘ [ product ]⟨ [ product ]π₁ , id ⟩ ≈⟨ [ product ⇒ product ]×∘⟨⟩ ⟩
      [ product ]⟨ id ∘ [ product ]π₁ , [ product ]π₂ ∘ id ⟩                     ≈⟨ Product.⟨⟩-cong₂ product identityˡ identityʳ ⟩
      [ product ]⟨ [ product ]π₁ , [ product ]π₂ ⟩                               ≈⟨ Product.η product ⟩
      id                                                                         ∎
    }
