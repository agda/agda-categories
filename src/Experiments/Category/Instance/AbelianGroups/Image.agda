{-# OPTIONS --without-K --safe #-}

-- The image of a homomorphism
module Experiments.Category.Instance.AbelianGroups.Image where

open import Data.Product using (Σ-syntax; _,_; _×_; proj₁; proj₂)

open import Level

open import Algebra.Properties.AbelianGroup
open import Experiments.Category.Instance.AbelianGroups

open AbelianGroupHomomorphism

Image : ∀ {c ℓ} {G H : AbelianGroup c ℓ} → AbelianGroupHomomorphism G H → AbelianGroup (c ⊔ ℓ) ℓ
Image {c = c} {ℓ = ℓ} {G = G} {H = H} f =
  subgroup H in-image in-image-∙-closed in-image-ε-closed in-image-⁻¹-closed
  where
    module G = AbelianGroup G
    module H = AbelianGroup H
   
    in-image : H.Carrier → Set (c ⊔ ℓ)
    in-image h = Σ[ g ∈ G.Carrier ] (⟦ f ⟧ g H.≈ h)

    in-image-∙-closed : ∀ h₁ h₂ → in-image h₁ → in-image h₂ → in-image (h₁ H.∙ h₂)
    in-image-∙-closed h₁ h₂ (g₁ , eq₁) (g₂ , eq₂) = (g₁ G.∙ g₂) , {!!}

    in-image-ε-closed : in-image H.ε
    in-image-ε-closed = {!!}

    in-image-⁻¹-closed : ∀ h → in-image h → in-image (h H.⁻¹)
    in-image-⁻¹-closed h (g , eq) = {!!}
