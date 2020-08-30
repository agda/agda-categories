{-# OPTIONS --without-K --safe #-}

-- Some of the obvious properties of cartesian functors
module Categories.Functor.Cartesian.Properties where

open import Level

open import Categories.Category
open import Categories.Category.Cartesian.Structure
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Properties
open import Categories.Functor.Cartesian

import Categories.Morphism as M
import Categories.Morphism.Reasoning as MR
import Categories.Object.Terminal as ⊤
import Categories.Object.Product as P

private
  variable
    o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ : Level

module _ (C : CartesianCategory o ℓ e) where
  open CartesianCategory C
  open P U

  idF-IsCartesianF : IsCartesianF C C idF
  idF-IsCartesianF = record
    { F-resp-⊤ = terminal.⊤-is-terminal
    ; F-resp-× = Product⇒IsProduct product
    }

  idF-CartesianF : CartesianF C C
  idF-CartesianF = record
    { isCartesian = idF-IsCartesianF
    }

module _ (A : CartesianCategory o ℓ e) (B : CartesianCategory o′ ℓ′ e′) (C : CartesianCategory o″ ℓ″ e″) where
  private
    module A = CartesianCategory A
    module B = CartesianCategory B
    module C = CartesianCategory C
    open P C.U

  ∘-IsCartesianF : ∀ {F : Functor A.U B.U} {G : Functor B.U C.U} →
                    IsCartesianF B C G → IsCartesianF A B F →
                    IsCartesianF A C (G ∘F F)
  ∘-IsCartesianF {F} {G} CG CF = record
    { F-resp-⊤ = ⊤.Terminal.⊤-is-terminal (⊤.transport-by-iso C.U C.terminal
                                          (M.≅.trans C.U (M.≅.sym C.U CG.⊤-iso) ([ G ]-resp-≅ (M.≅.sym B.U CF.⊤-iso))))
    ; F-resp-× = record
      { ⟨_,_⟩    = λ f g → G.₁ (CF.×-iso.to _ _) C.∘ CG.×-iso.to _ _ C.∘ C.⟨ f , g ⟩
      ; project₁ = λ {_ f g} → begin
        G.₁ (F.₁ A.π₁) C.∘ G.₁ (CF.×-iso.to _ _) C.∘ CG.×-iso.to _ _ C.∘ C.⟨ f , g ⟩ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ([ CG.F-prod _ _ ]⟨⟩∘ ○ CG.F-prod.⟨⟩-cong₂ _ _ C.project₁ C.project₂) ⟩
        G.₁ (F.₁ A.π₁) C.∘ G.₁ (CF.×-iso.to _ _) C.∘ CG.F-resp-×.⟨ f , g ⟩           ≈⟨ pullˡ ([ G ]-resp-∘ CF.F-resp-×.project₁) ⟩
        G.₁ B.π₁ C.∘ CG.F-resp-×.⟨ f , g ⟩                                           ≈⟨ CG.F-resp-×.project₁ ⟩
        f ∎
      ; project₂ = λ {_ f g} → begin
        G.₁ (F.₁ A.π₂) C.∘ G.₁ (CF.×-iso.to _ _) C.∘ CG.×-iso.to _ _ C.∘ C.⟨ f , g ⟩ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ([ CG.F-prod _ _ ]⟨⟩∘ ○ CG.F-prod.⟨⟩-cong₂ _ _ C.project₁ C.project₂) ⟩
        G.₁ (F.₁ A.π₂) C.∘ G.₁ (CF.×-iso.to _ _) C.∘ CG.F-resp-×.⟨ f , g ⟩           ≈⟨ pullˡ ([ G ]-resp-∘ CF.F-resp-×.project₂) ⟩
        G.₁ B.π₂ C.∘ CG.F-resp-×.⟨ f , g ⟩                                           ≈⟨ CG.F-resp-×.project₂ ⟩
        g ∎
      ; unique   = λ {_ h f g} eq₁ eq₂ → begin
        G.₁ (CF.×-iso.to _ _) C.∘ CG.×-iso.to _ _ C.∘ C.⟨ f , g ⟩
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.unique′ (C.project₁ ○ ⟺ eq₁ ○ pushˡ (⟺ ([ G ]-resp-∘ B.project₁)) ○ pushˡ (⟺ C.project₁))
                                       (C.project₂ ○ ⟺ eq₂ ○ pushˡ (⟺ ([ G ]-resp-∘ B.project₂)) ○ pushˡ (⟺ C.project₂)) ⟩
        G.₁ (CF.×-iso.to _ _) C.∘ CG.×-iso.to _ _ C.∘ CG.×-iso.from _ _ C.∘ G.₁ (CF.×-iso.from _ _) C.∘ h
          ≈⟨ refl⟩∘⟨ cancelˡ (CG.×-iso.isoˡ _ _) ⟩
        G.₁ (CF.×-iso.to _ _) C.∘ G.₁ (CF.×-iso.from _ _) C.∘ h
          ≈⟨ cancelˡ (M._≅_.isoˡ ([ G ]-resp-≅ (CF.×-iso _ _))) ⟩
        h
          ∎
      }
    }
    where module F  = Functor F
          module G  = Functor G
          module CG = IsCartesianF CG
          module CF = IsCartesianF CF
          open C.HomReasoning
          open MR C.U

∘-CartesianF : {A : CartesianCategory o ℓ e} {B : CartesianCategory o′ ℓ′ e′} {C : CartesianCategory o″ ℓ″ e″} →
               CartesianF B C → CartesianF A B → CartesianF A C
∘-CartesianF G F = record { isCartesian = ∘-IsCartesianF _ _ _ (CartesianF.isCartesian G) (CartesianF.isCartesian F) }
