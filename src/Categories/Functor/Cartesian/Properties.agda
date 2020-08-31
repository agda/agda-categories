{-# OPTIONS --without-K --safe #-}

-- Some of the obvious properties of cartesian functors
module Categories.Functor.Cartesian.Properties where

open import Level
open import Data.Product using (Σ ; _,_)

open import Categories.Category
open import Categories.Category.Cartesian.Structure
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Properties
open import Categories.Functor.Cartesian
open import Categories.Functor.Monoidal
open import Categories.NaturalTransformation

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

module _ {C : CartesianCategory o ℓ e} {D : CartesianCategory o′ ℓ′ e′} where
  private
    module C = CartesianCategory C
    module D = CartesianCategory D
    open D.HomReasoning
    open MR D.U
    open M D.U

  isMonoidalFunctor : CartesianF C D → MonoidalFunctor C.monoidalCategory D.monoidalCategory
  isMonoidalFunctor F = record
    { F          = F.F
    ; isMonoidal = record
      { ε             = F.⊤-iso.to
      ; ⊗-homo        = ntHelper record
        { η       = λ { (X , Y) → F.×-iso.to X Y }
        ; commute = λ { {X , Y} {Z , W} (f , g) →
          F.F-prod.unique′ _ _
            (begin
              F.₁ C.π₁ D.∘ F.×-iso.to Z W D.∘ (F.₁ f D.⁂ F.₁ g) ≈⟨ pullˡ F.F-resp-×.project₁ ⟩
              D.π₁ D.∘ (F.₁ f D.⁂ F.₁ g)                        ≈⟨ D.project₁ ⟩
              F.₁ f D.∘ D.π₁                                    ≈˘⟨ pullʳ F.F-resp-×.project₁ ⟩
              (F.₁ f D.∘ F.₁ C.π₁) D.∘ F.×-iso.to X Y           ≈˘⟨ pullˡ ([ F.F ]-resp-square C.project₁) ⟩
              F.₁ C.π₁ D.∘ F.₁ (f C.⁂ g) D.∘ F.×-iso.to X Y     ∎)
            (begin
              F.₁ C.π₂ D.∘ F.×-iso.to Z W D.∘ (F.₁ f D.⁂ F.₁ g) ≈⟨ pullˡ F.F-resp-×.project₂ ⟩
              D.π₂ D.∘ (F.₁ f D.⁂ F.₁ g)                        ≈⟨ D.project₂ ⟩
              F.₁ g D.∘ D.π₂                                    ≈˘⟨ pullʳ F.F-resp-×.project₂ ⟩
              (F.₁ g D.∘ F.₁ C.π₂) D.∘ F.×-iso.to X Y           ≈˘⟨ pullˡ ([ F.F ]-resp-square C.project₂) ⟩
              F.₁ C.π₂ D.∘ F.₁ (f C.⁂ g) D.∘ F.×-iso.to X Y     ∎)
          }
        }
      ; associativity = λ {X Y Z} → let open P D.U in begin
        F.₁ C.associator.from D.∘ F.×-iso.to (X C.× Y) Z D.∘ (F.×-iso.to X Y D.⁂ D.id)
          ≈⟨ F.F-resp-⟨⟩′ _ _ ⟩∘⟨ [ D.product ⇒ D.product ⇒ F.F-prod _ _ ]repack∘× ⟩
        F.F-resp-×.⟨ F.₁ (C.π₁ C.∘ C.π₁) , F.₁ C.⟨ C.π₂ C.∘ C.π₁ , C.π₂ ⟩ ⟩ D.∘ F.F-resp-×.⟨ F.×-iso.to X Y D.∘ D.π₁ , D.id D.∘ D.π₂ ⟩
          ≈⟨ F.F-prod.⟨⟩-cong₂ _ _ F.homomorphism (F.F-resp-⟨⟩′ _ _ ○ F.F-prod.⟨⟩-cong₂ _ _ F.homomorphism D.Equiv.refl) ⟩∘⟨refl ⟩
        F.F-resp-×.⟨ F.₁ C.π₁ D.∘ F.₁ C.π₁ , F.F-resp-×.⟨ F.₁ C.π₂ D.∘ F.₁ C.π₁ , F.₁ C.π₂ ⟩ ⟩ D.∘ F.F-resp-×.⟨ F.×-iso.to X Y D.∘ D.π₁ , D.id D.∘ D.π₂ ⟩
          ≈⟨ [ F.F-prod _ _ ]⟨⟩∘ ⟩
        F.F-resp-×.⟨ (F.₁ C.π₁ D.∘ F.₁ C.π₁) D.∘ _ , F.F-resp-×.⟨ F.₁ C.π₂ D.∘ F.₁ C.π₁ , F.₁ C.π₂ ⟩ D.∘ _ ⟩
          ≈⟨ F.F-prod.⟨⟩-cong₂ _ _ (pullʳ F.F-resp-×.project₁ ○ pullˡ F.F-resp-×.project₁)
                                   [ F.F-prod _ _ ]⟨⟩∘ ⟩
        F.F-resp-×.⟨ D.π₁ D.∘ D.π₁ , F.F-resp-×.⟨ (F.₁ C.π₂ D.∘ F.₁ C.π₁) D.∘ _ , F.₁ C.π₂ D.∘ _ ⟩ ⟩
          ≈⟨ F.F-prod.⟨⟩-cong₂ _ _ D.Equiv.refl
            (F.F-prod.⟨⟩-cong₂ _ _ (pullʳ F.F-resp-×.project₁ ○ pullˡ F.F-resp-×.project₂)
                                   (F.F-resp-×.project₂ ○ D.identityˡ)) ⟩
        F.F-resp-×.⟨ D.π₁ D.∘ D.π₁ , F.F-resp-×.⟨ D.π₂ D.∘ D.π₁ , D.π₂ ⟩ ⟩
          ≈˘⟨ F.F-prod.⟨⟩-cong₂ _ _ D.identityˡ ([ F.F-prod _ _ ]⟨⟩∘ ○ (F.F-prod.⟨⟩-cong₂ _ _ D.project₁ D.project₂)) ⟩
        F.F-resp-×.⟨ D.id D.∘ D.π₁ D.∘ D.π₁ , F.×-iso.to Y Z D.∘ D.⟨ D.π₂ D.∘ D.π₁ , D.π₂ ⟩ ⟩
          ≈˘⟨ [ D.product ⇒ (F.F-prod _ _) ]×∘⟨⟩ ⟩
        F.F-resp-×.⟨ D.id D.∘ D.π₁ , F.×-iso.to Y Z D.∘ D.π₂ ⟩ D.∘ D.associator.from
          ≈˘⟨ pullˡ [ D.product ⇒ D.product ⇒ F.F-prod _ _ ]repack∘× ⟩
        F.×-iso.to X (Y C.× Z) D.∘ (D.id D.⁂ F.×-iso.to Y Z) D.∘ D.associator.from
          ∎
      ; unitaryˡ      = begin
        F.₁ C.π₂ D.∘ F.F-resp-×.⟨ D.π₁ , D.π₂ ⟩ D.∘ (F.F-resp-⊤.! D.⁂ D.id) ≈⟨ pullˡ F.F-resp-×.project₂ ⟩
        D.π₂ D.∘ (F.F-resp-⊤.! D.⁂ D.id)                                    ≈⟨ D.project₂ ⟩
        D.id D.∘ D.π₂                                                       ≈⟨ D.identityˡ ⟩
        D.π₂                                                                ∎
      ; unitaryʳ      = begin
        F.₁ C.π₁ D.∘ F.F-resp-×.⟨ D.π₁ , D.π₂ ⟩ D.∘ (D.id D.⁂ F.F-resp-⊤.!) ≈⟨ pullˡ F.F-resp-×.project₁ ⟩
        D.π₁ D.∘ (D.id D.⁂ F.F-resp-⊤.!)                                    ≈⟨ D.project₁ ⟩
        D.id D.∘ D.π₁                                                       ≈⟨ D.identityˡ ⟩
        D.π₁                                                                ∎
      }
    }
    where module F = CartesianF F

  isStrongMonoidalFunctor : CartesianF C D → StrongMonoidalFunctor C.monoidalCategory D.monoidalCategory
  isStrongMonoidalFunctor F = record
    { F                = F.F
    ; isStrongMonoidal = record
      { ε             = ≅.sym F.⊤-iso
      ; ⊗-homo        = record
        { F⇒G = MF.⊗-homo
        ; F⇐G = ntHelper record
          { η       = λ { (X , Y) → F.×-iso.from X Y }
          ; commute = λ { {X , Y} {Z , W} (f , g) →
            begin
              D.⟨ F.₁ C.π₁ , F.₁ C.π₂ ⟩ D.∘ F.₁ (f C.⁂ g)                   ≈⟨ D.⟨⟩∘ ⟩
              D.⟨ F.₁ C.π₁ D.∘ F.₁ (f C.⁂ g) , F.₁ C.π₂ D.∘ F.₁ (f C.⁂ g) ⟩ ≈⟨ D.⟨⟩-cong₂ ([ F.F ]-resp-square C.project₁) ([ F.F ]-resp-square C.project₂) ⟩
              D.⟨ F.₁ f D.∘ F.F₁ C.π₁ , F.₁ g D.∘ F.F₁ C.π₂ ⟩               ≈˘⟨ D.⁂∘⟨⟩ ⟩
              (F.₁ f D.⁂ F.₁ g) D.∘ D.⟨ F.F₁ C.π₁ , F.F₁ C.π₂ ⟩             ∎ }
          }
        ; iso = λ { (X , Y) → record
          { isoˡ = F.×-iso.isoʳ X Y
          ; isoʳ = F.×-iso.isoˡ X Y
          } }
        }
      ; associativity = MF.associativity
      ; unitaryˡ      = MF.unitaryˡ
      ; unitaryʳ      = MF.unitaryʳ
      }
    }
    where module F  = CartesianF F
          module MF = MonoidalFunctor (isMonoidalFunctor F)
