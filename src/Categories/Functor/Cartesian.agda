{-# OPTIONS --without-K --safe #-}

-- A cartesian functor preserves products (of cartesian categories)
module Categories.Functor.Cartesian where

open import Level

open import Categories.Category.BinaryProducts
open import Categories.Category.Cartesian.Bundle using (CartesianCategory)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Properties

import Categories.Object.Product as P
import Categories.Object.Terminal as ⊤
import Categories.Morphism as M
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e o′ ℓ′ e′ : Level

record IsCartesianF (C : CartesianCategory o ℓ e) (D : CartesianCategory o′ ℓ′ e′)
  (F : Functor (CartesianCategory.U C) (CartesianCategory.U D)) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private
    module C = CartesianCategory C
    module D = CartesianCategory D
    open P D.U
    open M D.U
    open Functor F
    module PC = BinaryProducts C.products
    module PD = BinaryProducts D.products
    module TC = ⊤.Terminal C.terminal
    module TD = ⊤.Terminal D.terminal

  field
    F-resp-⊤ : ⊤.IsTerminal D.U (F₀ TC.⊤)
    F-resp-× : ∀ {A B} → IsProduct {P = F₀ (A PC.× B)} (F₁ PC.π₁) (F₁ PC.π₂)

  module F-resp-⊤ = ⊤.IsTerminal F-resp-⊤
  module F-resp-× {A B} = IsProduct (F-resp-× {A} {B})

  F-prod : ∀ A B → Product (F₀ A) (F₀ B)
  F-prod _ _ = IsProduct⇒Product F-resp-×

  module F-prod A B = Product (F-prod A B)

  F-resp-⟨⟩ : ∀ {A B X} → (f : X C.⇒ A) (g : X C.⇒ B) → PD.⟨ F₁ PC.π₁ , F₁ PC.π₂ ⟩ D.∘ F₁ PC.⟨ f , g ⟩ D.≈ PD.⟨ F₁ f , F₁ g ⟩
  F-resp-⟨⟩ f g = begin
    PD.⟨ F₁ PC.π₁ , F₁ PC.π₂ ⟩ D.∘ F₁ PC.⟨ f , g ⟩                    ≈⟨ PD.⟨⟩∘ ⟩
    PD.⟨ F₁ PC.π₁ D.∘ F₁ PC.⟨ f , g ⟩ , F₁ PC.π₂ D.∘ F₁ PC.⟨ f , g ⟩ ⟩ ≈⟨ PD.⟨⟩-cong₂ ([ F ]-resp-∘ PC.project₁) ([ F ]-resp-∘ PC.project₂) ⟩
    PD.⟨ F₁ f , F₁ g ⟩                                                ∎
    where open D.HomReasoning

  ⊤-iso : F₀ TC.⊤ ≅ TD.⊤
  ⊤-iso = ⊤.up-to-iso D.U (record { ⊤-is-terminal = F-resp-⊤ }) D.terminal

  module ⊤-iso = _≅_ ⊤-iso

  ×-iso : ∀ A B → F₀ (A PC.× B) ≅ F₀ A PD.× F₀ B
  ×-iso A B = record
    { from = PD.⟨ F₁ PC.π₁ , F₁ PC.π₂ ⟩
    ; to   = F-resp-×.⟨ PD.π₁ , PD.π₂ ⟩
    ; iso  = record
      { isoˡ = begin
        F-resp-×.⟨ PD.π₁ , PD.π₂ ⟩ D.∘ PD.⟨ F₁ PC.π₁ , F₁ PC.π₂ ⟩ ≈⟨ [ F-prod A B ]⟨⟩∘ ⟩
        F-resp-×.⟨ PD.π₁ D.∘ _ , PD.π₂ D.∘ _ ⟩                   ≈⟨ F-prod.⟨⟩-cong₂ A B PD.project₁ PD.project₂ ⟩
        F-resp-×.⟨ F₁ PC.π₁ , F₁ PC.π₂ ⟩                         ≈⟨ F-prod.η A B ⟩
        D.id                                                    ∎
      ; isoʳ = begin
        PD.⟨ F₁ PC.π₁ , F₁ PC.π₂ ⟩ D.∘ F-resp-×.⟨ PD.π₁ , PD.π₂ ⟩ ≈⟨ PD.⟨⟩∘ ⟩
        PD.⟨ F₁ PC.π₁ D.∘ _ , F₁ PC.π₂ D.∘ _ ⟩                   ≈⟨ PD.⟨⟩-cong₂ (F-prod.project₁ A B) (F-prod.project₂ A B) ⟩
        PD.⟨ PD.π₁ , PD.π₂ ⟩                                     ≈⟨ PD.η ⟩
        D.id                                                    ∎
      }
    }
    where open D.HomReasoning

  module ×-iso A B = _≅_ (×-iso A B)

  F-resp-⟨⟩′ : ∀ {A B X} → (f : X C.⇒ A) (g : X C.⇒ B) → F₁ PC.⟨ f , g ⟩ D.≈ F-resp-×.⟨ F₁ f , F₁ g ⟩
  F-resp-⟨⟩′ f g = begin
    F₁ PC.⟨ f , g ⟩                     ≈⟨ switch-fromtoˡ (×-iso _ _) (F-resp-⟨⟩ f g) ⟩
    ×-iso.to _ _ D.∘ PD.⟨ F₁ f , F₁ g ⟩ ≈⟨ ([ F-prod _ _ ]⟨⟩∘ ○ F-prod.⟨⟩-cong₂ _ _ PD.project₁ PD.project₂) ⟩
    F-resp-×.⟨ F₁ f , F₁ g ⟩            ∎
    where open MR D.U
          open D.HomReasoning

record CartesianF (C : CartesianCategory o ℓ e) (D : CartesianCategory o′ ℓ′ e′) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private
    module C = CartesianCategory C
    module D = CartesianCategory D

  field
    F           : Functor C.U D.U
    isCartesian : IsCartesianF C D F

  open Functor F public
  open IsCartesianF isCartesian public
