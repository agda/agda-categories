{-# OPTIONS --without-K --safe #-}

-- A cartesian functor preserves products (of cartesian categories)
module Categories.Functor.Cartesian where

open import Level

open import Categories.Category.Cartesian.Structure
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
    open ⊤ D.U
    open M D.U
    open Functor F

  field
    F-resp-⊤ : IsTerminal (F₀ C.⊤)
    F-resp-× : ∀ {A B} → IsProduct {P = F₀ (A C.× B)} (F₁ C.π₁) (F₁ C.π₂)

  module F-resp-⊤ = IsTerminal F-resp-⊤
  module F-resp-× {A B} = IsProduct (F-resp-× {A} {B})

  F-prod : ∀ A B → Product (F₀ A) (F₀ B)
  F-prod _ _ = IsProduct⇒Product F-resp-×

  module F-prod A B = Product (F-prod A B)

  F-resp-⟨⟩ : ∀ {A B X} → (f : X C.⇒ A) (g : X C.⇒ B) → D.⟨ F₁ C.π₁ , F₁ C.π₂ ⟩ D.∘ F₁ C.⟨ f , g ⟩ D.≈ D.⟨ F₁ f , F₁ g ⟩
  F-resp-⟨⟩ f g = begin
    D.⟨ F₁ C.π₁ , F₁ C.π₂ ⟩ D.∘ F₁ C.⟨ f , g ⟩                    ≈⟨ D.⟨⟩∘ ⟩
    D.⟨ F₁ C.π₁ D.∘ F₁ C.⟨ f , g ⟩ , F₁ C.π₂ D.∘ F₁ C.⟨ f , g ⟩ ⟩ ≈⟨ D.⟨⟩-cong₂ ([ F ]-resp-∘ C.project₁) ([ F ]-resp-∘ C.project₂) ⟩
    D.⟨ F₁ f , F₁ g ⟩                                             ∎
    where open D.HomReasoning

  ⊤-iso : F₀ C.⊤ ≅ D.⊤
  ⊤-iso = ⊤.up-to-iso D.U (record { ⊤-is-terminal = F-resp-⊤ }) D.terminal

  module ⊤-iso = _≅_ ⊤-iso

  ×-iso : ∀ A B → F₀ (A C.× B) ≅ F₀ A D.× F₀ B
  ×-iso A B = record
    { from = D.⟨ F₁ C.π₁ , F₁ C.π₂ ⟩
    ; to   = F-resp-×.⟨ D.π₁ , D.π₂ ⟩
    ; iso  = record
      { isoˡ = begin
        F-resp-×.⟨ D.π₁ , D.π₂ ⟩ D.∘ D.⟨ F₁ C.π₁ , F₁ C.π₂ ⟩ ≈⟨ [ F-prod A B ]⟨⟩∘ ⟩
        F-resp-×.⟨ D.π₁ D.∘ _ , D.π₂ D.∘ _ ⟩                 ≈⟨ F-prod.⟨⟩-cong₂ A B D.project₁ D.project₂ ⟩
        F-resp-×.⟨ F₁ C.π₁ , F₁ C.π₂ ⟩                       ≈⟨ F-prod.η A B ⟩
        D.id                                                 ∎
      ; isoʳ = begin
        D.⟨ F₁ C.π₁ , F₁ C.π₂ ⟩ D.∘ F-resp-×.⟨ D.π₁ , D.π₂ ⟩ ≈⟨ D.⟨⟩∘ ⟩
        D.⟨ F₁ C.π₁ D.∘ _ , F₁ C.π₂ D.∘ _ ⟩                  ≈⟨ D.⟨⟩-cong₂ (F-prod.project₁ A B) (F-prod.project₂ A B) ⟩
        D.⟨ D.π₁ , D.π₂ ⟩                                    ≈⟨ D.η ⟩
        D.id                                                 ∎
      }
    }
    where open D.HomReasoning

  module ×-iso A B = _≅_ (×-iso A B)

  F-resp-⟨⟩′ : ∀ {A B X} → (f : X C.⇒ A) (g : X C.⇒ B) → F₁ C.⟨ f , g ⟩ D.≈ F-resp-×.⟨ F₁ f , F₁ g ⟩
  F-resp-⟨⟩′ f g = begin
    F₁ C.⟨ f , g ⟩                     ≈⟨ switch-fromtoˡ (×-iso _ _) (F-resp-⟨⟩ f g) ⟩
    ×-iso.to _ _ D.∘ D.⟨ F₁ f , F₁ g ⟩ ≈⟨ ([ F-prod _ _ ]⟨⟩∘ ○ F-prod.⟨⟩-cong₂ _ _ D.project₁ D.project₂) ⟩
    F-resp-×.⟨ F₁ f , F₁ g ⟩           ∎
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
