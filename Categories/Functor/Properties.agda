{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Properties where

open import Categories.Category
open import Categories.Functor.Core
open import Categories.Morphisms

open import Relation.Binary using (_Preserves_⟶_)

module _ {o ℓ e o′ ℓ′ e′}
         {𝒞 : Category o ℓ e} {𝒟 : Category o′ ℓ′ e′}
         (F : Functor 𝒞 𝒟) where
  module 𝒞 = Category 𝒞
  module 𝒟 = Category 𝒟
  open 𝒞 hiding (_∘_)
  open Functor F

  module _ {A B C D : Obj}
           {f : A ⇒ B} {g : A ⇒ C} {h : B ⇒ D} {i : C ⇒ D} where

    [_]-resp-square : 𝒞.CommutativeSquare f g h i →
                      𝒟.CommutativeSquare (F₁ f) (F₁ g) (F₁ h) (F₁ i)
    [_]-resp-square sq = begin
      F₁ h ∘ F₁ f       ≈⟨ 𝒟.Equiv.sym homomorphism ⟩
      F₁ (𝒞 [ h ∘ f ]) ≈⟨ F-resp-≈ sq ⟩
      F₁ (𝒞 [ i ∘ g ]) ≈⟨ homomorphism ⟩
      F₁ i ∘ F₁ g       ∎
      where open 𝒟
            open 𝒟.HomReasoning

  [_]-resp-Iso : ∀ {A B} {f : A ⇒ B} {g : B ⇒ A} → Iso 𝒞 f g → Iso 𝒟 (F₁ f) (F₁ g)
  [_]-resp-Iso {f = f} {g} iso = record
    { isoˡ = begin
      F₁ g ∘ F₁ f       ≈⟨ sym homomorphism ⟩
      F₁ (𝒞 [ g ∘ f ]) ≈⟨ F-resp-≈ isoˡ ⟩
      F₁ 𝒞.id          ≈⟨ identity ⟩
      𝒟.id             ∎
    ; isoʳ = begin
      F₁ f ∘ F₁ g       ≈⟨ sym homomorphism ⟩
      F₁ (𝒞 [ f ∘ g ]) ≈⟨ F-resp-≈ isoʳ ⟩
      F₁ 𝒞.id          ≈⟨ identity ⟩
      𝒟.id             ∎
    }
    where open Iso iso
          open 𝒟
          open 𝒟.HomReasoning
          
  [_]-resp-≅ : F₀ Preserves _≅_ 𝒞 ⟶ _≅_ 𝒟
  [_]-resp-≅ i≅j = record
    { f   = F₁ f
    ; g   = F₁ g
    ; iso = [_]-resp-Iso iso
    }
    where open _≅_ i≅j
