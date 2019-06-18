{-# OPTIONS --without-K --safe #-}
module Categories.NaturalTransformation where

open import Categories.Category using (Category)
open import Categories.Functor renaming (id to idF)
open import Categories.NaturalTransformation.Core public

-- left and right unitors are very general
module _ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′}
  (F : Functor C D) where

  private module D = Category D
  open Category.HomReasoning D
  open Functor F

  -- Often called λ but that is likely too overloaded
  unitorˡ : NaturalTransformation F (F ∘F idF)
  unitorˡ = record
    { η = λ X → D.id
    ; commute = λ f →  begin
      D.id D.∘ F₁ f   ≈⟨ D.identityˡ ⟩
      F₁ f            ≈˘⟨ D.identityʳ ⟩
      F₁ f D.∘ D.id ∎
    }

  -- ρ
  unitorʳ : NaturalTransformation F (idF ∘F F)
  unitorʳ = record
    { η = λ _ → D.id
    ; commute = λ f → begin
      D.id D.∘ F₁ f   ≈⟨ D.identityˡ ⟩
      F₁ f            ≈˘⟨ D.identityʳ ⟩
      F₁ f D.∘ D.id ∎
    }

-- associator only for Endofunctor
module _ {o ℓ e} {C : Category o ℓ e} (F : Endofunctor C) where
  private module C = Category C
  open Category.HomReasoning C
  open Functor F
  -- α
  associator : NaturalTransformation ((F ∘F F) ∘F F) (F ∘F (F ∘F F))
  associator = record
    { η = λ _ → C.id
    ; commute = λ f → begin
      C.id C.∘ _   ≈⟨ C.identityˡ ⟩
      _            ≈˘⟨ C.identityʳ ⟩
      _ C.∘ C.id ∎
    }
