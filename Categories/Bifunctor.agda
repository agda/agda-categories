{-# OPTIONS --without-K --safe #-}
module Categories.Bifunctor where

open import Level
open import Data.Product using (_,_; swap)

open import Categories.Category

open import Categories.Functor public
open import Categories.Product

private
  variable
    o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ : Level
    C  : Category o ℓ e
    D  : Category o′ ℓ′ e′
    D₁ : Category o′ ℓ′ e′
    D₂ : Category o′ ℓ′ e′
    E  : Category o″ ℓ″ e″
    E₁ : Category o″ ℓ″ e″
    E₂ : Category o″ ℓ″ e″

Bifunctor : Category o ℓ e → Category o′ ℓ′ e′ → Category o″ ℓ″ e″ → Set _
Bifunctor C D E = Functor (Product C D) E

overlap-× : ∀ (H : Bifunctor D₁ D₂ C) (F : Functor E D₁) (G : Functor E D₂) → Functor E C
overlap-× H F G = H ∘F (F ※ G)

reduce-× : ∀ (H : Bifunctor D₁ D₂ C) (F : Functor E₁ D₁) (G : Functor E₂ D₂) → Bifunctor E₁ E₂ C
reduce-× H F G = H ∘F (F ⁂ G)

flip-bifunctor : Bifunctor C D E → Bifunctor D C E
flip-bifunctor {C = C} {D = D} {E = E} b = _∘F_ b (Swap {C = C} {D = D})
