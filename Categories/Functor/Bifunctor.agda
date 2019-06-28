{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Bifunctor where

open import Level
open import Data.Product using (_,_; swap)

open import Categories.Category

open import Categories.Functor public
open import Categories.Category.Product

private
  variable
    o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ : Level
    C D D₁ D₂ E E₁ E₂ : Category o ℓ e

Bifunctor : Category o ℓ e → Category o′ ℓ′ e′ → Category o″ ℓ″ e″ → Set _
Bifunctor C D E = Functor (Product C D) E

overlap-× : ∀ (H : Bifunctor D₁ D₂ C) (F : Functor E D₁) (G : Functor E D₂) → Functor E C
overlap-× H F G = H ∘F (F ※ G)

reduce-× : ∀ (H : Bifunctor D₁ D₂ C) (F : Functor E₁ D₁) (G : Functor E₂ D₂) → Bifunctor E₁ E₂ C
reduce-× H F G = H ∘F (F ⁂ G)

flip-bifunctor : Bifunctor C D E → Bifunctor D C E
flip-bifunctor {C = C} {D = D} {E = E} b = _∘F_ b (Swap {C = C} {D = D})

appˡ : Bifunctor C D E → Category.Obj C → Functor D E
appˡ F c = F ∘F constˡ c

appʳ : Bifunctor C D E → Category.Obj D → Functor C E
appʳ F d = F ∘F constʳ d
