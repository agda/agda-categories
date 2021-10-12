{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Bifunctor where

-- Bifunctor, aka a Functor from C × D to E
open import Level
open import Data.Product using (_,_)

open import Categories.Category
open import Categories.Functor
open import Categories.Functor.Construction.Constant
open import Categories.Category.Product

private
  variable
    o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ o‴ ℓ‴ e‴ o⁗ ℓ⁗ e⁗ : Level
    C : Category o ℓ e
    D D₁ D₂ : Category o′ ℓ′ e′
    E E₁ E₂ : Category o″ ℓ″ e″
    A A₁ A₂ : Category o‴ ℓ‴ e‴
    B B₁ B₂ : Category o⁗ ℓ⁗ e⁗

Bifunctor : Category o ℓ e → Category o′ ℓ′ e′ → Category o″ ℓ″ e″ → Set _
Bifunctor C D E = Functor (Product C D) E

module Bifunctor (H : Bifunctor C D E) where
  open Functor H public

  overlap-× : ∀ (F : Functor A C) (G : Functor A D) → Functor A E
  overlap-× F G = H ∘F (F ※ G)

  module overlap-× {o‴ ℓ‴ e‴} {A : Category o‴ ℓ‴ e‴} (F : Functor A C) (G : Functor A D) = Functor (overlap-× F G)

  reduce-× : ∀ (F : Functor A C) (G : Functor B D) → Bifunctor A B E
  reduce-× F G = H ∘F (F ⁂ G)

  flip : Bifunctor D C E
  flip = H ∘F Swap

  appˡ : Category.Obj C → Functor D E
  appˡ c = H ∘F constˡ c

  module appˡ (c : Category.Obj C) = Functor (appˡ c)

  appʳ : Category.Obj D → Functor C E
  appʳ d = H ∘F constʳ d

  module appʳ (d : Category.Obj D) = Functor (appʳ d)

  ₁ˡ : ∀ {A B d} (f : C [ A , B ]) → E [ F₀ (A , d) , F₀ (B , d) ]
  ₁ˡ f = ₁ (f , Category.id D)

  ₁ʳ : ∀ {A B c} (f : D [ A , B ]) → E [ F₀ (c , A) , F₀ (c , B) ]
  ₁ʳ f = ₁ (Category.id C , f)

  homomorphismˡ : ∀ {X Y Z d} {f : C [ X , Y ]} {g : C [ Y , Z ]} →
                     E [ ₁ˡ {d = d} (C [ g ∘ f ]) ≈ E [ ₁ˡ g ∘ ₁ˡ f ] ]
  homomorphismˡ = trans E (resp-≈ (refl C , sym D (Category.identity² D))) homomorphism
    where open Category.Equiv

  homomorphismʳ : ∀ {X Y Z c} {f : D [ X , Y ]} {g : D [ Y , Z ]} →
                     E [ ₁ʳ {c = c} (D [ g ∘ f ]) ≈ E [ ₁ʳ g ∘ ₁ʳ f ] ]
  homomorphismʳ = trans E (resp-≈ (sym C (Category.identity² C) , refl D)) homomorphism
    where open Category.Equiv

  resp-≈ˡ : ∀ {A B d} {f g : C [ A , B ]} → C [ f ≈ g ] → E [ ₁ˡ {d = d} f ≈ ₁ˡ g ]
  resp-≈ˡ f≈g = resp-≈ (f≈g , Category.Equiv.refl D)

  resp-≈ʳ : ∀ {A B c} {f g : D [ A , B ]} → D [ f ≈ g ] → E [ ₁ʳ {c = c} f ≈ ₁ʳ g ]
  resp-≈ʳ f≈g = resp-≈ (Category.Equiv.refl C , f≈g)

open Bifunctor public using (overlap-×; reduce-×; appˡ; appʳ) renaming (flip to flip-bifunctor)
