{-# OPTIONS --without-K --safe #-}
open import Categories.Category

-- You can transform functions out of discrete
-- categories into functors.
module Categories.Functor.Construction.Select {o ℓ e} (𝒞 : Category o ℓ e) where

open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Categories.Category.Discrete
open import Categories.Functor using (Functor)

private
  module 𝒞 = Category 𝒞

open Category 𝒞
open 𝒞.HomReasoning

Select : ∀ {o} {A : Set o} → (A → Obj) → Functor (Discrete A) 𝒞
Select {o} {A = A} select = record
  { F₀ = select
  ; F₁ = F₁
  ; identity = refl
  ; homomorphism = λ {X} {Y} {Z} {f} {g} → homomorphism f g
  ; F-resp-≈ = λ { ≡.refl → refl }
  }
  where
    F₁ : ∀ {X Y} → (f : Discrete A [ X , Y ]) → 𝒞 [ select X , select Y ]
    F₁ {X} {.X} ≡.refl = id

    homomorphism : ∀ {X Y Z} → (f : Discrete A [ X , Y ]) → (g : Discrete A [ Y , Z ])
                   → F₁ (Discrete A [ g ∘ f ]) ≈ 𝒞 [ F₁ g ∘ F₁ f ]
    homomorphism ≡.refl ≡.refl = sym 𝒞.identity²
