{-# OPTIONS --without-K --safe #-}
module Categories.Functor where

open import Level
open import Data.Product using (_×_; Σ)
open import Function.Surjection using (Surjective)
open import Function.Equality using (_⟶_)
open import Relation.Nullary

open import Categories.Category
open import Categories.Functor.Core public
import Categories.Morphism as Morphism

private
  variable
    o ℓ e o′ ℓ′ e′ : Level
    C D : Category o ℓ e

Contravariant : ∀ (C : Category o ℓ e) (D : Category o′ ℓ′ e′) → Set _
Contravariant C D = Functor (Category.op C) D

Faithful : Functor C D → Set _
Faithful {C = C} {D = D} F = ∀ {X Y} → (f g : C [ X , Y ]) → D [ F₁ f ≈ F₁ g ] → C [ f ≈ g ]
  where open Functor F

Full : Functor C D → Set _
Full {C = C} {D = D} F = ∀ {X Y} → Surjective {To = D.hom-setoid {F₀ X} {F₀ Y}} G
  where
    module C = Category C
    module D = Category D
    open Functor F
    G : ∀ {X Y} → (C.hom-setoid {X} {Y}) ⟶ D.hom-setoid {F₀ X} {F₀ Y}
    G = record { _⟨$⟩_ = F₁ ; cong = F-resp-≈ }

FullyFaithful : Functor C D → Set _
FullyFaithful F = Full F × Faithful F

-- Note that this is a constructive version of Essentially Surjective, which is
-- quite a strong assumption.
EssentiallySurjective : Functor C D → Set _
EssentiallySurjective {C = C} {D = D} F = (d : Obj) → Σ C.Obj (λ c → Functor.F₀ F c ≅ d)
  where
  open Morphism D
  open Category D
  module C = Category C
