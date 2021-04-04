{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Functor.Bifunctor

module Categories.Diagram.End {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′}
  (F : Bifunctor (Category.op C) C D) where

private
  module D = Category D
  open D
  open HomReasoning
  open Equiv
  variable
    A B : Obj
    f g : A ⇒ B

open import Level

open import Categories.Diagram.Wedge F
open import Categories.NaturalTransformation.Dinatural

record End : Set (levelOfTerm F) where
  field
    wedge : Wedge

  module wedge = Wedge wedge
  open wedge public
  open Wedge

  field
    factor    : (W : Wedge) → E W ⇒ wedge.E
    universal : ∀ {W : Wedge} {A} → wedge.dinatural.α A ∘ factor W ≈ dinatural.α W A
    unique    : ∀ {W : Wedge} {g : E W ⇒ wedge.E} → (∀ {A} → wedge.dinatural.α A ∘ g ≈ dinatural.α W A) → factor W ≈ g

  η-id : factor wedge ≈ D.id
  η-id = unique identityʳ

  unique′ :(∀ {A} → wedge.dinatural.α A ∘ f ≈ wedge.dinatural.α A ∘ g) → f ≈ g
  unique′ {f = f} {g = g} eq = ⟺ (unique {W = Wedge-∘ wedge f} refl) ○ unique (⟺ eq)
