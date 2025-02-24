{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Functor.Bifunctor using (Bifunctor)

module Categories.Diagram.Coend {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′}
  (F : Bifunctor (Category.op C) C D) where

open Category D
open HomReasoning
open Equiv

private
  variable
    A B : Obj
    f g : A ⇒ B

open import Level

open import Categories.Diagram.Cowedge F

record Coend : Set (levelOfTerm F) where
  field
    cowedge : Cowedge

  module cowedge = Cowedge cowedge
  open cowedge public
  open Cowedge

  field
    factor    : (W : Cowedge) → cowedge.E ⇒ E W
    universal : ∀ {W : Cowedge} {A} → factor W ∘ cowedge.dinatural.α A ≈ dinatural.α W A
    unique    : ∀ {W : Cowedge} {g : cowedge.E ⇒ E W} → (∀ {A} → g ∘ cowedge.dinatural.α A ≈ dinatural.α W A) → factor W ≈ g

  η-id : factor cowedge ≈ id
  η-id = unique identityˡ

  unique′ :(∀ {A} → f ∘ cowedge.dinatural.α A ≈ g ∘ cowedge.dinatural.α A) → f ≈ g
  unique′ {f = f} {g = g} eq = ⟺ (unique {W = Cowedge-∘ cowedge f} refl) ○ unique (⟺ eq)
