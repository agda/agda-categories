{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Functor.Bifunctor

module Categories.Diagram.End {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′}
  (F : Bifunctor (Category.op C) C D) where

private
  module C = Category C
  module D = Category D
  open D
  open HomReasoning
  open Equiv
  variable
    A B : Obj
    f g : A ⇒ B

open import Level
open import Data.Product using (Σ; _,_)

open import Categories.Functor
open import Categories.Functor.Construction.Constant
open import Categories.NaturalTransformation.Dinatural
open import Categories.Morphism.Reasoning D

open Functor F

record Wedge : Set (levelOfTerm F) where
  field
    E         : Obj
    dinatural : DinaturalTransformation (const E) F

  module dinatural = DinaturalTransformation dinatural

Wedge-∘ : (W : Wedge) → A ⇒ Wedge.E W → Wedge
Wedge-∘ {A = A} W f = record
  { E         = A
  ; dinatural = extranaturalʳ (λ X → dinatural.α X ∘ f)
                              (sym-assoc ○ ∘-resp-≈ˡ (extranatural-commʳ dinatural) ○ assoc)
  }
  where open Wedge W

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
