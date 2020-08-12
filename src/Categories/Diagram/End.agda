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

record Wedge-Morphism (W₁ W₂ : Wedge) : Set (levelOfTerm F) where
  private
    module W₁ = Wedge W₁
    module W₂ = Wedge W₂
    open DinaturalTransformation
  field
    u : W₁.E ⇒ W₂.E
    commute : ∀ {C} → W₂.dinatural.α C ∘ u ≈ W₁.dinatural.α C

Wedge-id : ∀ {W} → Wedge-Morphism W W
Wedge-id {W} = record { u = D.id ; commute = D.identityʳ }

Wedge-Morphism-∘ : {A B C : Wedge} → Wedge-Morphism B C → Wedge-Morphism A B → Wedge-Morphism A C
Wedge-Morphism-∘ M N = record { u = u M ∘ u N ; commute =  sym-assoc ○ (∘-resp-≈ˡ (commute M) ○ commute N) }
  where
  open Wedge-Morphism
  open HomReasoning

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
