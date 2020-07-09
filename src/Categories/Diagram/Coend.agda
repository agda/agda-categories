{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Functor.Bifunctor

module Categories.Diagram.Coend {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′}
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

record Cowedge : Set (levelOfTerm F) where
  field
    E         : Obj
    dinatural : DinaturalTransformation F (const E)

  module dinatural = DinaturalTransformation dinatural

Cowedge-∘ : (W : Cowedge) → Cowedge.E W ⇒ A → Cowedge
Cowedge-∘ {A = A} W f = record
  { E         = A
  ; dinatural = extranaturalˡ (λ X → f ∘ dinatural.α X)
                              (assoc ○ ∘-resp-≈ʳ (extranatural-commˡ dinatural) ○ sym-assoc)
  }
  where open Cowedge W

record Cowedge-Morphism (W₁ W₂ : Cowedge) : Set (levelOfTerm F) where
  private
    module W₁ = Cowedge W₁
    module W₂ = Cowedge W₂
    open DinaturalTransformation
  field
    u : W₁.E ⇒ W₂.E
    commute : ∀ {C} → u ∘ W₁.dinatural.α C ≈ W₂.dinatural.α C

Cowedge-id : ∀ {W} → Cowedge-Morphism W W
Cowedge-id {W} = record { u = D.id ; commute = D.identityˡ }

Cowedge-Morphism-∘ : {A B C : Cowedge} → Cowedge-Morphism B C → Cowedge-Morphism A B → Cowedge-Morphism A C
Cowedge-Morphism-∘ M N = record { u = u M ∘ u N ; commute = assoc ○ {!∘-resp-≈ʳ (commute N) ○ commute M!} }
  where
  open Cowedge-Morphism
  open HomReasoning

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

  η-id : factor cowedge ≈ D.id
  η-id = unique identityˡ

  unique′ :(∀ {A} → f ∘ cowedge.dinatural.α A ≈ g ∘ cowedge.dinatural.α A) → f ≈ g
  unique′ {f = f} {g = g} eq = ⟺ (unique {W = Cowedge-∘ cowedge f} refl) ○ unique (⟺ eq)
