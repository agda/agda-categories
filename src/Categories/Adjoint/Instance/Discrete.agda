{-# OPTIONS --without-K --safe #-}

module Categories.Adjoint.Instance.Discrete where

-- The Discrete/Forgetful/Codiscrete adjoint triple between Sets and
-- StrictCats.
--
-- We need 'strict' functor equality to prove functionality of the
-- forgetful functor (we cannot extract a propositional equality proof
-- on objects from a natural isomorphism).

open import Level using (Lift; lift)
open import Data.Unit using (⊤; tt)
import Function as Fun
open import Relation.Binary.PropositionalEquality -- lots of stuff from here

open import Categories.Adjoint
open import Categories.Category using (Category)
open import Categories.Category.Instance.StrictCats
open import Categories.Category.Instance.Sets
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Equivalence
import Categories.Category.Discrete as D
open import Categories.Morphism.HeterogeneousIdentity
open import Categories.Morphism.HeterogeneousIdentity.Properties
open import Categories.NaturalTransformation as NT using (NaturalTransformation; ntHelper)

-- The forgetful functor from StrictCats to Sets.

Forgetful : ∀ {o ℓ e} → Functor (Cats o ℓ e) (Sets o)
Forgetful {o} {ℓ} {e} = record
  { F₀ = Obj
  ; F₁ = F₀
  ; identity     = refl
  ; homomorphism = refl
  ; F-resp-≈     = λ F≡G {X} → eq₀ F≡G X
  }
  where
    open Category
    open Functor
    open _≡F_

-- The discrete functor (strict version)

Discrete : ∀ {o} → Functor (Sets o) (Cats o o o)
Discrete {o} = record
  { F₀ = D.Discrete
  ; F₁ = λ f → record
    { F₀ = f
    ; F₁ = cong f
    ; identity     = refl
    ; homomorphism = λ {_ _ _ p q} → cong-trans f p q
    ; F-resp-≈     = cong (cong f)
    }
  ; identity = record
    { eq₀ = λ _ → refl
    ; eq₁ = λ p → let open ≡-Reasoning in begin
        trans (cong Fun.id p) refl   ≡⟨ trans-reflʳ _ ⟩
               cong Fun.id p         ≡⟨ cong-id p ⟩
                           p         ∎
    }
  ; homomorphism = λ {_ _ _ f g} → record
    { eq₀ = λ _ → refl
    ; eq₁ = λ p → let open ≡-Reasoning in begin
        trans (cong (g Fun.∘ f) p) refl ≡⟨ trans-reflʳ _ ⟩
               cong (g Fun.∘ f) p       ≡⟨ cong-∘ p ⟩
               cong g (cong f p)        ∎
    }
  ; F-resp-≈ = λ {_ _ f g} f≗g → record
    { eq₀ = λ x → f≗g {x}
    ; eq₁ = λ {x} {y} p → naturality (λ x → subst (f x ≡_) (f≗g {x}) refl)
    }
  }
  where

    -- A helper lemma.
    -- FIXME: Should probably go into Relation.Binary.PropositionalEquality

    cong-trans : ∀ {A B : Set o} (f : A → B) {x y z} (p : x ≡ y) (q : y ≡ z) →
                 cong f (trans p q) ≡ trans (cong f p) (cong f q)
    cong-trans f refl refl = refl

-- The codiscrete functor (strict version)

Codiscrete : ∀ {o} ℓ e → Functor (Sets o) (Cats o ℓ e)
Codiscrete {o} ℓ e = record
  { F₀ = λ A → record
    { Obj = A
    ; _⇒_ = λ _ _ → Lift ℓ ⊤
    ; _≈_ = λ _ _ → Lift e ⊤
    ; id  = lift tt
    ; _∘_ = λ _ _ → lift tt
    ; assoc     = lift tt
    ; identityˡ = lift tt
    ; identityʳ = lift tt
    ; equiv     = record
      { refl  = lift tt
      ; sym   = λ _ → lift tt
      ; trans = λ _ _ → lift tt
      }
    ; ∘-resp-≈ = λ _ _ → lift tt
    }
  ; F₁ = λ f → record
    { F₀ = f
    ; F₁ = λ _ → lift tt
    ; identity     = lift tt
    ; homomorphism = lift tt
    ; F-resp-≈     = λ _ → lift tt
    }
  ; identity     = Equiv.refl
  ; homomorphism = Equiv.refl
  ; F-resp-≈     = λ {_ _ f g} f≗g → record
    { eq₀ = λ x → f≗g {x}
    ; eq₁ = λ _ → lift tt
    }
  }
  where open Category (Cats o ℓ e)


-- Discrete is left-adjoint to the forgetful functor from StrictCats to Sets

DiscreteLeftAdj : ∀ {o} → Discrete ⊣ Forgetful {o} {o} {o}
DiscreteLeftAdj {o} = record
  { unit   = unit
  ; counit = counit
  ; zig    = zig
  ; zag    = refl
  }
  where
    module U = Functor Forgetful
    module Δ = Functor Discrete

    unit : NaturalTransformation idF (Forgetful ∘F Discrete)
    unit = NT.id

    counitFun : ∀ C → Functor (Δ.F₀ (U.F₀ C)) C
    counitFun C = let open Category C in record
      { F₀ = Fun.id
      ; F₁ = hid C
      ; identity     = Equiv.refl
      ; homomorphism = λ {_ _ _ p q} → Equiv.sym (hid-trans C q p)
      ; F-resp-≈     = hid-cong C
      }

    counitComm : ∀ {C D} → (F : Functor C D) →
                 counitFun D ∘F (Δ.F₁ (U.F₁ F)) ≡F F ∘F counitFun C
    counitComm {C} {D} F =
      let open Functor F
          open Category D
          open HomReasoning
      in record
      { eq₀ = λ _ → refl
      ; eq₁ = λ {X Y} p → begin
        id ∘ hid D (cong F₀ p)   ≈⟨ identityˡ ⟩
             hid D (cong F₀ p)   ≈˘⟨ F-hid F p ⟩
        F₁ (hid C p)             ≈˘⟨ identityʳ ⟩
        F₁ (hid C p) ∘ id        ∎
      }

    counit : NaturalTransformation (Discrete ∘F Forgetful) idF
    counit = ntHelper record { η = counitFun ; commute = counitComm }

    zig : {A : Set o} → counitFun (Δ.F₀ A) ∘F (Δ.F₁ Fun.id) ≡F idF
    zig {A} = record { eq₀ = λ _ → refl ; eq₁ = λ{ refl → refl } }

-- Codiscrete is right-adjoint to the forgetful functor from StrictCats to Sets

CodiscreteRightAdj : ∀ {o ℓ e} → Forgetful ⊣ Codiscrete {o} ℓ e
CodiscreteRightAdj {o} {ℓ} {e} = record
  { unit   = unit
  ; counit = counit
  ; zig    = refl
  ; zag    = zag
  }
  where
    module U = Functor Forgetful
    module ∇ = Functor (Codiscrete ℓ e)

    unitFun : ∀ C → Functor C (∇.F₀ (U.F₀ C))
    unitFun C = let open Category C in record
      { F₀ = Fun.id
      ; F₁ = λ _ → lift tt
      ; identity     = lift tt
      ; homomorphism = lift tt
      ; F-resp-≈     = λ _ → lift tt
      }

    unitComm : ∀ {C D} → (F : Functor C D) →
               unitFun D ∘F F ≡F (∇.F₁ (U.F₁ F)) ∘F unitFun C
    unitComm {C} {D} F = record { eq₀ = λ _ → refl ; eq₁ = λ _ → lift tt }

    unit : NaturalTransformation idF (Codiscrete ℓ e ∘F Forgetful)
    unit = ntHelper record { η = unitFun ; commute = unitComm }

    counit : NaturalTransformation (Forgetful ∘F Codiscrete ℓ e) idF
    counit = NT.id

    zag : {B : Set o} → ∇.F₁ Fun.id ∘F unitFun (∇.F₀ B) ≡F idF
    zag {B} = record { eq₀ = λ _ → refl ; eq₁ = λ _ → lift tt }
