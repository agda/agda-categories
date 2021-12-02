{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category.Core using (Category)
open import Categories.Category
open import Categories.Monad

module Categories.Adjoint.Construction.Adjunctions {o ℓ e} {C : Category o ℓ e} (M : Monad C) where

open Category C

open import Categories.Adjoint
open import Categories.Functor
open import Categories.Morphism
open import Categories.Functor.Properties
open import Categories.NaturalTransformation.Core
open import Categories.NaturalTransformation.NaturalIsomorphism
open import Categories.Morphism.Reasoning as MR
open import Categories.Tactic.Category

-- three things:
-- 1. the category of adjunctions splitting a given Monad
-- 2. the proof that EM(M) is the terminal object here
-- 3. the proof that KL(M) is the initial object here

record SplitObj : Set (suc o ⊔ suc ℓ ⊔ suc e) where
  constructor Splitc
  field
    D : Category o ℓ e
    F : Functor C D
    G : Functor D C
    adj : F ⊣ G
    eqM : G ∘F F ≃ Monad.F M

record Split⇒ (X Y : SplitObj) : Set (suc o ⊔ suc ℓ ⊔ suc e) where
  constructor Splitc⇒
  private
    module X = SplitObj X
    module Y = SplitObj Y
  field
    H : Functor X.D Y.D
    HF≃F' : H ∘F X.F ≃ Y.F
    G'H≃G : Y.G ∘F H ≃ X.G

open Split⇒

Split : Monad C → Category _ _ _
Split M = record
  { Obj = SplitObj
  ; _⇒_ = Split⇒
  ; _≈_ = λ U V → Split⇒.H U ≃ Split⇒.H V
  ; id = split-id
  ; _∘_ = comp
  ; assoc = λ { {f = f} {g = g} {h = h} → associator (Split⇒.H f) (Split⇒.H g) (Split⇒.H h) }
  ; sym-assoc = λ { {f = f} {g = g} {h = h} → sym-associator (Split⇒.H f) (Split⇒.H g) (Split⇒.H h) }
  ; identityˡ = unitorˡ
  ; identityʳ = unitorʳ
  ; identity² = unitor²
  ; equiv = record { refl = refl ; sym = sym ; trans = trans }
  ; ∘-resp-≈ = _ⓘₕ_
  }
  where
  open NaturalTransformation
  split-id : {A : SplitObj} → Split⇒ A A
  split-id = record
    { H = Categories.Functor.id
    ; HF≃F' = unitorˡ
    ; G'H≃G = unitorʳ
    }
  comp : {A B X : SplitObj} → Split⇒ B X → Split⇒ A B → Split⇒ A X
  comp {A = A} {B = B} {X = X} (Splitc⇒ Hᵤ HF≃F'ᵤ G'H≃Gᵤ) (Splitc⇒ Hᵥ HF≃F'ᵥ G'H≃Gᵥ) = record
    { H = Hᵤ ∘F Hᵥ
    ; HF≃F' = HF≃F'ᵤ ⓘᵥ (Hᵤ ⓘˡ HF≃F'ᵥ) ⓘᵥ associator (SplitObj.F A) Hᵥ Hᵤ
    ; G'H≃G = G'H≃Gᵥ ⓘᵥ (G'H≃Gᵤ ⓘʳ Hᵥ) ⓘᵥ sym-associator Hᵥ Hᵤ (SplitObj.G X)
    }
