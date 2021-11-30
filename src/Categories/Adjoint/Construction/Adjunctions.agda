{-# OPTIONS --without-K --safe #-}

open import Level

open import Categories.Category.Core using (Category)
open import Categories.Category
open import Categories.Monad

module Categories.Adjoint.Construction.Adjunctions where

open import Categories.Category.Construction.Kleisli
open import Categories.Category.Construction.EilenbergMoore
open import Categories.Adjoint
open import Categories.Functor
open import Categories.Morphism
open import Categories.Functor.Properties
open import Categories.NaturalTransformation.Core
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_)
open import Categories.Morphism.Reasoning as MR
open import Categories.Tactic.Category

-- three things:
-- 1. the category of adjunctions splitting a given Monad
-- 2. the proof that EM(M) is the terminal object here
-- 3. the proof that KL(M) is the terminal object here

private
  variable
    o ℓ e : Level

record SplitObj {C : Category o ℓ e} (M : Monad C) : Set (suc o ⊔ suc ℓ ⊔ suc e) where
  field
    D : Category o ℓ e
    F : Functor C D
    G : Functor D C
    adj : F ⊣ G
    eqM : G ∘F F ≃ Monad.F M

record Split⇒ {C : Category o ℓ e} (M : Monad C) (X Y : SplitObj M) : Set (suc o ⊔ suc ℓ ⊔ suc e) where
  private
    module X = SplitObj X
    module Y = SplitObj Y
  field
    H : Functor X.D Y.D
    HF≃F' : H ∘F X.F ≃ Y.F
    G'H≃G : Y.G ∘F H ≃ X.G

Split : {𝒞 : Category o ℓ e} → Monad 𝒞 → Category _ _ _
Split {𝒞 = 𝒞} M = record
  { Obj = SplitObj M
  ; _⇒_ = Split⇒ M
  ; _≈_ = λ H K → {!   !}
  ; id = {!   !}
  ; _∘_ = {!   !}
  ; assoc = {!   !}
  ; sym-assoc = {!   !}
  ; identityˡ = {!   !}
  ; identityʳ = {!   !}
  ; identity² = {!   !}
  ; equiv = {!   !}
  ; ∘-resp-≈ = {!   !}
  }
  where
  open NaturalTransformation
  split-id : {A : SplitObj M} → Split⇒ M A A
  split-id = record
    { H = Categories.Functor.id
    ; HF≃F' = record { F⇒G = {!   !} ; F⇐G = {!   !} ; iso = {!   !} }
    ; G'H≃G = record { F⇒G = {!   !} ; F⇐G = {!   !} ; iso = {!   !} }
    }
