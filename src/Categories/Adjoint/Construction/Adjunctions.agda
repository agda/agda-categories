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
open import Categories.NaturalTransformation.NaturalIsomorphism -- using (_≃_; unitorʳ; unitorˡ)
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
  ; id = split-id
  ; _∘_ = comp
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
    ; HF≃F' = unitorˡ
    ; G'H≃G = unitorʳ
    }
  comp : {A B X : SplitObj M} → Split⇒ M B X → Split⇒ M A B → Split⇒ M A X
  comp U V = record 
    { H = H U ∘F H V 
    ; HF≃F' = {!   !}
    ; G'H≃G = {!   !} 
    }
    where
      module U = Split⇒ U 
      module V = Split⇒ V 
      open U 
      open V

  -- comp record { H = H ; HF≃F' = record { F⇒G = F⇒G₁ ; F⇐G = F⇐G₁ ; iso = iso₁ } ; G'H≃G = isoGH } 
  --      record { H = K ; HF≃F' = record { F⇒G = F⇒G ; F⇐G = F⇐G ; iso = iso } ; G'H≃G = isoGK }
  --       = record 
  --        { H = H ∘F K 
  --        ; HF≃F' = ≃.trans {!   !} {!   !}
  --        ; G'H≃G = {!   !} 
  --        }
