{-# OPTIONS --without-K --safe #-}

-- Define Strong Monad; use the Wikipedia definition
-- https://en.wikipedia.org/wiki/Strong_monad
-- At the nLab, https://ncatlab.org/nlab/show/strong+monad
-- there are two further definitions; the 2-categorical version is too complicated
-- and the Moggi definition is a special case of the one here

module Categories.Monad.Strong where

open import Level using (Level; _⊔_)
open import Data.Product using (_,_)

open import Categories.Category.Core using (Category)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Product using (_⁂_)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Monad using (Monad)
import Categories.Category.Monoidal.Reasoning as MonoidalReasoning


private
  variable
    o ℓ e : Level

-- (left) strength on a monad

record Strength {C : Category o ℓ e} (V : Monoidal C) (M : Monad C) : Set (o ⊔ ℓ ⊔ e) where
  open Category C
  open Monoidal V
  private
    module M = Monad M
  open M using (F)
  open NaturalTransformation M.η using (η)
  open NaturalTransformation M.μ renaming (η to μ)
  open Functor F
  field
    strengthen : NaturalTransformation (⊗ ∘F (idF ⁂ F)) (F ∘F ⊗)

  module strengthen = NaturalTransformation strengthen
  private
    module t = strengthen

  field
    -- strengthening with 1 is irrelevant
    identityˡ : {A : Obj} → F₁ (unitorˡ.from) ∘ t.η (unit , A) ≈ unitorˡ.from
    -- commutes with unit (of monad)
    η-comm : {A B : Obj} → t.η (A , B) ∘ (id ⊗₁ η B) ≈ η (A ⊗₀ B)
    -- strength commutes with multiplication
    μ-η-comm : {A B : Obj} → μ (A ⊗₀ B) ∘ F₁ (t.η (A , B)) ∘ t.η (A , F₀ B)
      ≈ t.η (A , B) ∘ (id ⊗₁ μ B)
    -- consecutive applications of strength commute (i.e. strength is associative)
    strength-assoc :  {A B C : Obj} → F₁ associator.from ∘ t.η (A ⊗₀ B , C)
      ≈ t.η (A , B ⊗₀ C) ∘ (id ⊗₁ t.η (B , C)) ∘ associator.from

  strength-natural-id : ∀ {X Y Z} (f : X ⇒ Y) → t.η (Y , Z) ∘ (f ⊗₁ id) ≈ F₁ (f ⊗₁ id) ∘ t.η (X , Z)
  strength-natural-id f = begin 
    t.η _ ∘ (f ⊗₁ id)    ≈˘⟨ refl⟩∘⟨ refl⟩⊗⟨ identity ⟩ 
    t.η _ ∘ (f ⊗₁ F₁ id) ≈⟨ t.commute (f , id) ⟩ 
    F₁ (f ⊗₁ id) ∘ t.η _ ∎
    where 
      open HomReasoning
      open MonoidalReasoning V using (refl⟩⊗⟨_)

record StrongMonad {C : Category o ℓ e} (V : Monoidal C) : Set (o ⊔ ℓ ⊔ e) where
  field
    M        : Monad C
    strength : Strength V M

  module M = Monad M
  open Strength strength public

-- right strength

record RightStrength {C : Category o ℓ e} (V : Monoidal C) (M : Monad C) : Set (o ⊔ ℓ ⊔ e) where
  open Category C
  open Monoidal V
  private
    module M = Monad M
  open M using (F)
  open NaturalTransformation M.η using (η)
  open NaturalTransformation M.μ renaming (η to μ)
  open Functor F
  field
    strengthen : NaturalTransformation (⊗ ∘F (F ⁂ idF)) (F ∘F ⊗)

  module strengthen = NaturalTransformation strengthen
  private
    module u = strengthen

  field
    -- strengthening with 1 is irrelevant
    identityˡ : {A : Obj} → F₁ (unitorʳ.from) ∘ u.η (A , unit) ≈ unitorʳ.from
    -- commutes with unit (of monad)
    η-comm : {A B : Obj} → u.η (A , B) ∘ (η A ⊗₁ id) ≈ η (A ⊗₀ B)
    -- strength commutes with multiplication
    μ-η-comm : {A B : Obj} → μ (A ⊗₀ B) ∘ F₁ (u.η (A , B)) ∘ u.η (F₀ A , B)
      ≈ u.η (A , B) ∘ (μ A ⊗₁ id)
    -- consecutive applications of strength commute (i.e. strength is associative)
    strength-assoc :  {A B C : Obj} → F₁ associator.to ∘ u.η (A , B ⊗₀ C)
      ≈ u.η (A ⊗₀ B , C) ∘ (u.η (A , B) ⊗₁ id) ∘ associator.to

  strength-natural-id : ∀ {X Y Z} (f : X ⇒ Y) → u.η (Z , Y) ∘ (id ⊗₁ f) ≈ F₁ (id ⊗₁ f) ∘ u.η (Z , X)
  strength-natural-id f = begin 
    u.η _ ∘ (id ⊗₁ f)    ≈˘⟨ refl⟩∘⟨ identity ⟩⊗⟨refl ⟩ 
    u.η _ ∘ (F₁ id ⊗₁ f) ≈⟨ u.commute (id , f) ⟩ 
    F₁ (id ⊗₁ f) ∘ u.η _ ∎
    where 
      open HomReasoning
      open MonoidalReasoning V using (_⟩⊗⟨refl)

record RightStrongMonad {C : Category o ℓ e} (V : Monoidal C) : Set (o ⊔ ℓ ⊔ e) where
  field
    M        : Monad C
    rightStrength : RightStrength V M

  module M = Monad M
  open RightStrength rightStrength public
