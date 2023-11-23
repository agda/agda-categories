{-# OPTIONS --without-K --safe #-}

-- Define Strong Monad; use the Wikipedia definition
-- https://en.wikipedia.org/wiki/Strong_monad
-- At the nLab, https://ncatlab.org/nlab/show/strong+monad
-- there are two further definitions; the 2-categorical version is too complicated
-- and the Moggi definition is a special case of the one here

module Categories.Monad.Strong  where

open import Level
open import Data.Product using (_,_)

open import Categories.Category
open import Categories.Functor renaming (id to idF)
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Symmetric
open import Categories.Category.Monoidal.Braided

open import Categories.Category.Product
open import Categories.Category.Product.Properties
open import Categories.NaturalTransformation hiding (id)
open import Categories.NaturalTransformation.NaturalIsomorphism renaming (associator to ∘-assoc)
open import Categories.Monad

private
  variable
    o ℓ e : Level

record Strength {C : Category o ℓ e} {V : Monoidal C} (S : Symmetric V) (M : Monad C) : Set (o ⊔ ℓ ⊔ e) where
  open Category C
  open Monoidal V

  private
    module M = Monad M
    
  open M using (F)
  open NaturalTransformation M.η using (η)
  open NaturalTransformation M.μ renaming (η to μ)
  open Functor F
  open Symmetric S using (braided)
  open NaturalIsomorphism using (F⇐G; F⇒G)

  private
    γ   = Braided.braiding.F⇒G braided
    γ⁻¹ = Braided.braiding.F⇐G braided

  field
    strengthen : NaturalTransformation (⊗ ∘F (idF ⁂ F)) (F ∘F ⊗)

   -- dual strength
  strengthen' : NaturalTransformation (⊗ ∘F (F ⁂ idF)) (F ∘F ⊗)
  strengthen' = (F ∘ˡ γ⁻¹) ∘ᵥ F⇒G (∘-assoc Swap ⊗ F) ∘ᵥ (strengthen ∘ʳ Swap) ∘ᵥ
                F⇐G (∘-assoc Swap (idF ⁂ F) ⊗) ∘ᵥ
                  (⊗ ∘ˡ F⇒G (SwapFG≅FGSwap C C F idF)) ∘ᵥ
                F⇒G (∘-assoc (F ⁂ idF) Swap ⊗) ∘ᵥ
                (γ ∘ʳ (F ⁂ idF))

  module strengthen  = NaturalTransformation strengthen
  module strengthen' = NaturalTransformation strengthen'

  private
    module t = strengthen

  field
    -- strengthening with 1 is irrelevant
    identityˡ : {A : Obj} → F₁ (unitorˡ.from) ∘ t.η (unit , A) ≈ unitorˡ.from
    -- commutes with unit (of monad)
    η-comm : {A B : Obj} → t.η (A , B) ∘ (id ⊗₁ η B) ≈  η (A ⊗₀ B)
    -- strength commutes with multiplication
    μ-η-comm : {A B : Obj} → μ (A ⊗₀ B) ∘ F₁ (t.η (A , B)) ∘ t.η (A , F₀ B)
      ≈ t.η (A , B) ∘ id ⊗₁ μ B
    -- consecutive applications of strength commute (i.e. strength is associative)
    strength-assoc :  {A B C : Obj} → F₁ associator.from ∘ t.η (A ⊗₀ B , C)
      ≈ t.η (A , B ⊗₀ C) ∘ id ⊗₁ t.η (B , C) ∘ associator.from   

record StrongMonad {C : Category o ℓ e} {V : Monoidal C} (S : Symmetric V) : Set (o ⊔ ℓ ⊔ e) where
  field
    M        : Monad C
    strength : Strength S M

  module M = Monad M
  open Strength strength public
