{-# OPTIONS --without-K --safe #-}

open import Level
open import Data.Product using (_,_)

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Monad
open import Categories.Monad.Strong
open import Categories.Category.Monoidal.Symmetric
open import Categories.Functor using (Functor; Endofunctor; _∘F_) renaming (id to idF)

open import Categories.NaturalTransformation using (NaturalTransformation)

module Categories.Monad.Commutative {o ℓ e} {C : Category o ℓ e} {V : Monoidal C} (S : Symmetric V) (SM : StrongMonad S) where

private
  module M = StrongMonad.M SM
  module τ  = StrongMonad.strengthen SM
  module τ' = StrongMonad.strengthen' SM

open NaturalTransformation
open Category C
open Monoidal V

open NaturalTransformation M.η using (η)
open NaturalTransformation M.μ renaming (η to μ)

open M using (F)
open Functor F

record Commutative : Set (o ⊔ ℓ ⊔ e) where
  field
    commutativity : {A B : Obj} → μ (A ⊗₀ B) ∘ F₁ (τ'.η (A , B)) ∘ τ.η (F₀ A , B)
                                ≈ μ (A ⊗₀ B) ∘ F₁ (τ.η (A , B)) ∘ τ'.η (A , F₀ B)

