{-# OPTIONS --without-K --safe #-}

-- a categorical (i.e. non-skeletal) version of Lawvere Theory,
-- as per https://ncatlab.org/nlab/show/Lawvere+theory

module Categories.Theory.Lawvere where

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_)
open import Level

open import Categories.Category.Cartesian.Structure
open import Categories.Category using (Category; _[_,_])
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-CartesianCategory)
open import Categories.Category.Product
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Cartesian
open import Categories.Functor.Cartesian.Properties
import Categories.Morphism as Mor
open import Categories.NaturalTransformation using (NaturalTransformation)

private
  variable
    o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ : Level

record FiniteProduct (o ℓ e : Level) : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
    T : CartesianCategory o ℓ e

  module T = CartesianCategory T
  open Mor T.U

  field
    generic : T.Obj

  field
    obj-iso-to-generic-power : ∀ x → Σ ℕ (λ n → x ≅ T.power generic n)

record LT-Hom (T₁ : FiniteProduct o ℓ e) (T₂ : FiniteProduct o′ ℓ′ e′) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private
    module T₁ = FiniteProduct T₁
    module T₂ = FiniteProduct T₂

  field
    cartF : CartesianF T₁.T T₂.T

  module cartF = CartesianF cartF

LT-id : {A : FiniteProduct o ℓ e} → LT-Hom A A
LT-id = record { cartF = idF-CartesianF _ }

LT-∘ : {A : FiniteProduct o ℓ e} {B : FiniteProduct o′ ℓ′ e′} {C : FiniteProduct o″ ℓ″ e″} →
       LT-Hom B C → LT-Hom A B → LT-Hom A C
LT-∘ G H = record { cartF = ∘-CartesianF (cartF G) (cartF H) }
  where open LT-Hom


record T-Algebra (FP : FiniteProduct o ℓ e) : Set (o ⊔ ℓ ⊔ e ⊔ suc (ℓ′ ⊔ e′)) where
  private
    module FP = FiniteProduct FP
  field
    cartF : CartesianF FP.T (Setoids-CartesianCategory ℓ′ e′)

  module cartF = CartesianF cartF

  mod : Functor FP.T.U (Setoids ℓ′ e′)
  mod = cartF.F
