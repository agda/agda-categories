{-# OPTIONS --without-K --safe #-}

-- a categorical (i.e. non-skeletal) version of Lawvere Theory,
-- as per https://ncatlab.org/nlab/show/Lawvere+theory

module Categories.Theory.Lawvere where

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_)
open import Level

open import Categories.Category.Cartesian
open import Categories.Category using (Category; _[_,_])
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cartesian)
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
    T : Category o ℓ e
  open Mor T
  field
    cart : Cartesian T
    generic : Category.Obj T
  open Cartesian cart using (power)
  field
    obj-iso-to-generic-power : (x : Category.Obj T) → Σ ℕ (λ n → x ≅ power generic n)

record LT-Hom (T₁ : FiniteProduct o ℓ e) (T₂ : FiniteProduct o′ ℓ′ e′) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private
    module T₁ = FiniteProduct T₁
    module T₂ = FiniteProduct T₂

  field
    F : Functor T₁.T T₂.T
    cartF : CartesianF T₁.cart T₂.cart F

LT-id : {A : FiniteProduct o ℓ e} → LT-Hom A A
LT-id = record { F = idF ; cartF = idF-Cartesian }

LT-∘ : {A : FiniteProduct o ℓ e} {B : FiniteProduct o′ ℓ′ e′} {C : FiniteProduct o″ ℓ″ e″} →
  LT-Hom B C → LT-Hom A B → LT-Hom A C
LT-∘ G H = record { F = F G ∘F F H ; cartF = ∘-Cartesian (cartF G) (cartF H) }
  where open LT-Hom

record T-Algebra (FP : FiniteProduct o ℓ e) : Set (o ⊔ ℓ ⊔ e ⊔ suc (ℓ′ ⊔ e′)) where
  private
    module FP = FiniteProduct FP
  field
    Mod : Functor FP.T (Setoids ℓ′ e′)
    Cart : CartesianF FP.cart Setoids-Cartesian Mod
