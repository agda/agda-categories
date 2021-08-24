{-# OPTIONS --without-K --safe #-}

-- The 'original' version of Lawvere Theory, based on
-- Nat^op and IOO functors. Contrast with the weak version at
-- https://ncatlab.org/nlab/show/Lawvere+theory
-- Unfortunately, many results on the weak version are not in
-- the literature, so doing that development would be new research.

module Categories.Theory.Lawvere where

open import Data.Nat using (ℕ)
open import Level

open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Cartesian.Bundle using (CartesianCategory)
import Categories.Category.Core as Cat
open import Categories.Category.Instance.Nat using (Nat; Natop-Cartesian)
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-CartesianCategory)
open import Categories.Category.Unbundled using (Category)
open import Categories.Category.Unbundled.Properties using (pack′; unpack′)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Cartesian
open import Categories.Functor.Cartesian.Properties
open import Categories.Functor.IdentityOnObjects

private
  variable
    ℓ e o′ ℓ′ e′ ℓ″ e″ : Level

record LawvereTheory (ℓ e : Level) : Set (suc (ℓ ⊔ e)) where
  private
    𝒩 = Cat.Category.op Nat
  field
    L : Category ℕ ℓ e
  L′ : Cat.Category 0ℓ ℓ e
  L′ = pack′ L
  field
    T : Cartesian L′
  CartT : CartesianCategory 0ℓ ℓ e
  CartT = record { U = L′ ; cartesian = T }
  field
    I : IdentityOnObjects (unpack′ 𝒩) L
    CartF : IsCartesianF Natop-Cartesian CartT (IOO⇒Functor I)

record LT-Hom (T₁ : LawvereTheory ℓ e) (T₂ : LawvereTheory ℓ′ e′) : Set (ℓ ⊔ e ⊔ ℓ′ ⊔ e′) where
  private
    module T₁ = LawvereTheory T₁
    module T₂ = LawvereTheory T₂

  field
    cartF : CartesianF T₁.CartT T₂.CartT

  module cartF = CartesianF cartF using (F)

LT-id : {A : LawvereTheory ℓ e} → LT-Hom A A
LT-id = record { cartF = idF-CartesianF _ }

LT-∘ : {A : LawvereTheory ℓ e} {B : LawvereTheory ℓ′ e′} {C : LawvereTheory ℓ″ e″} →
       LT-Hom B C → LT-Hom A B → LT-Hom A C
LT-∘ G H = record { cartF = ∘-CartesianF (cartF G) (cartF H) }
  where open LT-Hom

-- A 'Model' will be taken to be in Setoids.
record Model (LT : LawvereTheory ℓ e) : Set (ℓ ⊔ e ⊔ suc (ℓ′ ⊔ e′)) where
  private
    module LT = LawvereTheory LT
  field
    cartF : CartesianF LT.CartT (Setoids-CartesianCategory ℓ′ e′)

  module cartF = CartesianF cartF

  mod : Functor LT.L′ (Setoids ℓ′ e′)
  mod = cartF.F

-- But we can have more general models 'in' a cartesian category
record ModelsOf_In_ (LT : LawvereTheory ℓ e) (𝒞 : CartesianCategory o′ ℓ′ e′) : Set (ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private
    module LT = LawvereTheory LT using (L′; CartT)
    module CC = CartesianCategory 𝒞 using (U)
  field
    cartF : CartesianF LT.CartT 𝒞

  mod : Functor LT.L′ CC.U
  mod = CartesianF.F cartF
