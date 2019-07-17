{-# OPTIONS --without-K --safe #-}
module Categories.Enriched where

-- Enriched category over a Monoidal category K

-- interestingly, not a lot of the Monoidal pieces are used.

open import Level
open import Data.Product using (_,_)

open import Categories.Category using (Category; _[_,_])
open import Categories.Functor renaming (id to idF)
open import Categories.Category.Monoidal

private
  variable
    o ℓ e o′ ℓ′ e′ : Level

record Enriched {K : Category o ℓ e} (M : Monoidal K) : Set (suc o ⊔ ℓ ⊔ e) where
  open Category K renaming (Obj to ObjK; id to idK)
  open Monoidal M
  open Functor
  field
    Obj : Set o
    hom : (A B : Obj)   → ObjK
    id  : (A : Obj)     → K [ unit , hom A A ]
    ⊚   : {A B C : Obj} → K [ hom B C ⊗₀ hom A B , hom A C ]

    -- below we give the implicits, just for greater precision. Most could be elided,
    -- as shown in unitʳ
    unitˡ : {A B : Obj} →  ⊚ {A} {B} {B} ∘ id B ⊗₁ idK ≈ unitorˡ.from {hom A B}
    unitʳ : {A B : Obj} → ⊚ ∘ idK ⊗₁ id A ≈ unitorʳ.from {hom A B}
    ⊚-assoc : {A B C D : Obj} →
      ⊚ {A} {C} {D} ∘ (idK ⊗₁ ⊚ {A} {B} {C}) ∘ associator.from ≈ ⊚ ∘ (⊚ ⊗₁ idK)
