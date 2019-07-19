{-# OPTIONS --without-K --safe #-}
module Categories.Category.Enriched where

-- Enriched category over a Monoidal category K

-- interestingly, not a lot of the Monoidal pieces are used.

open import Level
open import Data.Product using (_,_)

open import Categories.Category using (Category; _[_,_])
open import Categories.Functor renaming (id to idF)
open import Categories.Category.Monoidal

private
  variable
    o ℓ e : Level

record Enriched {K : Category o ℓ e} (M : Monoidal K) (v : Level) : Set (o ⊔ ℓ ⊔ e ⊔ suc v) where
  open Category K renaming (Obj to ObjK; id to idK)
  open Commutation
  open Monoidal M
  open Functor
  field
    Obj : Set v
    hom : (A B : Obj)   → ObjK
    id  : (A : Obj)     → K [ unit , hom A A ]
    ⊚   : {A B C : Obj} → K [ hom B C ⊗₀ hom A B , hom A C ]

    ⊚-assoc : {A B C D : Obj} → [ (hom C D ⊗₀ hom B C) ⊗₀ hom A B ⇒ hom A D ]⟨
        associator.from    ⇒⟨ hom C D ⊗₀ (hom B C ⊗₀ hom A B) ⟩
        idK ⊗₁ ⊚          ⇒⟨ hom C D ⊗₀ hom A C ⟩
        ⊚
      ≈ ⊚ ⊗₁ idK          ⇒⟨ hom B D ⊗₀ hom A B ⟩
        ⊚ ⟩
    unitˡ : {A B : Obj} → [ unit ⊗₀ hom A B ⇒ hom A B ]⟨
        id B ⊗₁ idK   ⇒⟨ hom B B ⊗₀ hom A B ⟩
        ⊚
      ≈ unitorˡ.from ⟩
    unitʳ : {A B : Obj} → [ hom A B ⊗₀ unit ⇒ hom A B ]⟨
        idK ⊗₁ id A    ⇒⟨ hom A B ⊗₀ hom A A ⟩
        ⊚
      ≈ unitorʳ.from ⟩
