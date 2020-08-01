{-# OPTIONS --without-K --safe #-}
open import Categories.Category.Core

-- slice category (https://ncatlab.org/nlab/show/over+category)
-- TODO: Forgetful Functor from Slice to 𝒞
module Categories.Category.Slice {o ℓ e} (𝒞 : Category o ℓ e) where

open Category 𝒞
open HomReasoning
open Equiv

open import Level
open import Function.Base using (_$_)
open import Relation.Binary.Core using (Rel)

open import Categories.Morphism.Reasoning 𝒞

record SliceObj (X : Obj) : Set (o ⊔ ℓ) where
  constructor sliceobj
  field
    {Y} : Obj
    arr : Y ⇒ X

private
  variable
    A : Obj
    X Y Z : SliceObj A

record Slice⇒ {A : Obj} (X Y : SliceObj A) : Set (ℓ ⊔ e) where
  constructor slicearr
  private
    module X = SliceObj X
    module Y = SliceObj Y
  field
    {h} : X.Y ⇒ Y.Y
    △   : Y.arr ∘ h ≈ X.arr

Slice : Obj → Category _ _ _
Slice A       = record
  { Obj       = SliceObj A
  ; _⇒_       = Slice⇒
  ; _≈_       = λ where
    (slicearr {f} _) (slicearr {g} _) → f ≈ g
  ; id        = slicearr identityʳ
  ; _∘_       = _∘′_
  ; assoc     = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv     = record -- must be expanded to get levels to work out
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  ; ∘-resp-≈  = ∘-resp-≈
  }
  where _∘′_ : Slice⇒ Y Z → Slice⇒ X Y → Slice⇒ X Z
        _∘′_ {Y = sliceobj y} {Z = sliceobj z} {X = sliceobj x} (slicearr {g} △) (slicearr {f} △′) = slicearr $ begin
          z ∘ g ∘ f ≈⟨ pullˡ △ ⟩
          y ∘ f     ≈⟨ △′ ⟩
          x         ∎
