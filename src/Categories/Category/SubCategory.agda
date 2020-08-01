{-# OPTIONS --without-K --safe #-}
open import Categories.Category

{- Definition of SubCategory of a given Category C.

  Here a SubCategory is defined via
  - an index set I
  - a mapping I → Obj (not necessarily injective)
  - a proof (as a unary relation) that for all a, b : A, all arrows U a ⇒ U b belong to the SubCategory
    (note that this is 'backwards' from SubCategory at https://ncatlab.org/nlab/show/subcategory
     which would be
     (∀ {x y : Obj} (f : x ⇒ y) → R f → ∃ (A × B) (λ (a , b) → U a × U b))
     and that would be awkward to work with.
  - a proof that all objects pointed to by I have identity arrows that belong
  - a proof that composable arrows in the SubCategory are closed under composition

  It is simpler to package up all of that into a single record.
-}
module Categories.Category.SubCategory {o ℓ e} (C : Category o ℓ e) where

open Category C
open Equiv

open import Level
open import Data.Product

private
  variable
    i : Level

record SubCat {ℓ′} (I : Set i) : Set (o ⊔ ℓ ⊔ i ⊔ suc ℓ′) where
  field
    U : I → Obj
    R : {a b : I} → U a ⇒ U b → Set ℓ′
    Rid : {a : I} → R (id {U a})
    _∘R_ : {a b c : I} {f : U b ⇒ U c} {g : U a ⇒ U b} → R f → R g → R (f ∘ g)

SubCategory : {ℓ′ : Level} {I : Set i} → SubCat {ℓ′ = ℓ′} I → Category _ _ _
SubCategory {I = I} sc = let open SubCat sc in record
  { Obj       = I
  ; _⇒_       = λ a b → Σ (U a ⇒ U b) R
  ; _≈_       = λ f g → proj₁ f ≈ proj₁ g
  ; id        = id , Rid
  ; _∘_       = zip _∘_ _∘R_
  ; assoc     = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv     = record -- need to expand this out, else the levels don't work out
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  ; ∘-resp-≈  = ∘-resp-≈
  }

FullSubCategory : ∀ {I : Set i} → (U : I → Obj) → Category _ _ _
FullSubCategory {I = I} U = record
  { Obj       = I
  ; _⇒_       = λ x y → U x ⇒ U y
  ; _≈_       = _≈_
  ; id        = id
  ; _∘_       = _∘_
  ; assoc     = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv     = equiv
  ; ∘-resp-≈  = ∘-resp-≈
  }
