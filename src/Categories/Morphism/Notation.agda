{-# OPTIONS --without-K --safe #-}

{-
  Useful notation for Epimorphisms, Mononmorphisms, and isomorphisms
-}
module Categories.Morphism.Notation where

open import Level

open import Categories.Category.Core
open import Categories.Morphism

private
  variable
    o ℓ e : Level

_[_↣_] : (𝒞 : Category o ℓ e) → (A B : Category.Obj 𝒞) → Set (o ⊔ ℓ ⊔ e)
𝒞 [ A ↣ B ] = _↣_ 𝒞 A B

_[_↠_] : (𝒞 : Category o ℓ e) → (A B : Category.Obj 𝒞) → Set (o ⊔ ℓ ⊔ e)
𝒞 [ A ↠ B ] = _↠_ 𝒞 A B

_[_≅_] : (𝒞 : Category o ℓ e) → (A B : Category.Obj 𝒞) → Set (ℓ ⊔ e)
𝒞 [ A ≅ B ] = _≅_ 𝒞 A B
