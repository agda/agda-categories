{-# OPTIONS --without-K --safe #-}
module Categories.GlobularSet where

-- Globular sets are defined in a Categorical context, but
-- should they be inside the Categories hierarchy?

open import Level
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (refl)

open import Categories.Category
open import Categories.Category.Instance.Globe
open import Categories.Category.Instance.Sets
open import Categories.Functor
open import Categories.Functor.Presheaf

private
  variable
    o ℓ e : Level

GlobularSet : (o : Level) → Set (suc o)
GlobularSet o = Presheaf Globe (Sets o)

-- TODO? make universe polymorphic with polymorphic ⊤
Trivial : GlobularSet zero
Trivial = record
  { F₀ = λ _ → ⊤
  ; F₁ = λ _ x → x
  ; identity = refl
  ; homomorphism = refl
  ; F-resp-≈ = λ _ → refl
  }

GlobularObject : Category o ℓ e → Set _
GlobularObject C = Functor (Category.op Globe) C
