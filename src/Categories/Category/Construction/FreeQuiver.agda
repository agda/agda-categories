{-# OPTIONS --without-K --safe #-}

open import Level
open import Data.Quiver using (Quiver)

-- The Category of (free) paths over a Quiver
module Categories.Category.Construction.FreeQuiver {o ℓ e}
  (G : Quiver o ℓ e) where

open import Function.Base using (_$_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties hiding (trans)
open import Data.Quiver.Paths

open import Categories.Category.Core using (Category)

open Quiver G
private module P = Paths G
open P

PathCategory : Category o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)
PathCategory = record
  { Obj       = Obj
  ; _⇒_       = Star _⇒_
  ; _≈_       = _≈*_
  ; id        = ε
  ; _∘_       = _▻▻_
  ; assoc     = λ {_ _ _ _} {f g h} → sym $ ≡⇒≈* $ ◅◅-assoc f g h
  ; sym-assoc = λ {_ _ _ _} {f g h} → ≡⇒≈* $ ◅◅-assoc f g h
  ; identityˡ = λ {_ _ f} → ◅◅-identityʳ f
  ; identityʳ = refl
  ; identity² = refl
  ; equiv     = isEquivalence
  ; ∘-resp-≈  = resp
  }
  where
  resp : ∀ {A B C} {f h : Star _⇒_ B C} {g i : Star _⇒_ A B} →
           f ≈* h → g ≈* i → (f ▻▻ g) ≈* (h ▻▻ i)
  resp eq ε = eq
  resp eq (eq₁ ◅ eq₂) = eq₁ ◅ (resp eq eq₂)

open P public renaming (_≈*_ to [_]_≈*_)
