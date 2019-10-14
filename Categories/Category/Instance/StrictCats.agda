{-# OPTIONS --without-K --safe #-}
module Categories.Category.Instance.StrictCats where

-- The (large) 'strict' category of (small) categories.
-- The difference here is that _≈_ is not |NaturalIsomorphism| but |_≈F_|

open import Level
open import Data.Product using (Σ) renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Categories.Category using (Category)
open import Categories.Functor using (Functor; id; _∘F_)
open import Categories.Functor.Equivalence

private
  variable
    o ℓ e : Level

Cats : ∀ o ℓ e → Category (suc (o ⊔ ℓ ⊔  e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
Cats o ℓ e = record
  { Obj       = Category o ℓ e
  ; _⇒_       = Functor
  ; _≈_       = _≡F_
  ; id        = id
  ; _∘_       = _∘F_
  ; assoc     = λ {_ _ _} {D} → (λ _ → refl) ,, λ f → Category.Equiv.refl D
  ; sym-assoc = λ {_ _ _} {D} → (λ _ → refl) ,, λ f → Category.Equiv.refl D
  ; identityˡ = λ {_} {B} → (λ _ → refl) ,, λ _ → Category.Equiv.refl B
  ; identityʳ = λ {_} {B} → (λ _ → refl) ,, λ _ → Category.Equiv.refl B
  ; equiv     = ≡F-equiv
  ; ∘-resp-≈  = λ {A} {B} {C} {f} {h} {g} {i} f≡h g≡i →  ∘F-perserves-≡F {h = f} {h} {g} {i} f≡h g≡i
  }
