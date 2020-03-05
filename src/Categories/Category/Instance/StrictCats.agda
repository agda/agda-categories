{-# OPTIONS --without-K --safe #-}
module Categories.Category.Instance.StrictCats where

-- The (large) 'strict' category of (small) categories.
-- The difference here is that _≈_ is not |NaturalIsomorphism| but |_≈F_|

open import Level
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
  ; assoc     = λ {_ _ _ _ F G H} → ≡F-assoc {F = F} {G} {H}
  ; sym-assoc = λ {_ _ _ _ F G H} → ≡F-sym-assoc {F = F} {G} {H}
  ; identityˡ = ≡F-identityˡ
  ; identityʳ = ≡F-identityʳ
  ; identity² = ≡F-identity²
  ; equiv     = ≡F-equiv
  ; ∘-resp-≈  = ∘F-resp-≡F
  }
