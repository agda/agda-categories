{-# OPTIONS --without-K --safe #-}
module Categories.Category.Instance.StrictGroupoids where

-- The 'strict' category of groupoids.
-- The difference here is that _≈_ is not |NaturalIsomorphism| but |_≡F_|

open import Level
open import Relation.Binary.PropositionalEquality using (refl)

open import Categories.Category using (Category)
open import Categories.Category.Groupoid using (Groupoid)
open import Categories.Category.Instance.Groupoids using (F-resp-⁻¹)
open import Categories.Functor using (Functor; id; _∘F_)
open import Categories.Functor.Equivalence

private
  variable
    o ℓ e : Level

open Groupoid using (category)

Groupoids : ∀ o ℓ e → Category (suc (o ⊔ ℓ ⊔  e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
Groupoids o ℓ e = record
  { Obj       = Groupoid o ℓ e
  ; _⇒_       = λ G H → Functor (category G) (category H)
  ; _≈_       = _≡F_
  ; id        = id
  ; _∘_       = _∘F_
  ; assoc     = λ {_ _ _ _ F G H} → ≡F-assoc     {F = F} {G} {H}
  ; sym-assoc = λ {_ _ _ _ F G H} → ≡F-sym-assoc {F = F} {G} {H}
  ; identityˡ = ≡F-identityˡ
  ; identityʳ = ≡F-identityʳ
  ; identity² = ≡F-identity²
  ; equiv     = ≡F-equiv
  ; ∘-resp-≈  = ∘F-resp-≡F
  }
