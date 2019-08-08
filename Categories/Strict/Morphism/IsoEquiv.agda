{-# OPTIONS --without-K --safe #-}

open import Categories.Strict.Category

module Categories.Strict.Morphism.IsoEquiv {o ℓ} (𝒞 : Category o ℓ) where

open import Level
open import Function using (flip)
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong₂)

open import Categories.Strict.Morphism 𝒞

open Category 𝒞

private
  variable
    A B C : Obj

infix 4 _≃_
record _≃_ (i j : A ≅ B) : Set (o ⊔ ℓ) where
  open _≅_
  field
    from-≈ : from i ≡ from j
    to-≈   : to i ≡ to j

≃-isEquivalence : IsEquivalence (_≃_ {A} {B})
≃-isEquivalence = record
  { refl  = record
    { from-≈ = refl
    ; to-≈   = refl
    }
  ; sym   = λ where
    record { from-≈ = from-≈ ; to-≈ = to-≈ } → record
      { from-≈ = sym from-≈
      ; to-≈   = sym to-≈
      }
  ; trans = λ where
    record { from-≈ = from-≈ ; to-≈ = to-≈ } record { from-≈ = from-≈′ ; to-≈ = to-≈′ } → record
      { from-≈ = trans from-≈ from-≈′
      ; to-≈   = trans to-≈ to-≈′
      }
  }
  where open _≅_

≃-setoid : ∀ {A B : Obj} → Setoid _ _
≃-setoid {A} {B} = record
  { Carrier       = A ≅ B
  ; _≈_           = _≃_
  ; isEquivalence = ≃-isEquivalence
  }

{- Category of Isos isn't Strict?
Isos : Category _ _
Isos = record
  { Obj       = Obj
  ; _⇒_       = _≅_
  ; id        = ≅.refl
  ; _∘_       = flip ≅.trans
  ; assoc     = {!!} -- record { from-≈ = assoc ; to-≈ = sym assoc }
  ; identityˡ = {!!} -- record { from-≈ = identityˡ ; to-≈ = identityʳ }
  ; identityʳ = {!!} -- record { from-≈ = identityʳ ; to-≈ = identityˡ }
  }
-}
