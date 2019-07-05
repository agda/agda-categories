{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Morphism.IsoEquiv {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level
open import Function using (flip)
open import Relation.Binary hiding (_⇒_)

open import Categories.Morphism 𝒞

open Category 𝒞

private
  variable
    A B C : Obj

infix 4 _≃_
record _≃_ (i j : A ≅ B) : Set (o ⊔ ℓ ⊔ e) where
  open _≅_
  field
    from-≈ : from i ≈ from j
    to-≈   : to i ≈ to j

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
        open Equiv

≃-setoid : ∀ {A B : Obj} → Setoid _ _
≃-setoid {A} {B} = record
  { Carrier       = A ≅ B
  ; _≈_           = _≃_
  ; isEquivalence = ≃-isEquivalence
  }

Isos : Category _ _ _
Isos = record
  { Obj       = Obj
  ; _⇒_       = _≅_
  ; _≈_       = _≃_
  ; id        = ≅.refl
  ; _∘_       = flip ≅.trans
  ; assoc     = record { from-≈ = assoc ; to-≈ = sym assoc }
  ; identityˡ = record { from-≈ = identityˡ ; to-≈ = identityʳ }
  ; identityʳ = record { from-≈ = identityʳ ; to-≈ = identityˡ }
  ; equiv     = ≃-isEquivalence
  ; ∘-resp-≈  = λ where
    record { from-≈ = from-≈ ; to-≈ = to-≈ } record { from-≈ = from-≈′ ; to-≈ = to-≈′ } → record
      { from-≈ = ∘-resp-≈ from-≈ from-≈′
      ; to-≈   = ∘-resp-≈ to-≈′ to-≈
      }
  }
  where open Equiv
