{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Morphisms  {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level
open import Function using (flip)
open import Relation.Binary hiding (_⇒_)

open import Categories.Square.Core 𝒞

open Category 𝒞

private
  variable
    A B C : Obj

Mono : ∀ (f : A ⇒ B) → Set _
Mono {A = A} f = ∀ {C} → (g₁ g₂ : C ⇒ A) → f ∘ g₁ ≈ f ∘ g₂ → g₁ ≈ g₂

Epi : ∀ (f : A ⇒ B) → Set _
Epi {B = B} f = ∀ {C} → (g₁ g₂ : B ⇒ C) → g₁ ∘ f ≈ g₂ ∘ f → g₁ ≈ g₂

record Iso (from : A ⇒ B) (to : B ⇒ A) : Set (o ⊔ ℓ ⊔ e) where
  field
    isoˡ : to ∘ from ≈ id
    isoʳ : from ∘ to ≈ id

infix 4 _≅_
record _≅_ (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    from : A ⇒ B
    to   : B ⇒ A
    iso  : Iso from to

  open Iso iso public

≅-refl : Reflexive _≅_
≅-refl = record
  { from = id
  ; to   = id
  ; iso  = record
    { isoˡ = identityˡ
    ; isoʳ = identityʳ
    }
  }

≅-sym : Symmetric _≅_
≅-sym A≅B = record
  { from = to
  ; to   = from
  ; iso  = record
    { isoˡ = isoʳ
    ; isoʳ = isoˡ
    }
  }
  where open _≅_ A≅B

≅-trans : Transitive _≅_
≅-trans A≅B B≅C = record
  { from = from B≅C ∘ from A≅B
  ; to   = to A≅B ∘ to B≅C
  ; iso  = record
    { isoˡ = begin
      (to A≅B ∘ to B≅C) ∘ from B≅C ∘ from A≅B ≈⟨ cancelInner (isoˡ B≅C) ⟩
      to A≅B ∘ from A≅B                       ≈⟨ isoʳ (≅-sym A≅B) ⟩
      id                                      ∎
    ; isoʳ = begin
      (from B≅C ∘ from A≅B) ∘ to A≅B ∘ to B≅C ≈⟨ cancelInner (isoʳ A≅B) ⟩
      from B≅C ∘ to B≅C                       ≈⟨ isoˡ (≅-sym B≅C) ⟩
      id                                      ∎
    }
  }
  where open _≅_
        open HomReasoning
        open Equiv

≅-isEquivalence : IsEquivalence _≅_
≅-isEquivalence = record
  { refl  = ≅-refl
  ; sym   = ≅-sym
  ; trans = ≅-trans
  }

≅-setoid : Setoid _ _
≅-setoid = record
  { Carrier       = Obj
  ; _≈_           = _≅_
  ; isEquivalence = ≅-isEquivalence
  }

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
  ; id        = ≅-refl
  ; _∘_       = flip ≅-trans
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

