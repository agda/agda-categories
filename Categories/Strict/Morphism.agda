{-# OPTIONS --without-K --safe #-}

{-
  Properties and definitions regarding Morphisms of a category:
  - Monomorphism
  - Epimorphism
  - Isomorphism
  - (object) equivalence ('spelled' _≅_ ). Exported as the module ≅
-}
open import Categories.Strict.Category

module Categories.Strict.Morphism {o ℓ} (𝒞 : Category o ℓ) where

open import Level
open import Function using (flip)
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality

open import Categories.Strict.Morphism.Reasoning.Core 𝒞

open Category 𝒞

private
  variable
    A B C : Obj

Mono : ∀ (f : A ⇒ B) → Set _
Mono {A = A} f = ∀ {C} → (g₁ g₂ : C ⇒ A) → f ∘ g₁ ≡ f ∘ g₂ → g₁ ≡ g₂

Epi : ∀ (f : A ⇒ B) → Set _
Epi {B = B} f = ∀ {C} → (g₁ g₂ : B ⇒ C) → g₁ ∘ f ≡ g₂ ∘ f → g₁ ≡ g₂

record Iso (from : A ⇒ B) (to : B ⇒ A) : Set (o ⊔ ℓ) where
  field
    isoˡ : to ∘ from ≡ id
    isoʳ : from ∘ to ≡ id

infix 4 _≅_
record _≅_ (A B : Obj) : Set (o ⊔ ℓ) where
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

≅-isEquivalence : IsEquivalence _≅_
≅-isEquivalence = record
  { refl  = ≅-refl
  ; sym   = ≅-sym
  ; trans = ≅-trans
  }

-- But make accessing it easy:
module ≅ = IsEquivalence ≅-isEquivalence

-------------
-- Q: does this belong here?
