{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Morphisms  {o ℓ e} (C : Category o ℓ e) where

open import Level
open import Function using (flip)
open import Relation.Binary hiding (_⇒_)

open import Categories.Square.Core C

open Category C

private
  variable
    A B : Obj

Mono : ∀ (f : A ⇒ B) → Set _
Mono {A} f = ∀ {C} → (g₁ g₂ : C ⇒ A) → f ∘ g₁ ≈ f ∘ g₂ → g₁ ≈ g₂

Epi : ∀ (f : A ⇒ B) → Set _
Epi {B = B} f = ∀ {C} → (g₁ g₂ : B ⇒ C) → g₁ ∘ f ≈ g₂ ∘ f → g₁ ≈ g₂

record Iso (f : A ⇒ B) (g : B ⇒ A) : Set (o ⊔ ℓ ⊔ e) where
  field
    isoˡ : g ∘ f ≈ id
    isoʳ : f ∘ g ≈ id

infix 4 _≅_
record _≅_ (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    f   : A ⇒ B
    g   : B ⇒ A
    iso : Iso f g

  open Iso iso public

≅-refl : Reflexive _≅_
≅-refl = record
  { f   = id
  ; g   = id
  ; iso = record
    { isoˡ = identityˡ
    ; isoʳ = identityʳ
    }
  }

≅-sym : Symmetric _≅_
≅-sym A≅B = record
  { f   = g
  ; g   = f
  ; iso = record
    { isoˡ = isoʳ
    ; isoʳ = isoˡ
    }
  }
  where open _≅_ A≅B

≅-trans : Transitive _≅_
≅-trans A≅B B≅C = record
  { f   = f B≅C ∘ f A≅B
  ; g   = g A≅B ∘ g B≅C
  ; iso = record
    { isoˡ = begin
      (g A≅B ∘ g B≅C) ∘ f B≅C ∘ f A≅B   ≈⟨ cancelInner (isoˡ B≅C) ⟩
      g A≅B ∘ f A≅B                     ≈⟨ isoʳ (≅-sym A≅B) ⟩
      id                                ∎
    ; isoʳ = begin
      (f B≅C ∘ f A≅B) ∘ g A≅B ∘ g B≅C   ≈⟨ cancelInner (isoʳ A≅B) ⟩
      f B≅C ∘ g B≅C                     ≈⟨ isoˡ (≅-sym B≅C) ⟩
      id                                ∎
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
    f-≈ : f i ≈ f j
    g-≈ : g i ≈ g j

≃-isEquivalence : IsEquivalence (_≃_ {A} {B})
≃-isEquivalence = record
  { refl  = record
    { f-≈ = refl
    ; g-≈ = refl
    }
  ; sym   = λ where
    record { f-≈ = f-≈ ; g-≈ = g-≈ } → record
      { f-≈ = sym f-≈
      ; g-≈ = sym g-≈
      }
  ; trans = λ where
    record { f-≈ = f-≈ ; g-≈ = g-≈ } record { f-≈ = f-≈′ ; g-≈ = g-≈′ } → record
      { f-≈ = trans f-≈ f-≈′
      ; g-≈ = trans g-≈ g-≈′
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
  ; assoc     = record { f-≈ = assoc ; g-≈ = sym assoc }
  ; identityˡ = record { f-≈ = identityˡ ; g-≈ = identityʳ }
  ; identityʳ = record { f-≈ = identityʳ ; g-≈ = identityˡ }
  ; equiv     = ≃-isEquivalence
  ; ∘-resp-≈  = λ where
    record { f-≈ = f-≈ ; g-≈ = g-≈ } record { f-≈ = f-≈′ ; g-≈ = g-≈′ } → record
      { f-≈ = ∘-resp-≈ f-≈ f-≈′
      ; g-≈ = ∘-resp-≈ g-≈′ g-≈
      }
  }
  where open Equiv

