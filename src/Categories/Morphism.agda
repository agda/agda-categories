{-# OPTIONS --without-K --safe #-}

{-
  Properties and definitions regarding Morphisms of a category:
  - Monomorphism
  - Epimorphism
  - Isomorphism
  - (object) equivalence ('spelled' _≅_ ). Exported as the module ≅
-}
open import Categories.Category.Core

module Categories.Morphism {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level
open import Relation.Binary hiding (_⇒_)
open import Data.Fin using (Fin; zero) renaming (suc to nzero)

open import Categories.Morphism.Reasoning.Core 𝒞

open Category 𝒞

private
  variable
    A B C : Obj

Mono : ∀ (f : A ⇒ B) → Set (o ⊔ ℓ ⊔ e)
Mono {A = A} f = ∀ {C} → (g₁ g₂ : C ⇒ A) → f ∘ g₁ ≈ f ∘ g₂ → g₁ ≈ g₂

JointMono : {ι : Level} (I : Set ι) (B : I → Obj) → ((i : I) → A ⇒ B i) → Set (o ⊔ ℓ ⊔ e ⊔ ι)
JointMono {A} I B f = ∀ {C} → (g₁ g₂ : C ⇒ A) → ((i : I) → f i ∘ g₁ ≈ f i ∘ g₂) → g₁ ≈ g₂

JointMono₂ : (f : A ⇒ B) (g : A ⇒ C) → Set (o ⊔ ℓ ⊔ e)
JointMono₂ {A}{B}{C} f g = JointMono (Fin 2) (λ{zero → B; (nzero _) → C}) (λ{zero → f; (nzero _) → g})

record _↣_ (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    mor  : A ⇒ B
    mono : Mono mor

Epi : ∀ (f : A ⇒ B) → Set (o ⊔ ℓ ⊔ e)
Epi {B = B} f = ∀ {C} → (g₁ g₂ : B ⇒ C) → g₁ ∘ f ≈ g₂ ∘ f → g₁ ≈ g₂

JointEpi : (I : Set) (A : I → Obj) → ((i : I) → A i ⇒ B) → Set (o ⊔ ℓ ⊔ e)
JointEpi {B} I A f = ∀ {C} → (g₁ g₂ : B ⇒ C) → ((i : I) → g₁ ∘ f i ≈ g₂ ∘ f i) → g₁ ≈ g₂

JointEpi₂ : (f : A ⇒ B) (g : C ⇒ B) → Set (o ⊔ ℓ ⊔ e)
JointEpi₂ {A}{B}{C} f g = JointEpi (Fin 2) (λ{zero → A; (nzero _) → C}) (λ{zero → f; (nzero _) → g})

record _↠_ (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    mor : A ⇒ B
    epi : Epi mor

_SectionOf_ : (g : B ⇒ A) (f : A ⇒ B) → Set e
g SectionOf f = f ∘ g ≈ id

_RetractOf_ : (g : B ⇒ A) (f : A ⇒ B) → Set e
g RetractOf f = g ∘ f ≈ id

record Retract (X U : Obj) : Set (ℓ ⊔ e) where
  field
    section : X ⇒ U
    retract : U ⇒ X
    is-retract : retract ∘ section ≈ id

record Iso (from : A ⇒ B) (to : B ⇒ A) : Set e where
  field
    isoˡ : to ∘ from ≈ id
    isoʳ : from ∘ to ≈ id

-- We often say that a morphism "is an iso" if there exists some inverse to it.
-- This does buck the naming convention we use somewhat, but it lines up
-- better with the literature.
record IsIso (from : A ⇒ B) : Set (ℓ ⊔ e) where
  field
    inv : B ⇒ A
    iso : Iso from inv

  open Iso iso public

infix 4 _≅_
record _≅_ (A B : Obj) : Set (ℓ ⊔ e) where
  field
    from : A ⇒ B
    to   : B ⇒ A
    iso  : Iso from to

  open Iso iso public

-- don't pollute the name space too much
private
  ≅-refl : Reflexive _≅_
  ≅-refl = record
    { from = id
    ; to   = id
    ; iso  = record
      { isoˡ = identity²
      ; isoʳ = identity²
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
        to A≅B ∘ from A≅B                       ≈⟨  isoˡ A≅B  ⟩
        id                                      ∎
      ; isoʳ = begin
        (from B≅C ∘ from A≅B) ∘ to A≅B ∘ to B≅C ≈⟨ cancelInner (isoʳ A≅B) ⟩
        from B≅C ∘ to B≅C                       ≈⟨ isoʳ B≅C ⟩
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

-- But make accessing it easy:
module ≅ = IsEquivalence ≅-isEquivalence

≅-setoid : Setoid _ _
≅-setoid = record
  { Carrier       = Obj
  ; _≈_           = _≅_
  ; isEquivalence = ≅-isEquivalence
  }
