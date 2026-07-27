{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category using (module Definitions)
open import Categories.Morphism.Lifts using (MorphismClass)


-- Consider a category 𝒞 and two morphism classes ℰ and ℳ.
-- The level of the morphism equalities is called `eq`
-- such that the identifier `e` stays fresh for members of ℰ.
module Categories.Morphism.FactorizationSystem.Core
       {o ℓ eq} (𝒞 : Category o ℓ eq)
       {ℓℰ ℓℳ} (ℰ : MorphismClass 𝒞 ℓℰ) (ℳ : MorphismClass 𝒞 ℓℳ) where

open import Level

open import Categories.Morphism.Lifts 𝒞 using (MorphismClassMember; ≈-closed; UniqueDiagonal; Diagonal)
open import Categories.Morphism {o} {ℓ} {eq} 𝒞 using (IsIso)
open Category 𝒞
open Definitions 𝒞 using (CommutativeSquare)
open MorphismClassMember using (mor)

private
  variable
    A B C D : Obj

-- We write ->> / ↠ for morphisms in ℰ
_↠_ : Obj → Obj → Set (ℓ ⊔ ℓℰ)
_↠_ = MorphismClassMember ℰ

-- We write >-> / ↣ for morphisms in ℳ
_↣_ : Obj → Obj → Set (ℓ ⊔ ℓℳ)
_↣_ = MorphismClassMember ℳ

record Factorization (h : A ⇒ B) : Set (o ⊔ ℓ ⊔ eq ⊔ ℓℰ ⊔ ℓℳ) where
  field
    Im : Obj
    e : A ↠ Im
    m : Im ↣ B
    m∘e≈h : mor m ∘ mor e ≈ h

-- A factorization system (also called factorization structure) for
-- morphisms in the category 𝒞, see section 14 of "Abstract and
-- Concrete Categories - The Joy of Cats" by Adámek, Herrlich, Strecker, 2004.
record FactorizationSystem : Set (o ⊔ ℓ ⊔ eq ⊔ ℓℰ ⊔ ℓℳ) where
  field
    ℰ-resp-≈ : ≈-closed ℰ
    ℳ-resp-≈ : ≈-closed ℳ
    -- 1. every morphism admits an (ℰ,ℳ)-factorization
    factor : ∀ (f : A ⇒ B) → Factorization f
    -- 2. ℰ and ℳ are closed under compositions with isomorphisms:
    Iso∘ℰ : ∀ {h : B ⇒ C} → IsIso h → (e : A ↠ B) → ℰ (h ∘ mor e)
    ℳ∘Iso : ∀ (m : B ↣ C) → {h : A ⇒ B} → IsIso h → ℳ (mor m ∘ h)
    -- 3. every commutative square of the form
    --      e
    --   A ───>> B
    --   │     / │
    --   │  ∃!╱  │
    -- f │   ╱   │ g
    --   │  ╱    │
    --   V V     V
    --    C >──> D
    --      m
    --  has a unique diagonal filler.
    diagonal-filler : {f : A ⇒ C} {g : B ⇒ D} (e : A ↠ B) (m : C ↣ D)
                      (comm : CommutativeSquare (mor e) f g (mor m))
                      → UniqueDiagonal (mor e) f g (mor m)
  diag-unique₂ : {f : A ⇒ C} {g : B ⇒ D} (e : A ↠ B) (m : C ↣ D)
            → (d₁ d₂ : Diagonal (mor e) f g (mor m))
            → Diagonal.d d₁ ≈ Diagonal.d d₂
  diag-unique₂ {f = f} {g = g} e m d₁ d₂ =
    UniqueDiagonal.unique₂ (diagonal-filler e m (Diagonal.comm d₁)) d₁ d₂

