{-# OPTIONS --without-K --safe #-}

open import Categories.Category

-- Lifts a 1-Category into a bicategory

module Categories.Bicategory.Construction.1-Category
  {o ℓ e} b (C : Category o ℓ e) where

open import Level using (Lift; lift)
open import Data.Unit using (⊤; tt)
open import Data.Product using (uncurry)
open import Relation.Binary using (Setoid)

open import Categories.Bicategory
open import Categories.Category.Construction.0-Groupoid using (0-Groupoid)
open import Categories.Category.Instance.Cats using (Cats)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Instance.Cats using (module Product)
open import Categories.Category.Groupoid using (Groupoid; IsGroupoid)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Construction.Constant using (const)
open import Categories.Functor.Bifunctor using (Bifunctor)

private module C = Category C
open C hiding (id)

1-Category : Bicategory ℓ e b o
1-Category = record
  { enriched = record
    { Obj     = Obj
    ; hom     = hom
    ; id      = id
    ; ⊚       = ⊚
    ; ⊚-assoc = ⊚-assoc
    ; unitˡ   = unitˡ
    ; unitʳ   = unitʳ
    }
  ; triangle = lift tt
  ; pentagon = lift tt
  }
  where
    open Monoidal (Product.Cats-Monoidal {ℓ} {e} {b})
    open Commutation (Cats ℓ e b)

    -- Since we are doing Setoid-enriched category theory, we don't
    -- lift homsets to discrete hom-categories, but hom-setoids to
    -- thin hom-groupoids.

    hom : C.Obj → C.Obj → Category ℓ e b
    hom A B = Groupoid.category (0-Groupoid b (hom-setoid {A} {B}))

    id : ∀ {A} → Functor unit (hom A A)
    id = const C.id

    ⊚ : ∀ {A B C} → Bifunctor (hom B C) (hom A B) (hom A C)
    ⊚ {A} {B} {C} = record
      { F₀ = uncurry _∘_
      ; F₁ = uncurry ∘-resp-≈
      ; identity     = lift tt
      ; homomorphism = lift tt
      ; F-resp-≈     = λ _ → lift tt
      }

    ⊚-assoc : ∀ {A B C D} →
      [ (hom C D ⊗₀ hom B C) ⊗₀ hom A B ⇒ hom A D ]⟨
        ⊚ ⊗₁ idF          ⇒⟨ hom B D ⊗₀ hom A B ⟩
        ⊚
      ≈ associator.from   ⇒⟨ hom C D ⊗₀ (hom B C ⊗₀ hom A B) ⟩
        idF ⊗₁ ⊚          ⇒⟨ hom C D ⊗₀ hom A C ⟩
        ⊚
      ⟩
    ⊚-assoc = record
      { F⇒G = record { η = λ _ →     assoc ; commute = λ _ → lift tt }
      ; F⇐G = record { η = λ _ → sym-assoc ; commute = λ _ → lift tt }
      ; iso = λ _ → record { isoˡ = lift tt ; isoʳ = lift tt }
      }

    unitˡ : ∀ {A B} →
      [ unit ⊗₀ hom A B ⇒ hom A B ]⟨
        id ⊗₁ idF    ⇒⟨ hom B B ⊗₀ hom A B ⟩
        ⊚
      ≈ unitorˡ.from
      ⟩
    unitˡ = record
      { F⇒G = record { η = λ _ →           identityˡ ; commute = λ _ → lift tt }
      ; F⇐G = record { η = λ _ → Equiv.sym identityˡ ; commute = λ _ → lift tt }
      ; iso = λ _ → record { isoˡ = lift tt ; isoʳ = lift tt }
      }

    unitʳ : ∀ {A B} →
      [ hom A B ⊗₀ unit ⇒ hom A B ]⟨
        idF ⊗₁ id    ⇒⟨ hom A B ⊗₀ hom A A ⟩
        ⊚
      ≈ unitorʳ.from
      ⟩
    unitʳ = record
      { F⇒G = record { η = λ _ →           identityʳ ; commute = λ _ → lift tt }
      ; F⇐G = record { η = λ _ → Equiv.sym identityʳ ; commute = λ _ → lift tt }
      ; iso = λ _ → record { isoˡ = lift tt ; isoʳ = lift tt }
      }

open Bicategory 1-Category

-- The hom-categories are hom-groupoids

hom-isGroupoid : ∀ {A B} → IsGroupoid (hom A B)
hom-isGroupoid = Groupoid.isGroupoid (0-Groupoid b hom-setoid)
