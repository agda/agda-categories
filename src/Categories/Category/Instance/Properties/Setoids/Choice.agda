{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Properties.Setoids.Choice where

open import Categories.Category using (Category)
open import Categories.Category.Exact using (Exact)
open import Categories.Category.Instance.Setoids using (Setoids)

open import Data.Product using (∃; proj₁; proj₂; _,_; Σ-syntax; _×_; -,_; map; zip; swap; map₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Equality as SΠ using (Π; _⇨_) renaming (id to ⟶-id; _∘_ to _∘⟶_)

open import Level
open import Relation.Binary using (Setoid; Rel; IsEquivalence)
import Relation.Binary.Reasoning.Setoid as SR

open import Data.Nat.Base
import Relation.Binary.PropositionalEquality.Core as P

open Setoid renaming (_≈_ to [_][_≈_]; Carrier to ∣_∣) using (isEquivalence; refl; sym; trans)
open Π using (_⟨$⟩_; cong)

module _ ℓ where
  private
    S = Setoids ℓ ℓ
    open Category S hiding (_≈_)
    module S = Category S

  open import Categories.Category.Instance.Properties.Setoids.Exact

  ℕ-Setoid : Setoid ℓ ℓ
  ℕ-Setoid = record { Carrier = Lift _ ℕ ; _≈_ = P._≡_  ; isEquivalence = record { refl = P.refl ; sym = P.sym ; trans = P.trans } }

  -- Countable choice for setoids 
  ℕ-Choice :  ∀ {A : Setoid ℓ ℓ} (f : A ⇒ ℕ-Setoid) → SSurj ℓ f → Σ[ g ∈ ∣ ℕ-Setoid ⇨ A ∣ ] [ ℕ-Setoid ⇨ ℕ-Setoid ][ f ∘ g ≈ id ]
  ℕ-Choice {A} f surj = record
    { _⟨$⟩_ = λ n → let x , eq = surj n in x
    ; cong = λ {n}{m} eq → let x , _ = surj n; y , _ = surj m in (P.subst (λ m → [ A ][ proj₁ (surj n) ≈ proj₁ (surj m) ])) eq (refl A) 
    }
    , λ {n}{m} n≡m → let _ , eq = surj n in P.trans eq n≡m
