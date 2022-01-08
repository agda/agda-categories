{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Properties.Setoids.Choice where

open import Categories.Category using (Category)
open import Categories.Category.Exact using (Exact)
open import Categories.Category.Instance.Setoids using (Setoids)

open import Data.Product using (∃; proj₁; proj₂; _,_; Σ-syntax; _×_; -,_; map; zip; swap; map₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Equality as SΠ using (Π; _⇨_) renaming (id to ⟶-id; _∘_ to _∘⟶_)

open import Level
open import Relation.Binary using (Setoid; Rel; REL; IsEquivalence)
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
  open import Categories.Object.InternalRelation using (Relation) 

  -- Presentation axiom, aka CoSHEP (http://nlab-pages.s3.us-east-2.amazonaws.com/nlab/show/presentation+axiom)
  record CoSHEP (A : Setoid ℓ ℓ) : Set (Level.suc ℓ) where
    field
      {P} : Setoid ℓ ℓ
      pre : P ⇒ A
      choice : {X : Setoid ℓ ℓ} (f : X ⇒ P) → SSurj ℓ f → Σ[ g ∈ ∣ P ⇨ X ∣ ] [ P ⇨ P ][ f ∘ g ≈ id ]

  Setoid-CoSHEP : (A : Setoid ℓ ℓ) → CoSHEP A
  Setoid-CoSHEP A = record
    { P = record
           { Carrier = ∣ A ∣
           ; _≈_ = P._≡_
           ; isEquivalence = record { refl = P.refl ; sym = P.sym ; trans = P.trans }
           }
    ; pre = record
           { _⟨$⟩_ = λ x → x
           ; cong = λ {x}{y} eq → P.subst (λ z → [ A ][ x ≈ z ]) eq (refl A)
           }
    ; choice = λ {X} f surj → record
           { _⟨$⟩_ = λ y → let x , _ = surj y in x
           ; cong = λ {x}{y} x≡y → P.subst (λ z → [ X ][ proj₁ (surj x) ≈ proj₁ (surj z) ]) x≡y (refl X)
           }
           , λ {x}{y} x≡y → let z , eq = surj x in P.trans eq x≡y
    }

  entire : {A B : Setoid ℓ ℓ} → (R : Relation S A B) → Set ℓ
  entire {A} R = ∀ (x : ∣ A ∣) →  Σ[ e ∈ ∣ dom ∣ ]  [ A ][ p₁ ⟨$⟩ e ≈ x ]  
    where open Relation R

  ℕ-Setoid : Setoid ℓ ℓ
  ℕ-Setoid = record { Carrier = Lift _ ℕ ; _≈_ = P._≡_  ; isEquivalence = record { refl = P.refl ; sym = P.sym ; trans = P.trans } }

  record DepChoice {A : Setoid ℓ ℓ} (R : Relation S A A) (inhb : ∣ A ∣) (ent : entire R) : Set (Level.suc ℓ) where
    open Relation R
    
    field
      pair   : ℕ → ∣ dom ∣
      chain  : ∀ (n : ℕ) → [ A ][ p₁ ⟨$⟩ pair (ℕ.suc n) ≈ p₂ ⟨$⟩ pair n ]
  
  -- Dependent choice for setoids 
  Setoid-DepChoice :  {A : Setoid ℓ ℓ} (R : Relation S A A) (inhb : ∣ A ∣) (ent : entire R) → DepChoice R inhb ent
  Setoid-DepChoice {A} R inhb ent = record
    { pair  = pair
    ; chain = chain
    }
      where
        open Relation R
        
        pair : ℕ → ∣ dom ∣
        pair ℕ.zero = proj₁ (ent inhb)
        pair (ℕ.suc n) = let x , _ = ent (p₂ ⟨$⟩ pair n) in x

        chain : (n : ℕ) → [ A ][ p₁ ⟨$⟩ proj₁ (ent (p₂ ⟨$⟩ pair n)) ≈ p₂ ⟨$⟩ pair n ]
        chain ℕ.zero    = let _ , eq = ent (p₂ ⟨$⟩ proj₁ (ent inhb)) in eq
        chain (ℕ.suc n) = let x , eq = ent (p₂ ⟨$⟩ proj₁ (ent (p₂ ⟨$⟩ pair n))) in eq

  -- Countable choice for setoids 
  ℕ-Choice :  ∀ {A : Setoid ℓ ℓ} (f : A ⇒ ℕ-Setoid) → SSurj ℓ f → Σ[ g ∈ ∣ ℕ-Setoid ⇨ A ∣ ] [ ℕ-Setoid ⇨ ℕ-Setoid ][ f ∘ g ≈ id ]
  ℕ-Choice {A} f surj = record
    { _⟨$⟩_ = λ n → let x , eq = surj n in x
    ; cong = λ {n}{m} eq → let x , _ = surj n; y , _ = surj m in P.subst (λ m → [ A ][ proj₁ (surj n) ≈ proj₁ (surj m) ]) eq (refl A) 
    }
    , λ {n}{m} n≡m → let _ , eq = surj n in P.trans eq n≡m
