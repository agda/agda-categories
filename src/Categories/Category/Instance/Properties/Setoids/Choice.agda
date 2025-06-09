{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Properties.Setoids.Choice where

open import Categories.Category using (Category)
open import Categories.Category.Exact using (Exact)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Instance.Properties.Setoids.Exact using (SSurj)
open import Categories.Object.InternalRelation using (Relation)

open import Data.Nat.Base using (ℕ)
open import Data.Product using (∃; proj₁; proj₂; _,_; Σ-syntax; _×_; -,_; map; zip; swap; map₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Function.Construct.Setoid using () renaming (setoid to _⇨_)
open import Level using (Level; Lift)
open import Relation.Binary using (Setoid; Rel; REL; IsEquivalence)
import Relation.Binary.PropositionalEquality.Core as P
import Relation.Binary.Reasoning.Setoid as SR

open Setoid renaming (_≈_ to [_][_≈_]; Carrier to ∣_∣) using (isEquivalence; refl; sym; trans)

module _ ℓ where
  private
    S = Setoids ℓ ℓ
    open Category S hiding (_≈_)
    module S = Category S

  -- Presentation axiom, aka CoSHEP (https://ncatlab.org/nlab/show/presentation+axiom)
  record CoSHEP (A : Setoid ℓ ℓ) : Set (Level.suc ℓ) where
    field
      {P} : Setoid ℓ ℓ
      pre   : P ⇒ A
      surj  : SSurj ℓ pre
      split : {X : Setoid ℓ ℓ} (f : X ⇒ P) → SSurj ℓ f → Σ[ g ∈ ∣ P ⇨ X ∣ ] [ P ⇨ P ][ f ∘ g ≈ id ]

  Setoid-CoSHEP : (A : Setoid ℓ ℓ) → CoSHEP A
  Setoid-CoSHEP A = record
    { P = record
           { Carrier = ∣ A ∣
           ; _≈_ = P._≡_
           ; isEquivalence = record { refl = P.refl ; sym = P.sym ; trans = P.trans }
           }
    ; pre = record
           { to = λ x → x
           ; cong = λ {x} eq → P.subst (λ z → [ A ][ x ≈ z ]) eq (refl A)
           }
    ; surj = λ x → x , refl A
    ; split = λ {X} f surj → record
           { to = λ y → let x , _ = surj y in x
           ; cong = λ {x}{y} x≡y → P.subst (λ z → [ X ][ proj₁ (surj x) ≈ proj₁ (surj z) ]) x≡y (refl X)
           }
           , λ {x} → proj₂ (surj x)
    }

  entire : {A B : Setoid ℓ ℓ} → (R : Relation S A B) → Set ℓ
  entire {A} R = ∀ (x : ∣ A ∣) →  Σ[ e ∈ ∣ dom ∣ ]  [ A ][ p₁ ⟨$⟩ e ≈ x ]
    where open Relation R

  functional : {A B : Setoid ℓ ℓ} → (R : Relation S A B) → Set ℓ
  functional {A}{B} R = ∀ (e₁ e₂ : ∣ dom ∣) → [ A ][ p₁ ⟨$⟩ e₁ ≈ p₁ ⟨$⟩ e₂ ] → [ B ][ p₂ ⟨$⟩ e₁ ≈ p₂ ⟨$⟩ e₂ ]
    where open Relation R

  ℕ-Setoid : Setoid ℓ ℓ
  ℕ-Setoid = record { Carrier = Lift _ ℕ ; _≈_ = P._≡_
                    ; isEquivalence = record { refl = P.refl ; sym = P.sym ; trans = P.trans }
                    }

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
    { to = λ n → let x , eq = surj n in x
    ; cong = λ {n}{m} eq → let x , _ = surj n; y , _ = surj m in P.subst (λ m → [ A ][ proj₁ (surj n) ≈ proj₁ (surj m) ]) eq (refl A)
    }
    , λ {n} → proj₂ (surj n)

  -- principle of unique choice for setoids
  -- https://ncatlab.org/nlab/show/principle+of+unique+choice
  record UniqueChoice {A B : Setoid ℓ ℓ} (R : Relation S A B) (ent : entire R) (frel : functional R) : Set ℓ where
    open Relation R

    field
      fun    : A ⇒ B
      isfun  : ∀ (e : ∣ dom ∣) →  [ B ][ fun ⟨$⟩ (p₁ ⟨$⟩ e) ≈  p₂ ⟨$⟩ e ]

  Setoid-UniqueChoice :  {A B : Setoid ℓ ℓ} (R : Relation S A B) (ent : entire R) (frel : functional R) → UniqueChoice R ent frel
  Func.to (UniqueChoice.fun (Setoid-UniqueChoice R ent frel)) x =  p₂ ⟨$⟩ proj₁ (ent x)
        where open Relation R

  Func.cong (UniqueChoice.fun (Setoid-UniqueChoice {A} {B} R ent frel)) {n} {m} n≈m =
     let (en , p₁en≈n) = ent n
         (em , p₁em≈m) = ent m in frel en em
     (begin
        p₁ ⟨$⟩ en  ≈⟨ p₁en≈n ⟩
               n   ≈⟨ n≈m ⟩
               m  ≈˘⟨ p₁em≈m ⟩
        p₁ ⟨$⟩ em
     ∎)
       where
         open Relation R
         open SR A

  UniqueChoice.isfun (Setoid-UniqueChoice R ent frel) e = let (e' , p₁e'≈p₁e) = ent (p₁ ⟨$⟩ e) in frel e' e p₁e'≈p₁e
      where open Relation R
