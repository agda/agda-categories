{-# OPTIONS --without-K --safe #-}
module Categories.Category.Monoidal.Instance.Rels where

-- The category of relations is cartesian and (by self-duality) co-cartesian.
-- Perhaps slightly counter-intuitively if you're used to categories which act
-- like Sets, the product acts on objects as the disjoint union.

open import Data.Empty.Polymorphic using (⊥; ⊥-elim)
import Data.Product as ×
open × using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function using (case_of_; flip)
open import Level using (Lift; lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Categories.Category.Cartesian using (Cartesian; module CartesianMonoidal)
open import Categories.Category.Core using (Category)
open import Categories.Category.Cocartesian using (Cocartesian)
open import Categories.Category.Instance.Rels using (Rels)

module _ {o ℓ} where

  Rels-Cartesian : Cartesian (Rels o ℓ)
  Rels-Cartesian = record
    { terminal = record
      { ⊤ = ⊥
      ; ⊤-is-terminal = record
        { ! = λ { _ (lift ()) }
        ; !-unique = λ _ → (λ { {_} {lift ()} }) , (λ { {_} {lift ()} })
        }
      }
    ; products = record
      { product = λ {A} {B} → record
        { A×B = A ⊎ B
        ; π₁ = [ (λ x y → Lift ℓ (x ≡ y) ) , (λ _ _ → ⊥) ]′
        ; π₂ = [ (λ _ _ → ⊥) , (λ x y → Lift ℓ (x ≡ y)) ]′
        ; ⟨_,_⟩ = λ L R c → [ L c , R c ]′
        ; project₁ = (λ { (inj₁ x , r , lift refl) → r})
          , λ r → inj₁ _ , r , lift refl
        ; project₂ = (λ { (inj₂ _ , r , lift refl) → r })
          , (λ r → inj₂ _ , r , lift refl)
        ; unique =
            λ { (p , q) (p′ , q′) → (λ { {_} {inj₁ a} r → case (q {_} {a} r) of λ { (inj₁ .a , s , lift refl) → s}
                                       ; {_} {inj₂ b} r → case (q′ {_} {b} r) of λ { (inj₂ .b , s , lift refl) → s} })
                                   , λ { {_} {inj₁ a} hxa → p (inj₁ a , hxa , lift refl)
                                       ; {_} {inj₂ b} hxb → p′ (inj₂ b , hxb , lift refl) } }
        }
      }
    }

  module Rels-CartesianMonoidal = CartesianMonoidal _ Rels-Cartesian
  open Rels-CartesianMonoidal renaming (monoidal to Rels-Monoidal) public

  -- because Rels is dual to itself, the proof that it is cocartesian resembles the proof that it's cartesian
  -- Rels is not self-dual 'on the nose', so we can't use duality proper.
  Rels-Cocartesian : Cocartesian (Rels o ℓ)
  Rels-Cocartesian = record
    { initial = record
      { ⊥ = ⊥
      ; ⊥-is-initial = record
        { ! = λ ()
        ; !-unique = λ _ → (λ { {()} }) , (λ { {()} })
        }
      }
    ; coproducts = record
      { coproduct = λ {A} {B} → record
        { A+B = A ⊎ B
        ; i₁ = λ a → [ (λ a′ → Lift ℓ (a ≡ a′)) , (λ _ → ⊥) ]′
        ; i₂ = λ b → [ (λ _ → ⊥) , (λ b′ → Lift ℓ (b ≡ b′)) ]′
        ; [_,_] = λ L R a+b c → [ flip L c , flip R c ]′ a+b
        ; inject₁ = (λ { (inj₁ x , lift refl , fxy) → fxy})
          , λ r → inj₁ _ , lift refl , r
        ; inject₂ = (λ { (inj₂ _ , lift refl , r) → r })
          , (λ r → inj₂ _ , lift refl , r)
        ; unique = λ { (p , q) (p′ , q′) → (λ { {inj₁ a} r → case (q {a} r) of λ { (inj₁ .a , lift refl , s) → s}
                                              ; {inj₂ b} r → case (q′ {b} r) of λ { (inj₂ .b , lift refl , s) → s} })
                                          , λ { {inj₁ a} hxa → p (inj₁ a , lift refl , hxa)
                                              ; {inj₂ b} hxb → p′ (inj₂ b , lift refl , hxb) } }
        }
      }
    }
