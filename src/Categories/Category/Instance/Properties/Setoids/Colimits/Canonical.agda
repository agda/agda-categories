{-# OPTIONS --without-K --safe #-}

-- A "canonical" presentation of binary coproducts in Setoid.
--
-- Done by analogy with Categories.Category.Instance.Properties.Setoids.Colimits.Canonical

module Categories.Category.Instance.Properties.Setoids.Colimits.Canonical where

open import Level

open import Data.Product using (_,_; _×_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; map) renaming ([_,_] to ⟦_,_⟧; [_,_]′ to ⟦_,_⟧′)

open import Relation.Binary.Bundles using (Setoid)
open import Function.Equality as SΠ renaming (id to ⟶-id)
import Relation.Binary.Reasoning.Setoid as SR

open import Categories.Diagram.Pullback
open import Categories.Category.Instance.Setoids
open import Categories.Object.Coproduct


open Setoid renaming (_≈_ to [_][_≈_])

coproduct : ∀ (o ℓ : Level) (X Y : Setoid (o ⊔ ℓ) ℓ) → Coproduct (Setoids (o ⊔ ℓ) ℓ) X Y
coproduct _ _ X Y = record
   { A+B = record
       { Carrier = X₀ ⊎ Y₀
       ; _≈_ = λ { (inj₁ p) (inj₁ q) → [ X ][ p ≈ q ]
                 ; (inj₁ p) (inj₂ q) → Lift _ ⊥
                 ; (inj₂ p) (inj₁ q) → Lift _ ⊥
                 ; (inj₂ p) (inj₂ q) → [ Y ][ p ≈ q ]
                 } 
       ; isEquivalence = record
         { refl = λ { {inj₁ x} → refl X ; {inj₂ y} → refl Y}
         ; sym = λ { {inj₁ _} {inj₁ _} eq → sym X eq ; {inj₂ _} {inj₂ _} → sym Y}
         ; trans = λ { {inj₁ _} {inj₁ _} {inj₁ _} → trans X ; {inj₂ _} {inj₂ _} {inj₂ _} → trans Y}
         }
       }
   ; i₁ = record { _⟨$⟩_ = inj₁ ; cong = λ x → x }
   ; i₂ = record { _⟨$⟩_ = inj₂ ; cong = λ x → x }
   ; [_,_] = λ f g → record
        { _⟨$⟩_ = λ { (inj₁ x) → f ⟨$⟩ x ; (inj₂ y) → g ⟨$⟩ y}
        ; cong = λ { {inj₁ _} {inj₁ _} eq → cong f eq ; {inj₂ _} {inj₂ _} → cong g}
        }
   ; inject₁ = λ {_}{f} → cong f
   ; inject₂ = λ {_}{_}{g} → cong g
   -- The first argument of sym must be 'g.B' But that is just Agda's internal name, which seems to be
   -- inaccessible, because the codomain of g is declared to be private. It is not clear how to access it.
   ; unique = λ{ {_} {f}{g}{h} eq₁ eq₂ {inj₁ x} {inj₁ y} x≈y → sym {!!} {!!} ; {_} {_} {g} eq₁ eq₂ {inj₂ y₁} {inj₂ y} x≈y → sym {!!} {!!}}
   }
     where X₀ = Carrier X; Y₀ = Carrier Y
