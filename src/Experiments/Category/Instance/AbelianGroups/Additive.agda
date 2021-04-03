{-# OPTIONS --without-K --safe #-}
module Experiments.Category.Instance.AbelianGroups.Additive where

open import Level
open import Function using (_$_)
open import Data.Unit.Polymorphic
open import Data.Product using (Σ-syntax; _,_; _×_; proj₁; proj₂)

import Algebra.Construct.DirectProduct as DirectProducts
import Algebra.Construct.Zero as Zeros
open import Algebra.Properties.AbelianGroup

import Relation.Binary.Reasoning.Setoid as SR

open import Categories.Category
open import Categories.Object.Initial
open import Categories.Object.Zero
open import Categories.Object.Biproduct

import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR

open import Categories.Category.Preadditive
open import Categories.Category.Additive

open import Experiments.Category.Instance.AbelianGroups
open import Experiments.Category.Instance.AbelianGroups.Preadditive

private
  variable
    c ℓ : Level

open AbelianGroup
open AbelianGroupHomomorphism

𝟎 : Zero (AbelianGroups c ℓ)
𝟎 = record
  { 𝟘 = Zeros.abelianGroup
  ; isZero = record
    { isInitial = record
      { ! = λ {A} → record
        { ⟦_⟧ = λ _ → ε A
        ; cong = λ _ → refl A
        ; homo = λ _ _ → sym A (identityʳ A (ε A))
        }
      ; !-unique = λ  {A} f tt → sym A (ε-homo f)
      }
    }
  }

module _ {G : AbelianGroup c ℓ} where
  private
    module G = AbelianGroup G
    open SR G.setoid
    open Mor (AbelianGroups c ℓ)
    open Category (AbelianGroups c ℓ)

  -- All zero objects in Ab are trivial.
  zero-trivial : IsZero (AbelianGroups c ℓ) G → (x y : G.Carrier) → x G.≈ y
  zero-trivial is-zero x y = begin
    x   ≈˘⟨ iso.isoʳ x ⟩
    G.ε ≈⟨ iso.isoʳ y ⟩
    y ∎
    where
      module is-zero = IsZero is-zero
      module 𝟎 = Zero 𝟎
      module iso = _≅_ (up-to-iso (AbelianGroups c ℓ) 𝟎.initial is-zero.initial)

biproduct : ∀ {A B} → Biproduct (AbelianGroups c ℓ) A B
biproduct {A = A} {B = B} = record
  { A⊕B = DirectProducts.abelianGroup A B
  ; π₁ = record
    { ⟦_⟧ = proj₁
    ; cong = proj₁
    ; homo = λ _ _ → refl A
    }
  ; π₂ = record
    { ⟦_⟧ = proj₂
    ; cong = proj₂
    ; homo = λ _ _ → refl B
    }
  ; i₁ = record
    { ⟦_⟧ = λ x → x , B.ε
    ; cong = λ eq → eq , B.refl
    ; homo = λ _ _ → A.refl , B.sym (B.identityʳ _)
    }
  ; i₂ = record
    { ⟦_⟧ = λ x → A.ε , x
    ; cong = λ eq → A.refl , eq
    ; homo = λ _ _ → A.sym (A.identityʳ _) , B.refl
    }
  ; isBiproduct = record
    { isCoproduct = record
      { [_,_] = λ {C} f g →
        let module C = AbelianGroup C
            open SR (C.setoid)
            open MR (Delooping C)
        in record
          { ⟦_⟧ = λ { (a , b) → ⟦ f ⟧ a C.∙ ⟦ g ⟧ b }
          ; cong = λ { (eqa , eqb) → C.∙-cong (cong f eqa) (cong g eqb) }
          ; homo = λ { (a₁ , b₁)  (a₂ , b₂) → begin
            ⟦ f ⟧ (a₁ A.∙ a₂) C.∙ ⟦ g ⟧ (b₁ B.∙ b₂)           ≈⟨ C.∙-cong (homo f a₁ a₂) (homo g b₁ b₂) ⟩
            ⟦ f ⟧ a₁ C.∙ ⟦ f ⟧ a₂ C.∙ (⟦ g ⟧ b₁ C.∙ ⟦ g ⟧ b₂) ≈⟨ center (C.comm (⟦ f ⟧ a₂) (⟦ g ⟧ b₁)) ⟩
            ⟦ f ⟧ a₁ C.∙ (⟦ g ⟧ b₁ C.∙ ⟦ f ⟧ a₂ C.∙ ⟦ g ⟧ b₂) ≈⟨ pull-first C.refl ⟩
            ⟦ f ⟧ a₁ C.∙ ⟦ g ⟧ b₁ C.∙ (⟦ f ⟧ a₂ C.∙ ⟦ g ⟧ b₂) ∎
            }
          }
      ; inject₁ = λ {C} {f} {g} x →
        let open MR (Delooping C)
        in elimʳ (ε-homo g)
      ; inject₂ = λ {C} {f} {g} x →
        let open MR (Delooping C)
        in elimˡ (ε-homo f)
      ; unique = λ { {C} {h} {f} {g} eq₁ eq₂ (a , b) →
          let module C = AbelianGroup C
              open SR (C.setoid)
          in begin
            ⟦ f ⟧ a C.∙ ⟦ g ⟧ b                 ≈˘⟨ C.∙-cong (eq₁ a) (eq₂ b) ⟩
            ⟦ h ⟧ (a , B.ε) C.∙ ⟦ h ⟧ (A.ε , b) ≈˘⟨ homo h (a , B.ε) (A.ε , b) ⟩
            ⟦ h ⟧ (a A.∙ A.ε , B.ε B.∙ b)       ≈⟨ cong h ((A.identityʳ a) , (B.identityˡ b)) ⟩
            ⟦ h ⟧ (a , b) ∎
        }
      }
    ; isProduct = record
      { ⟨_,_⟩ = λ {C} f g →
        let module C = AbelianGroup C
            open SR (C.setoid)
            open MR (Delooping C)
        in record
          { ⟦_⟧ = λ x → (⟦ f ⟧ x) , (⟦ g ⟧ x)
          ; cong = λ eq → cong f eq , cong g eq
          ; homo = λ x y → (homo f x y) , (homo g x y)
          }
      ; project₁ = λ _ → A.refl
      ; project₂ = λ _ → B.refl
      ; unique = λ {C} {h} {f} {g} eq₁ eq₂ x → (A.sym (eq₁ x)) , (B.sym (eq₂ x))
      }
    ; π₁∘i₁≈id = λ _ → A.refl
    ; π₂∘i₂≈id = λ _ → B.refl
    ; permute = λ _ → A.refl , B.refl
    }
  }
  where
    module A = AbelianGroup A
    module B = AbelianGroup B

AbelianGroupsAdditive : Additive (AbelianGroups c ℓ)
AbelianGroupsAdditive = record
  { 𝟎 = 𝟎
  ; biproduct = biproduct
  ; preadditive = AbelianGroupsPreadditive
  }
