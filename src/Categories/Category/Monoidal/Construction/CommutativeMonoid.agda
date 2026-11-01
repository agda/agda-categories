{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (CommutativeMonoid)

-- A commutative monoid is a one-object monoidal category whose tensor is
-- multiplication.

module Categories.Category.Monoidal.Construction.CommutativeMonoid
  o {c ℓ} (M : CommutativeMonoid c ℓ) where

open import Data.Product using (_,_; uncurry)
import Relation.Binary.Reasoning.Setoid as SetoidR

open import Categories.Category.Core using (Category)
open import Categories.Category.Construction.MonoidAsCategory
open import Categories.Category.Monoidal.Core using (Monoidal; monoidalHelper)
open import Categories.Category.Monoidal.Symmetric using (Symmetric; symmetricHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)
import Categories.Morphism as Morphism

open CommutativeMonoid M
open import Algebra.Properties.CommutativeSemigroup commutativeSemigroup using (medial)

baseCat : Category o _ _
baseCat = MonoidAsCategory o monoid

CMonoidAsMonoidalCat : Monoidal (baseCat)
CMonoidAsMonoidalCat = monoidalHelper _ record
  { ⊗ = record
    { F₀ = λ _ → _
    ; F₁ = uncurry _∙_
    ; identity = identityˡ _
    ; homomorphism = medial _ _ _ _
    ; F-resp-≈ = uncurry ∙-cong
    }
  ; unit = _
  ; unitorˡ = Morphism.≅.refl _
  ; unitorʳ = Morphism.≅.refl _
  ; associator = Morphism.≅.refl _
  ; unitorˡ-commute = λ { {f = f} →
      trans (identityˡ _) (trans (identityˡ f) (sym (identityʳ f))) }
  ; unitorʳ-commute = λ { {f = f} → identityˡ (f ∙ ε) }
  ; assoc-commute = assoc-natural
  ; triangle = identityʳ _
  ; pentagon = trans (∙-cong (identityˡ _) (identityˡ _)) (identityˡ _)
  }
  where
  abstract
    -- The outer units are the components of the identity associator.
    assoc-natural : {f g h : Carrier} → ε ∙ ((f ∙ g) ∙ h) ≈ (f ∙ (g ∙ h)) ∙ ε
    assoc-natural {f = f} {g} {h} = begin
      ε ∙ ((f ∙ g) ∙ h)  ≈⟨ identityˡ _ ⟩
      (f ∙ g) ∙ h        ≈⟨ assoc f g h ⟩
      f ∙ (g ∙ h)        ≈⟨ identityʳ _ ⟨
      (f ∙ (g ∙ h)) ∙ ε  ∎
      where open SetoidR setoid

CMonoidAsSymmetricMonoidal : Symmetric CMonoidAsMonoidalCat
CMonoidAsSymmetricMonoidal = symmetricHelper _ record
  { braiding = niHelper record
    { η = λ _ → ε
    ; η⁻¹ = λ _ → ε
    ; commute = λ { (f , g) →
        trans (identityˡ _) (trans (comm f g) (sym (identityʳ _))) }
    ; iso = λ _ → record
      { isoˡ = identityˡ _
      ; isoʳ = identityˡ _
      }
    }
  ; commutative = identityˡ _
  ; hexagon = ∙-cong (identityˡ _) (identityˡ _)
  }
