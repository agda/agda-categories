{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Quivers where

-- The Category of Quivers

open import Level using (Level; suc; _⊔_)
open import Function using (_$_; flip)
open import Relation.Binary.PropositionalEquality as ≡
open import Relation.Binary.PropositionalEquality.Subst.Properties
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties hiding (trans)
open import Data.Quiver
open import Data.Quiver.Paths
import Data.Quiver.Morphism as QM
open QM using (Morphism; _≃_; ≃-Equivalence; ≃-resp-∘)

open import Categories.Category
import Categories.Category.Construction.PathCategory as PC
open import Categories.NaturalTransformation hiding (id)
open import Categories.NaturalTransformation.NaturalIsomorphism
  hiding (refl; sym; trans; isEquivalence; _≃_)
import Categories.Morphism.HeterogeneousIdentity as HId

private
  variable
    o ℓ e o′ ℓ′ e′ : Level

Quivers : ∀ o ℓ e → Category (suc (o ⊔ ℓ ⊔ e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
Quivers o ℓ e = record
  { Obj       = Quiver o ℓ e
  ; _⇒_       = Morphism
  ; _≈_       = _≃_
  ; id        = QM.id
  ; _∘_       = QM._∘_
  ; assoc     = λ {_ _ _ G} → record { F₀≡ = refl ; F₁≡ = Equiv.refl G }
  ; sym-assoc = λ {_ _ _ G} → record { F₀≡ = refl ; F₁≡ = Equiv.refl G }
  ; identityˡ = λ {_ G}     → record { F₀≡ = refl ; F₁≡ = Equiv.refl G }
  ; identityʳ = λ {_ G}     → record { F₀≡ = refl ; F₁≡ = Equiv.refl G }
  ; identity² = λ {G}       → record { F₀≡ = refl ; F₁≡ = Equiv.refl G }
  ; equiv     = ≃-Equivalence
  ; ∘-resp-≈  = QM.≃-resp-∘
  }
  where open Quiver using (module Equiv)
