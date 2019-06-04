{-# OPTIONS --without-K --safe #-}

module Categories.NaturalTransformation.NaturalIsomorphism where

open import Level
open import Relation.Binary using (IsEquivalence)

open import Categories.Category
open import Categories.Functor as ℱ hiding (id)
open import Categories.NaturalTransformation.Core as α hiding (id)
import Categories.Morphism as Morphism
import Categories.Morphism.Properties as Morphismₚ
import Categories.Square as Square
open import Categories.Functor.Properties

open import Relation.Binary

private
  variable
    o ℓ e o′ ℓ′ e′ : Level
    C D E : Category o ℓ e

record NaturalIsomorphism {C : Category o ℓ e}
                          {D : Category o′ ℓ′ e′}
                          (F G : Functor C D) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private module C = Category C
  private module D = Category D
  private module F = Functor F
  private module G = Functor G
  open F
  open G renaming (F₀ to G₀; F₁ to G₁)

  field
    F⇒G : NaturalTransformation F G
    F⇐G : NaturalTransformation G F

  module ⇒ = NaturalTransformation F⇒G
  module ⇐ = NaturalTransformation F⇐G

  open Morphism D

  field
    iso : ∀ X → Iso (⇒.η X) (⇐.η X)

id : Reflexive (NaturalIsomorphism {C = C} {D = D})
id {C = C} {D = D} {x = F} = record
  { F⇒G = α.id
  ; F⇐G = α.id
  ; iso = λ A → record
    { isoˡ = Category.identityˡ D
    ; isoʳ = Category.identityʳ D
    }
  }

sym : Symmetric (NaturalIsomorphism {C = C} {D = D})
sym {C = C} {D = D} F≃G = record
  { F⇒G = F⇐G
  ; F⇐G = F⇒G
  ; iso = λ X →
    let open Iso (iso X) in record
    { isoˡ = isoʳ
    ; isoʳ = isoˡ
    }
  }
  where open NaturalIsomorphism F≃G
        open Morphism D

trans : Transitive (NaturalIsomorphism {C = C} {D = D})
trans {C = C} {D = D} F≃G G≃H = record
  { F⇒G = F⇒G G≃H ∘ᵥ F⇒G F≃G
  ; F⇐G = F⇐G F≃G ∘ᵥ F⇐G G≃H
  ; iso = λ X → record
    { isoˡ = begin
      D [ η (F⇐G F≃G ∘ᵥ F⇐G G≃H) X ∘ η (F⇒G G≃H ∘ᵥ F⇒G F≃G) X ] ≈⟨ cancelInner (isoˡ (iso G≃H X)) ⟩
      η (F⇐G F≃G ∘ᵥ F⇒G F≃G) X                                  ≈⟨ isoˡ (iso F≃G X) ⟩
      D.id                                                      ∎
    ; isoʳ = begin
      D [ η (F⇒G G≃H ∘ᵥ F⇒G F≃G) X ∘ η (F⇐G F≃G ∘ᵥ F⇐G G≃H) X ] ≈⟨ cancelInner (isoʳ (iso F≃G X)) ⟩
      η (F⇒G G≃H ∘ᵥ F⇐G G≃H) X                                  ≈⟨ isoʳ (iso G≃H X) ⟩
      D.id                                                      ∎
    }
  }
  where module D = Category D
        open NaturalIsomorphism
        open NaturalTransformation
        open Morphism D
        open Iso
        open Category.HomReasoning D
        open Square D

isEquivalence : IsEquivalence (NaturalIsomorphism {C = C} {D = D})
isEquivalence {C = C} {D = D} = record
  { refl  = id
  ; sym   = sym
  ; trans = trans
  }

setoid : ∀ {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → Setoid _ _
setoid {C = C} {D = D} = record 
  { Carrier       = Functor C D
  ; _≈_           = NaturalIsomorphism
  ; isEquivalence = isEquivalence {C = C} {D = D}
  }

infixr 9 _ⓘˡ_ _ⓘʳ_

_ⓘˡ_ : ∀ {F G : Functor C D} →
         (H : Functor D E) → (η : NaturalIsomorphism F G) → NaturalIsomorphism (H ∘F F) (H ∘F G)
_ⓘˡ_ {C = C} {E = E} H η = record
  { F⇒G = H ∘ˡ F⇒G
  ; F⇐G = H ∘ˡ F⇐G
  ; iso = λ X → [ H ]-resp-Iso (iso X)
  }
  where open NaturalIsomorphism η
        open Functor H

_ⓘʳ_ : ∀ {F G : Functor C D} →
         (η : NaturalIsomorphism F G) → (K : Functor E C) → NaturalIsomorphism (F ∘F K) (G ∘F K)
_ⓘʳ_ η K = record
  { F⇒G = F⇒G ∘ʳ K
  ; F⇐G = F⇐G ∘ʳ K
  ; iso = λ X → iso (F₀ X)
  }
  where open NaturalIsomorphism η
        open Functor K
