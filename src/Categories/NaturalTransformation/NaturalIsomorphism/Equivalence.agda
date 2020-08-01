{-# OPTIONS --without-K --safe #-}
module Categories.NaturalTransformation.NaturalIsomorphism.Equivalence where

-- a certain notion of equivalence between Natural Isomorphisms.

open import Level
open import Data.Product using (_×_; _,_; map; zip)
open import Relation.Binary.Structures using (IsEquivalence)

open import Categories.Category.Core
open import Categories.Functor.Core using (Functor)
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (_≃_)
open import Categories.NaturalTransformation.Equivalence
open NaturalIsomorphism

private
  variable
    o ℓ e o′ ℓ′ e′ : Level
    C D : Category o ℓ e

infix 4 _≅_
_≅_ : ∀ {F G : Functor C D} → (α β : NaturalIsomorphism F G) → Set _
α ≅ β = F⇒G α ≃ F⇒G β × F⇐G α ≃ F⇐G β

≅-isEquivalence : ∀ {F G : Functor C D} → IsEquivalence (_≅_ {F = F} {G = G})
≅-isEquivalence {D = D} {F = F} {G = G} = record
  { refl  = H.refl , H.refl
  ; sym   =  map (λ z → H.sym z) (λ z → H.sym z) -- eta expansion needed
  ; trans = zip (λ a b → H.trans a b) λ a b → H.trans a b -- ditto
  }
  where module H = Category.Equiv D
