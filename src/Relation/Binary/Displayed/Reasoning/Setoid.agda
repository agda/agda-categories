{-# OPTIONS --safe --without-K #-}

open import Relation.Binary
open import Relation.Binary.Displayed

module Relation.Binary.Displayed.Reasoning.Setoid {a ℓ a′ ℓ′} {S : Setoid a ℓ} (S′ : DisplayedSetoid S a′ ℓ′) where

open import Level
open import Relation.Binary.Reasoning.Setoid S

open Setoid S
open DisplayedSetoid S′

infix 4 _IsRelatedTo[_]_

data _IsRelatedTo[_]_ {x y : Carrier} (x′ : Carrier′ x) (p : x IsRelatedTo y) (y′ : Carrier′ y) : Set (ℓ ⊔ ℓ′) where
  relTo[] : (x′≈[x≈y]y′ : x′ ≈[ begin p ] y′) → x′ IsRelatedTo[ p ] y′

infix  1 begin′_
infixr 2 step-≈[] step-≈˘[]
infix  4 _∎′

begin′_ : ∀ {x y} {x′ : Carrier′ x} {y′ : Carrier′ y} {x∼y : x IsRelatedTo y}
          → x′ IsRelatedTo[ x∼y ] y′ → x′ ≈[ begin x∼y ] y′
begin′ relTo[] x′≈[x≈y]y′ = x′≈[x≈y]y′

step-≈[] : ∀ {x y z} (x′ : Carrier′ x) {y′ : Carrier′ y} {z′ : Carrier′ z} {y∼z : y IsRelatedTo z} {x≈y : x ≈ y}
         → y′ IsRelatedTo[ y∼z ] z′ → x′ ≈[ x≈y ] y′ → x′ IsRelatedTo[ step-≈ x y∼z x≈y ] z′
step-≈[] x′ {y∼z = relTo _} (relTo[] y≈[]z) x≈[]y = relTo[] (trans′ x≈[]y y≈[]z)
syntax step-≈[] x′ y′∼z′ x′≈[]y′ = x′ ≈[]⟨ x′≈[]y′ ⟩ y′∼z′

step-≈˘[] : ∀ {x y z} (x′ : Carrier′ x) {y′ : Carrier′ y} {z′ : Carrier′ z} {y∼z : y IsRelatedTo z} {y≈x : y ≈ x}
          → y′ IsRelatedTo[ y∼z ] z′ → y′ ≈[ y≈x ] x′ → x′ IsRelatedTo[ step-≈˘ x y∼z y≈x ] z′
step-≈˘[] x′ y′∼z′ y′≈x′ = x′ ≈[]⟨ sym′ y′≈x′ ⟩ y′∼z′ 
syntax step-≈˘[] x′ y′∼z′ y′≈[]x′ = x′ ≈˘[]⟨ y′≈[]x′ ⟩ y′∼z′

_∎′ : ∀ {x} (x′ : Carrier′ x) → x′ IsRelatedTo[ x ∎ ] x′
_∎′ x′ = relTo[] refl′

-- TODO: propositional equality
-- Maybe TODO: have a convenient way to specify the base equality, e.g. _≈[_]⟨_⟩_
