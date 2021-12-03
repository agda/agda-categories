{-# OPTIONS --without-K --safe #-}

-- Formalization of internal relations
-- (=congruences: https://ncatlab.org/nlab/show/congruence)

open import Categories.Category
module Categories.Object.InternalRelation {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level hiding (zero)
open import Data.Unit
open import Data.Fin using (Fin; zero) renaming (suc to nzero)

import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR
open import Categories.Morphism.Notation

open import Categories.Diagram.Pullback
open import Categories.Diagram.KernelPair
open import Categories.Category.Cartesian

open import Categories.Category.BinaryProducts 𝒞 using (BinaryProducts; module BinaryProducts)

private
  module 𝒞 = Category 𝒞

open Category 𝒞
open Mor 𝒞

-- A relation is a span, "which is (-1)-truncated as a morphism into the cartesian product."
-- (https://ncatlab.org/nlab/show/span#correspondences)
isRelation : {X Y R : 𝒞.Obj} (f : R ⇒ X) (g : R ⇒ Y) → Set (o ⊔ ℓ ⊔ e)
isRelation{X}{Y}{R} f g = JointMono
     (Fin 2)
     (λ{zero → X; (nzero _) → Y})
     (λ{zero → f; (nzero _) → g}) 

record Relation (X Y : 𝒞.Obj) : Set (suc (o ⊔ ℓ ⊔ e)) where
  open Mor 𝒞
  
  field
    dom : 𝒞.Obj
    p₁ : dom ⇒ X 
    p₂ : dom ⇒ Y 

  field
    relation : isRelation p₁ p₂

record isEqSpan {X R : 𝒞.Obj} (f : R ⇒ X) (g : R ⇒ X) : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
     R×R : Pullback 𝒞 f g

  module R×R = Pullback R×R renaming (P to dom)

  field
     refl  : X ⇒ R
     sym   : R ⇒ R
     trans : R×R.dom ⇒ R
    
     is-refl₁ : f ∘ refl ≈ id
     is-refl₂ : g ∘ refl ≈ id

     is-sym₁ : f ∘ sym ≈ g
     is-sym₂ : g ∘ sym ≈ f

     is-trans₁ : f ∘ trans ≈ f ∘ R×R.p₁
     is-trans₂ : g ∘ trans ≈ g ∘ R×R.p₂

-- Internal equivalence
record Equivalence (X : 𝒞.Obj) : Set (suc (o ⊔ ℓ ⊔ e)) where
  open Mor 𝒞
  open BinaryProducts  

  field
     R : Relation X X
    
  open Relation R
  module R = Relation R

  field
    eqspan : isEqSpan R.p₁ R.p₂

module _ where
  open Pullback hiding (P)
  
  KP⇒EqSpan : {X Y : 𝒞.Obj} (f : X ⇒ Y) → (kp : KernelPair 𝒞 f) → (p : Pullback 𝒞 (p₁ kp) (p₂ kp)) → isEqSpan (p₁ kp) (p₂ kp)
  KP⇒EqSpan f kp p = record
    { R×R = p
    ; refl = universal kp {_} {id}{id} 𝒞.Equiv.refl
    ; sym  = universal kp {_} {p₂ kp}{p₁ kp} (𝒞.Equiv.sym (commute kp))
    ; trans = universal kp {_}{p₁ kp ∘ p₁ p}{p₂ kp ∘ p₂ p} (∘-resp-≈ʳ (commute p))
    ; is-refl₁  = p₁∘universal≈h₁ kp
    ; is-refl₂  = p₂∘universal≈h₂ kp
    ; is-sym₁   = p₁∘universal≈h₁ kp
    ; is-sym₂   = p₂∘universal≈h₂ kp
    ; is-trans₁ = p₁∘universal≈h₁ kp
    ; is-trans₂ = p₂∘universal≈h₂ kp
    }
                         
  KP⇒Relation : {X Y : 𝒞.Obj} (f : X ⇒ Y) → (kp : KernelPair 𝒞 f) → (p : Pullback 𝒞 (p₁ kp) (p₂ kp)) → isRelation (p₁ kp) (p₂ kp)
  KP⇒Relation f kp _ _ _ eq = unique-diagram kp (eq zero) (eq (nzero zero))
