{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Properties.Setoids.Exact where

open import Level
open import Data.Product using (Σ; proj₁; proj₂; _,_; Σ-syntax; _×_; -,_)
open import Function.Equality using (Π)
open import Relation.Binary using (Setoid; Rel)
open import Categories.Category using (Category; _[_,_])
open import Categories.Category.Instance.Setoids
open import Categories.Category.Exact
open import Categories.Category.Cocartesian
open import Categories.Diagram.Pullback
open import Categories.Diagram.Pullback.Properties
open import Categories.Category.Instance.Properties.Setoids.Limits.Canonical
open import Categories.Category.Monoidal.Instance.Setoids 
open import Data.Sum.Relation.Binary.Pointwise
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using ([_,_]′; _⊎_)
open import Function.Equality as SΠ renaming (id to ⟶-id)
open import Data.Product using (∃)

open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cartesian)

open Π

module _ ℓ where
  private
    S = Setoids ℓ ℓ
    module S = Category S
    
  open Pullback
  
  Setoids-Exact : Exact (Setoids ℓ ℓ)
  Setoids-Exact = record
    { regular = record
        { finitely-complete = record
           { cartesian = Setoids-Cartesian
           ; equalizer = λ _ _ → pullback×cartesian⇒equalizer S (pullback ℓ ℓ) Setoids-Cartesian
           }
        ; coeq-of-kernelpairs = λ f kp → {!!} -- canonical colimits
        ; pullback-of-regularepi-is-regularepi = {!!}
        }
    ; quotient = λ E → record { arr = ? ; isCoequalizer = ? }
    ; effective = {!!}
    }
