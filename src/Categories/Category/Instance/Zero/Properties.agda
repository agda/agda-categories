{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Zero.Properties {o ℓ e} where

open import Data.Empty.Polymorphic using (⊥-elim)

open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Categories.Category.Instance.Cats using (Cats)
open import Categories.Category.Instance.Zero.Core using (Zero)
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)
open import Categories.Object.Initial (Cats o ℓ e) using (Initial; IsInitial)

open Initial
open IsInitial
open Functor

-- Unlike for ⊤ being Terminal, Agda can't deduce these, need to be explicit
Zero-⊥ : Initial
Zero-⊥ .⊥ = Zero
Zero-⊥ .⊥-is-initial .! .F₀ ()
Zero-⊥ .⊥-is-initial .!-unique f = niHelper record
  { η = λ()
  ; η⁻¹ = λ()
  ; commute = λ{ {()} }
  ; iso = λ()
  }
