{-# OPTIONS --without-K --safe #-}
open import Categories.Category using (Category; module Definitions)

-- Definition of the "Twisted" Functor between certain Functor Categories
module Categories.Functor.Instance.Twisted {o ℓ e o′ ℓ′ e′} (𝒞 : Category o ℓ e) (𝒟 : Category o′ ℓ′ e′) where

import Categories.Category.Construction.TwistedArrow as TW
open import Categories.Category.Product
open import Categories.Category.Construction.Functors
open import Categories.Functor
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)

open import Data.Product using (_,_)

private
  module C = Category 𝒞

Twisted : Functor (Functors (Product C.op 𝒞) 𝒟) (Functors (TW.TwistedArrow 𝒞) 𝒟)
Twisted = record
  { F₀ = Func
  ; F₁ = Nat
  ; identity = D.Equiv.refl
  ; homomorphism = D.Equiv.refl
  ; F-resp-≈ = λ f≈g → f≈g
  }
  where
  open TW.Morphism
  open TW.Morphism⇒
  open Functor
  module CC = Category (Product C.op 𝒞)
  module D = Category 𝒟
  Func : Functor (Product C.op 𝒞) 𝒟 → Functor (TW.TwistedArrow 𝒞) 𝒟
  Func F = record
    { F₀ = λ x → F₀ F (dom x , cod x)
    ; F₁ = λ f → F₁ F (dom⇐ f , cod⇒ f)
    ; identity = identity F
    ; homomorphism = homomorphism F
    ; F-resp-≈ = F-resp-≈ F
    }
  Nat : {F G : Functor (Product C.op 𝒞) 𝒟} → NaturalTransformation F G → NaturalTransformation (Func F) (Func G)
  Nat nt = ntHelper record
    { η = λ x → η nt (dom x , cod x)
    ; commute = λ f → commute nt (dom⇐ f , cod⇒ f)
    }
    where
    open NaturalTransformation
