{-# OPTIONS --without-K --safe #-}

open import Level
open import Data.Product using (_,_)

open import Categories.Category using (Category; module Definitions)

open import Categories.Category.Construction.TwistedArrow
open import Categories.Category.Product renaming (Product to _×ᶜ_)
open import Categories.Category.Construction.Functors
open import Categories.Functor
open import Categories.Functor.Bifunctor
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_; _ⓘʳ_)
open import Categories.Functor.Limits using (Continuous)


-- Definition of the "Twisted" Functor between certain Functor Categories
module Categories.Functor.Instance.Twisted {o ℓ e o′ ℓ′ e′} (C : Category o ℓ e) (D : Category o′ ℓ′ e′)where

private
  module C = Category C
  module D = Category D

open Morphism
open Morphism⇒
-- precomposition with the forgetful functor
Twist : Functor (C.op ×ᶜ C) D → Functor (TwistedArrow C) D
Twist F = F ∘F Forget C

Twist′ : Functor (C.op ×ᶜ C) D → Functor (Category.op (TwistedArrow C.op)) D
Twist′ F = F ∘F (Functor.op (Forget C.op))

-- precomposition is functorial
Twisted : Functor (Functors (C.op ×ᶜ C) D) (Functors (TwistedArrow C) D)
Twisted = appʳ product (Forget C)

Twistⁿⁱ : ∀ {F G : Functor (C.op ×ᶜ C) D } → (F ≃ G) → Twist F ≃ Twist G
Twistⁿⁱ α = α ⓘʳ Forget C
