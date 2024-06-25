{-# OPTIONS --without-K --safe #-}

open import Level

open import Categories.Category.Core using (Category)

module Categories.Diagram.Empty {o ℓ e} (C : Category o ℓ e) (o′ ℓ′ e′ : Level) where

open import Categories.Category.Construction.Empty {o′} {ℓ′} {e′} using (Empty)
open import Categories.Functor.Core using (Functor)

open Functor

empty : Functor Empty C
empty .F₀ ()
