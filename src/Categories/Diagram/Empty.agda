{-# OPTIONS --without-K --safe #-}

open import Level

open import Categories.Category.Core using (Category)

module Categories.Diagram.Empty {o ℓ e} (C : Category o ℓ e) (o′ ℓ′ e′ : Level) where

open import Categories.Category.Instance.Zero {o′} {ℓ′} {e′} using (Zero)
open import Categories.Functor.Core using (Functor)

open Functor

empty : Functor Zero C
empty .F₀ ()
