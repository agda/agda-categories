{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Functor.Hom.Properties {o ℓ e} (C : Category o ℓ e) where

open import Categories.Functor.Hom.Properties.Covariant C public
open import Categories.Functor.Hom.Properties.Contra C public
