{-# OPTIONS --without-K --safe #-}
module Categories.NaturalTransformation where

open import Categories.Category using (Category)
open import Categories.Functor renaming (id to idF)
open import Categories.NaturalTransformation.Core public
