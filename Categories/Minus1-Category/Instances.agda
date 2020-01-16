{-# OPTIONS --without-K --safe #-}

-- The two obvious instances, Zero and One.

module Categories.Minus1-Category.Instances where

open import Level
open import Data.Empty
open import Data.Unit

open import Categories.Minus1-Category
open import Categories.Category using (Category)
open import Categories.Category.Instance.One

private
  variable
    t : Level

-1-Zero : Strict-1-Category t
-1-Zero {t} = record  { Obj = Lift t ⊥ }

-1-One : Strict-1-Category t
-1-One {t} = record { Obj = Lift t ⊤ }
