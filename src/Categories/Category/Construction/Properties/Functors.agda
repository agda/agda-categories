{-# OPTIONS --without-K --safe #-}

module Categories.Category.Construction.Properties.Functors where

open import Categories.Category.Complete.Properties
  using ( Functors-Complete
        ; evalF-Continuous)
  public
open import Categories.Category.Cocomplete.Properties
  using (Functors-Cocomplete)
  public
