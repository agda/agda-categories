{-# OPTIONS --without-K --safe #-}

module Categories.Category.Construction.Properties.Presheaves where

open import Categories.Category.Construction.Properties.Presheaves.Cartesian
  using (module IsCartesian)
  public

open import Categories.Category.Construction.Properties.Presheaves.CartesianClosed
  using (module IsCCC)
  public
