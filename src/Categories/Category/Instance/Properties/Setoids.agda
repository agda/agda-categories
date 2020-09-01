{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Properties.Setoids where

open import Categories.Category.Instance.Properties.Setoids.Complete
  using (Setoids-Complete)
  public

open import Categories.Category.Instance.Properties.Setoids.Cocomplete
  using (Setoids-Cocomplete)
  public

open import Categories.Category.Instance.Properties.Setoids.LCCC
  using (Setoids-LCCC)
  public

open import Categories.Category.Instance.Properties.Setoids.CCC
  using (Setoids-CCC)
  public
