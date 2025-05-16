{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Object.Coproduct.Indexed.Properties {o ℓ e} (C : Category o ℓ e) where

open import Function.Base using () renaming (_∘_ to _∙_)
open import Level

open import Categories.Object.Coproduct.Indexed C using (IndexedCoproductOf; AllCoproductsOf)

lowerAllCoproductsOf : ∀ {i} j → AllCoproductsOf (i ⊔ j) → AllCoproductsOf i
lowerAllCoproductsOf j coprod P = record
  { X = X
  ; ι = ι ∙ lift
  ; [_] = λ f → [ f ∙ lower ]
  ; commute = commute
  ; unique = λ eq → unique eq
  }
  where open IndexedCoproductOf (coprod {Lift j _} (P ∙ lower))
