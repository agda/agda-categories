{-# OPTIONS --without-K --safe #-}

-- Definition of Monoidal Category

-- Big design decision that differs from the previous version:
-- Do not go through "Functor.Power" to encode variables and work
-- at the level of NaturalIsomorphisms, instead work at the object/morphism
-- level, via the more direct _⊗₀_ _⊗₁_ _⊗- -⊗_.
-- The original design needed quite a few contortions to get things working,
-- but these are simply not needed when working directly with the morphisms.
--
-- Smaller design decision: export some items with long names
-- (unitorˡ, unitorʳ and associator), but internally work with the more classical
-- short greek names (λ, ρ and α respectively).

module Categories.Category.Monoidal where

open import Categories.Category.Monoidal.Core public
open import Categories.Category.Monoidal.Structure public
