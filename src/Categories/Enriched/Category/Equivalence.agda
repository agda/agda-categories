{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using () renaming (Category to Setoid-Category)
open import Categories.Category.Monoidal.Core using (Monoidal)

-- Strong equivalences of enriched categories.

module Categories.Enriched.Category.Equivalence
  {o ℓ e} {V : Setoid-Category o ℓ e} (M : Monoidal V) where

open import Level using (_⊔_)

open import Categories.Enriched.Category M using (Category)
open import Categories.Enriched.Functor M using (Functor; _∘F_)
  renaming (id to idF)
open import Categories.Enriched.NaturalTransformation.NaturalIsomorphism M
  using (NaturalIsomorphism)

record WeakInverse {a b} {C : Category a} {D : Category b}
  (F : Functor C D) (G : Functor D C) : Set (ℓ ⊔ e ⊔ a ⊔ b) where
  field
    F∘G≈id : NaturalIsomorphism (F ∘F G) idF
    G∘F≈id : NaturalIsomorphism (G ∘F F) idF

  module F∘G≈id = NaturalIsomorphism F∘G≈id
  module G∘F≈id = NaturalIsomorphism G∘F≈id

record StrongEquivalence {a b} (C : Category a) (D : Category b) : Set (ℓ ⊔ e ⊔ a ⊔ b) where
  field
    F            : Functor C D
    G            : Functor D C
    weak-inverse : WeakInverse F G

  open WeakInverse weak-inverse public
