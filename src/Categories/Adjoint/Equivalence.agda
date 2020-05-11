{-# OPTIONS --without-K --safe #-}

module Categories.Adjoint.Equivalence where

open import Level

open import Categories.Adjoint
open import Categories.Adjoint.TwoSided
open import Categories.Adjoint.TwoSided.Compose
open import Categories.Category.Core using (Category)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.NaturalTransformation.NaturalIsomorphism as ≃ using (_≃_)

open import Relation.Binary using (Setoid; IsEquivalence)

private
  variable
    o ℓ e o′ ℓ′ e′ : Level
    C D E    : Category o ℓ e

record ⊣Equivalence (C : Category o ℓ e) (D : Category o′ ℓ′ e′) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  field
    L    : Functor C D
    R    : Functor D C
    L⊣⊢R : L ⊣⊢ R

  module L    = Functor L
  module R    = Functor R

  open _⊣⊢_ L⊣⊢R public

refl : ⊣Equivalence C C
refl = record
  { L    = idF
  ; R    = idF
  ; L⊣⊢R = id⊣⊢id
  }

sym : ⊣Equivalence C D → ⊣Equivalence D C
sym e = record
  { L    = R
  ; R    = L
  ; L⊣⊢R = op₂
  }
  where open ⊣Equivalence e

trans : ⊣Equivalence C D → ⊣Equivalence D E → ⊣Equivalence C E
trans e e′ = record
  { L    = e′.L ∘F e.L
  ; R    = e.R ∘F e′.R
  ; L⊣⊢R = e.L⊣⊢R ∘⊣⊢ e′.L⊣⊢R
  }
  where module e  = ⊣Equivalence e using (L; R; L⊣⊢R)
        module e′ = ⊣Equivalence e′ using (L; R; L⊣⊢R)

isEquivalence : ∀ {o ℓ e} → IsEquivalence (⊣Equivalence {o} {ℓ} {e})
isEquivalence = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }

setoid : ∀ o ℓ e → Setoid _ _
setoid o ℓ e = record
  { Carrier       = Category o ℓ e
  ; _≈_           = ⊣Equivalence
  ; isEquivalence = isEquivalence
  }
