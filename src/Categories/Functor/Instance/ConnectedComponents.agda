{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Instance.ConnectedComponents where

open import Level
open import Function using () renaming (_∘′_ to _∙_)
open import Relation.Binary.Construct.Closure.SymmetricTransitive as ST using (Plus⇔; minimal)

open import Categories.Category
open import Categories.Category.Instance.Cats using (Cats)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor hiding (id)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)

-- this is the left adjoint to Disc : Setoids ⇒ Cats
Π₀ : ∀ {o ℓ e} → Functor (Cats o ℓ e) (Setoids o (o ⊔ ℓ))
Π₀ = record
  { F₀ = λ C → ST.setoid (Category._⇒_ C) (Category.id C)
  ; F₁ = λ F → record
    { to = Functor.F₀ F
    ; cong = ST.gmap (Functor.F₀ F) (Functor.F₁ F)
    }
  ; identity = λ {A} → Plus⇔.forth (Category.id A)
  ; homomorphism = λ {_ _ Z F G x} → Plus⇔.forth (Category.id Z)
  ; F-resp-≈ = λ {A} {B} {f} {g} α {a} → Plus⇔.forth (NaturalIsomorphism.⇒.η α a)
  }
