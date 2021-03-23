{-# OPTIONS --without-K --safe #-}

{-
  Properties regarding Morphisms of a category:
  - Regular Monomorphism
  - Regular Epimorphism

  https://ncatlab.org/nlab/show/regular+epimorphism

  These are defined here rather than in Morphism, as this
  might cause import cycles (and make the dependency graph
  very odd).
-}
open import Categories.Category.Core

module Categories.Morphism.Regular {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level
open import Data.Product using (Σ; _×_; _,_)

open import Categories.Diagram.Equalizer 𝒞
open import Categories.Diagram.Coequalizer 𝒞

open Category 𝒞

private
  variable
    A B : Obj

RegularMono : (f : A ⇒ B) → Set (o ⊔ ℓ ⊔ e)
RegularMono {B = B} f = Σ Obj (λ C → Σ (B ⇒ C × B ⇒ C) (λ { (h , g ) → IsEqualizer f h g }))

RegularEpi : (f : A ⇒ B) → Set (o ⊔ ℓ ⊔ e)
RegularEpi {A = A} f = Σ Obj (λ C → Σ (C ⇒ A × C ⇒ A) (λ { (h , g) → IsCoequalizer h g f}))
