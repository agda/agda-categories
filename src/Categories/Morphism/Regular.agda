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

open import Categories.Morphism 𝒞
open import Categories.Diagram.Equalizer 𝒞
open import Categories.Diagram.Coequalizer 𝒞

open Category 𝒞

private
  variable
    A B : Obj

record RegularMono (f : A ⇒ B) : Set (o ⊔ ℓ ⊔ e) where
  field
    { C } : Obj
    g : B ⇒ C
    h : B ⇒ C
    equalizer : IsEqualizer f h g

record RegularEpi (f : A ⇒ B) : Set (o ⊔ ℓ ⊔ e) where
  field
    { C } : Obj
    h : C ⇒ A
    g : C ⇒ A
    coequalizer : IsCoequalizer h g f

RegularMono⇒Mono : ∀ {f : A ⇒ B} → RegularMono f → Mono f
RegularMono⇒Mono regular = IsEqualizer⇒Mono equalizer
  where
    open RegularMono regular

RegularEpi⇒Epi : ∀ {f : A ⇒ B} → RegularEpi f → Epi f
RegularEpi⇒Epi regular = IsCoequalizer⇒Epi coequalizer
  where
    open RegularEpi regular

