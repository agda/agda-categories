{-# OPTIONS --without-K --safe #-}

open import Categories.Bicategory using (Bicategory)

-- A Pseudofunctor is a homomorphism of Bicategories
-- Follow Bénabou's definition, which is basically that of a Functor

-- Note that what is in nLab is an "exploded" version of the simpler version below

module Categories.Pseudofunctor {o ℓ e t o′ ℓ′ e′ t′}
                                (C : Bicategory o ℓ e t)
                                (D : Bicategory o′ ℓ′ e′ t′)
                                where

open import Level
open import Data.Product using (_,_)

import Categories.Bicategory.Extras as BicategoryExtras
open import Categories.Category using (Category; _[_,_]; module Commutation)
open import Categories.Category.Instance.One using (shift)
open import Categories.Category.Product using (_⁂_)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (NaturalIsomorphism; _≃_)

open BicategoryExtras using (module ComHom)
open Category using (Obj)
open NaturalIsomorphism using (F⇒G; F⇐G)

private
  module C = BicategoryExtras C
  module D = BicategoryExtras D

record Pseudofunctor : Set (o ⊔ ℓ ⊔ e ⊔ t ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ t′) where

  field
    P₀ : C.Obj → D.Obj
    P₁ : {x y : C.Obj} → Functor (C.hom x y) (D.hom (P₀ x) (P₀ y))
    -- For maximal generality, shift the levels of One. P preserves id
    P-identity : {A : C.Obj} →  D.id {P₀ A} ∘F shift o′ ℓ′ e′ ≃ P₁ ∘F (C.id {A})
    -- P preserves composition
    P-homomorphism : {x y z : C.Obj} → D.⊚ ∘F (P₁ ⁂ P₁) ≃ P₁ ∘F C.⊚ {x} {y} {z}
    -- P preserves ≃

  module P₁ {x} {y} = Functor (P₁ {x} {y})
  module unitˡ {A} = NaturalTransformation (F⇒G (P-identity {A}))
  module unitʳ {A} = NaturalTransformation (F⇐G (P-identity {A}))
  module Hom {x} {y} {z} = NaturalTransformation (F⇒G (P-homomorphism {x} {y} {z}))

  -- For notational convenience, shorten some functor applications
  private
    F₀   = λ {x y} f → Functor.F₀ (P₁ {x} {y}) f
    F₁   = λ {x y f g} α → Functor.F₁ (P₁ {x} {y}) {f} {g} α
    Pid  = λ {A} → NaturalTransformation.η (F⇒G (P-identity {A})) _
    Phom = λ {x} {y} {z} f,g →
           NaturalTransformation.η (F⇒G (P-homomorphism {x} {y} {z})) f,g

  field
    unitaryˡ : {x y : C.Obj} →
               let open ComHom D in
               {f : Obj (C.hom x y)} →
               [ D.id₁ D.⊚₀ F₀ f     ⇒ F₀ f ]⟨
                 Pid D.⊚₁ D.id₂      ⇒⟨ F₀ C.id₁ D.⊚₀ F₀ f ⟩
                 Phom (C.id₁ , f)    ⇒⟨ F₀ (C.id₁ C.⊚₀ f) ⟩
                 F₁ C.unitorˡ.from
               ≈ D.unitorˡ.from
               ⟩
    unitaryʳ : {x y : C.Obj} →
               let open ComHom D in
               {f : Obj (C.hom x y)} →
               [ F₀ f D.⊚₀ D.id₁     ⇒ F₀ f ]⟨
                 D.id₂ D.⊚₁ Pid      ⇒⟨ F₀ f D.⊚₀ F₀ C.id₁ ⟩
                 Phom (f , C.id₁)    ⇒⟨ F₀ (f C.⊚₀ C.id₁) ⟩
                 F₁ C.unitorʳ.from
               ≈ D.unitorʳ.from
               ⟩

    assoc : {x y z w : C.Obj} →
            let open ComHom D in
            {f : Obj (C.hom x y)} {g : Obj (C.hom y z)} {h : Obj (C.hom z w)} →
            [ (F₀ h D.⊚₀ F₀ g) D.⊚₀ F₀ f    ⇒ F₀ (h C.⊚₀ (g C.⊚₀ f)) ]⟨
              Phom (h , g) D.⊚₁ D.id₂       ⇒⟨ F₀ (h C.⊚₀ g) D.⊚₀ F₀ f ⟩
              Phom (_ , f)                  ⇒⟨ F₀ ((h C.⊚₀ g) C.⊚₀ f) ⟩
              F₁ C.associator.from
            ≈ D.associator.from             ⇒⟨ F₀ h D.⊚₀ (F₀ g D.⊚₀ F₀ f) ⟩
              D.id₂ D.⊚₁ Phom (g , f)       ⇒⟨ F₀ h D.⊚₀ F₀ (g C.⊚₀ f) ⟩
              Phom (h , _)
            ⟩

  -- Useful shorthands

  ₀        = P₀
  module ₁ = P₁
