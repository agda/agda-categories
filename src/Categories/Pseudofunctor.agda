{-# OPTIONS --without-K --safe #-}

open import Categories.Bicategory using (Bicategory)

-- A Pseudofunctor is a homomorphism of Bicategories
-- Follow Bénabou's definition, which is basically that of a Functor

-- Note that what is in nLab is an "exploded" version of the simpler version below
module Categories.Pseudofunctor where

open import Level
open import Data.Product using (_,_)

open import Categories.Bicategory.Extras using (module Extras)
import Categories.Category as Category
open Category.Category using (Obj)
open Category using (Category; _[_,_]; module Commutation)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Category.Product using (_⁂_)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; _≃_)
open import Categories.Category.Instance.One using (shift)
open NaturalIsomorphism using (F⇒G; F⇐G)

record Pseudofunctor {o ℓ e t o′ ℓ′ e′ t′  : Level} (C : Bicategory o ℓ e t) (D : Bicategory o′ ℓ′ e′ t′)
    : Set (o ⊔ ℓ ⊔ e ⊔ t ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ t′) where
  private
    module C = Bicategory C using (Obj; hom; id; ⊚; id₁; _⊚₀_)
    module CC = Extras C using (unitorˡ; unitorʳ; associator)
    module D = Bicategory D using (Obj; hom; id; ⊚; id₁; id₂; _⊚₀_; _⊚₁_)
    module DD = Extras D using (unitorˡ; unitorʳ; associator)

  field
    P₀ : C.Obj → D.Obj
    P₁ : {x y : C.Obj} → Functor (C.hom x y) (D.hom (P₀ x) (P₀ y))
    -- For maximal generality, shift the levels of One. P preserves id
    P-identity : {A : C.Obj} →  D.id {P₀ A} ∘F shift o′ ℓ′ e′ ≃ P₁ ∘F (C.id {A})
    -- P preserves composition
    P-homomorphism : {x y z : C.Obj} → D.⊚ ∘F (P₁ ⁂ P₁) ≃ P₁ ∘F C.⊚ {x} {y} {z}
    -- P preserves ≃

  module unitˡ {A} = NaturalTransformation (F⇒G (P-identity {A}))
  module unitʳ {A} = NaturalTransformation (F⇐G (P-identity {A}))
  module Hom {x} {y} {z} = NaturalTransformation (F⇒G (P-homomorphism {x} {y} {z}))

  -- For notational convenience, shorten some functor applications
  private
    F₀ = λ {x y} X → Functor.F₀ (P₁ {x} {y}) X

  field
    unitaryˡ : {x y : C.Obj} →
               let open Commutation (D.hom (P₀ x) (P₀ y)) in
               {f : Obj (C.hom x y)} →
               [ D.id₁ D.⊚₀ (F₀ f)            ⇒ F₀ f ]⟨
                 unitˡ.η _ D.⊚₁ D.id₂         ⇒⟨ F₀ C.id₁ D.⊚₀ F₀ f ⟩
                 Hom.η ( C.id₁ , f)           ⇒⟨ F₀ (C.id₁ C.⊚₀ f) ⟩
                 Functor.F₁ P₁ CC.unitorˡ.from
               ≈ DD.unitorˡ.from
               ⟩
    unitaryʳ : {x y : C.Obj} →
               let open Commutation (D.hom (P₀ x) (P₀ y)) in
               {f : Obj (C.hom x y)} →
               [ (F₀ f) D.⊚₀ D.id₁             ⇒ F₀ f ]⟨
                 D.id₂ D.⊚₁ unitˡ.η _          ⇒⟨ F₀ f D.⊚₀ F₀ C.id₁ ⟩
                 Hom.η ( f , C.id₁ )            ⇒⟨ F₀ (f C.⊚₀ C.id₁) ⟩
                 Functor.F₁ P₁ (CC.unitorʳ.from)
               ≈ DD.unitorʳ.from
               ⟩

    assoc : {x y z w : C.Obj} →
            let open Commutation (D.hom (P₀ x) (P₀ w)) in
            {f : Obj (C.hom x y)} {g : Obj (C.hom y z)} {h : Obj (C.hom z w)} →
            [ (F₀ h D.⊚₀ F₀ g) D.⊚₀ F₀ f     ⇒ F₀ (h C.⊚₀ (g C.⊚₀ f)) ]⟨
              Hom.η (h , g) D.⊚₁ D.id₂       ⇒⟨ F₀ (h C.⊚₀ g) D.⊚₀ F₀ f ⟩
              Hom.η (_ , f)                   ⇒⟨ F₀ ((h C.⊚₀ g) C.⊚₀ f) ⟩
              Functor.F₁ P₁ CC.associator.from
            ≈ DD.associator.from              ⇒⟨ F₀ h D.⊚₀ (F₀ g D.⊚₀ F₀ f) ⟩
              D.id₂ D.⊚₁ Hom.η (g , f)       ⇒⟨ F₀ h D.⊚₀ F₀ (g C.⊚₀ f) ⟩
              Hom.η (h , _)
            ⟩
