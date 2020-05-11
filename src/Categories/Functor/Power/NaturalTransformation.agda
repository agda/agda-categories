{-# OPTIONS --without-K --safe #-}
open import Level
open import Categories.Category

module Categories.Functor.Power.NaturalTransformation {o ℓ e : Level} (C : Category o ℓ e) where

open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin; inject+; raise)
open import Data.Sum.Base using (_⊎_; [_,_]′; inj₁; inj₂)
open import Function.Base using () renaming (_∘_ to _∙_)
open import Data.Product using (_,_)

import Categories.Functor.Power as Power
module Pow = Power C
open Pow
open import Categories.Functor.Bifunctor using (Bifunctor)

-- open import Categories.Functor.Bifunctor.NaturalTransformation renaming (id to idⁿ; _≡_ to _≡ⁿ_)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper; _∘ˡ_)
open import Categories.Category.Product using (_※ⁿ_)
open import Categories.Functor using (Functor; module Functor)

flattenPⁿ : {D : Category o ℓ e} {m n : ℕ} {F G : Powerfunctor′ D (Fin m ⊎ Fin n)} (η : NaturalTransformation F G) →
            NaturalTransformation (flattenP F) (flattenP G)
flattenPⁿ {m = m} {n} η = record
  { η           = λ Xs → η.η (Xs ∙ pack)
  ; commute     = λ fs → η.commute (fs ∙ pack)
  ; sym-commute = λ fs → η.sym-commute (fs ∙ pack)
  }
  where
  private module η = NaturalTransformation η
  pack = [ inject+ n , raise m ]′

reduceN′ : ∀ {i j : Level} {I : Set i} {J : Set j}  {F F′ : Powerendo′ I} {G G′ : Powerendo′ J}
  (H : Bifunctor C C C)
  (φ : NaturalTransformation F F′)  (γ : NaturalTransformation G G′) → NaturalTransformation (reduce′ H F G) (reduce′ H F′ G′)
reduceN′ {I = I} {J} {F} {F′} {G} {G′} H φ γ = ntHelper record
  { η = my-η
  ; commute = λ {Xs Ys} → my-commute Xs Ys
  }
  where
  module C = Category C
  module F = Functor F
  module F′ = Functor F′
  module G = Functor G
  module G′ = Functor G′
  module φ = NaturalTransformation φ
  module γ = NaturalTransformation γ
  module H = Functor H
  module L = Functor (reduce′ H F G)
  module R = Functor (reduce′ H F′ G′)
  open Definitions C
  my-η : ∀ Xs → C [ L.F₀ Xs , R.F₀ Xs ]
  my-η Xs = H.F₁ ((φ.η (Xs ∙ inj₁)) , (γ.η (Xs ∙ inj₂)))
  my-commute : ∀ Xs Ys fs → CommutativeSquare (L.F₁ fs) (my-η Xs) (my-η Ys) (R.F₁ fs)
  my-commute Xs Ys fs = begin
      my-η Ys ∘ L.F₁ fs                             ≈˘⟨ H.homomorphism ⟩
      H.F₁ ((φ.η _ ∘ F.F₁ _) , (γ.η _ ∘ G.F₁ _))    ≈⟨ H.F-resp-≈ ((φ.commute _) , (γ.commute _)) ⟩
      H.F₁ ((F′.F₁ _ ∘ φ.η _) , (G′.F₁ _ ∘ γ.η _))  ≈⟨ H.homomorphism ⟩
      R.F₁ fs ∘ my-η Xs
    ∎
    where
    open C using (_∘_)
    open C.HomReasoning

-- Giving the implicits below is not necessary, but makes typechecking faster
reduceN : {m n : ℕ} {F F′ : Powerendo m} {G G′ : Powerendo n}
  (H : Bifunctor C C C)  (φ : NaturalTransformation F F′) (γ : NaturalTransformation G G′) →
  NaturalTransformation (reduce H F G) (reduce H F′ G′)
reduceN  {F = f} {f′} {g} {g′} H φ γ = flattenPⁿ  {F = reduce′ H f g} {G = reduce′ H f′ g′} (reduceN′ H φ γ)

overlapN : {n : ℕ} {F F′ : Powerendo n} {G G′ : Powerendo n}
           (H : Bifunctor C C C) (φ : NaturalTransformation F F′) (γ : NaturalTransformation G G′) →
           NaturalTransformation (overlaps H F G) (overlaps H F′ G′)
overlapN H φ γ = H ∘ˡ (φ ※ⁿ γ)
