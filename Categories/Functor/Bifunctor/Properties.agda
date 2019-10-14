{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Bifunctor.Properties where

open import Level
open import Data.Product using (Σ; _,_)

open import Categories.Category
open import Categories.Functor
open import Categories.Functor.Bifunctor
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level
    C D E : Category o ℓ e

module _ (F : Bifunctor C D E) where
  private
    module C = Category C
    module D = Category D
    module E = Category E

    variable
      A B : C.Obj
      X Y : D.Obj
      f h j : A C.⇒ B
      g i k : X D.⇒ Y

  open E
  open HomReasoning
  open Functor F

  [_]-commute : F₁ (C.id , g) ∘ F₁ (f , D.id) ≈ F₁ (f , D.id) ∘ F₁ (C.id , g)
  [_]-commute {g = g} {f = f} = begin
    F₁ (C.id , g) ∘ F₁ (f , D.id) ≈˘⟨ homomorphism ⟩
    F₁ (C.id C.∘ f , g D.∘ D.id)  ≈⟨ F-resp-≈ (MR.id-comm-sym C , MR.id-comm D) ⟩
    F₁ (f C.∘ C.id , D.id D.∘ g)  ≈⟨ homomorphism ⟩
    F₁ (f , D.id) ∘ F₁ (C.id , g) ∎

  [_]-decompose₁ : F₁ (f , g) ≈ F₁ (f , D.id) ∘ F₁ (C.id , g)
  [_]-decompose₁ {f = f} {g = g} = begin
    F₁ (f , g)                    ≈˘⟨ F-resp-≈ (C.identityʳ , D.identityˡ) ⟩
    F₁ (f C.∘ C.id , D.id D.∘ g)  ≈⟨ homomorphism ⟩
    F₁ (f , D.id) ∘ F₁ (C.id , g) ∎

  [_]-decompose₂ : F₁ (f , g) ≈ F₁ (C.id , g) ∘ F₁ (f , D.id)
  [_]-decompose₂ {f = f} {g = g} = begin
    F₁ (f , g)                    ≈˘⟨ F-resp-≈ (C.identityˡ , D.identityʳ) ⟩
    F₁ (C.id C.∘ f , g D.∘ D.id)  ≈⟨ homomorphism ⟩
    F₁ (C.id , g) ∘ F₁ (f , D.id) ∎

  [_]-merge : f C.∘ h C.≈ j → g D.∘ i D.≈ k →  F₁ (f , g) ∘ F₁ (h , i) ≈ F₁ (j , k)
  [_]-merge {f = f} {h = h} {j = j} {g = g} {i = i} {k = k} eq eq′ = begin
    F₁ (f , g) ∘ F₁ (h , i) ≈˘⟨ homomorphism ⟩
    F₁ (f C.∘ h , g D.∘ i)  ≈⟨ F-resp-≈ (eq , eq′) ⟩
    F₁ (j , k)              ∎
