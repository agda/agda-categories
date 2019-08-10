{-# OPTIONS --without-K --safe #-}

module Categories.Bicategory.Bigroupoid where

open import Level
open import Data.Product using (Σ; _,_)

open import Categories.Adjoint
open import Categories.Category
open import Categories.Category.Product
open import Categories.Category.Groupoid
open import Categories.Bicategory
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Construction.Constant
open import Categories.NaturalTransformation.NaturalIsomorphism

-- https://link.springer.com/article/10.1023/A:1011270417127
record Bigroupoid {o ℓ e t} (C : Bicategory o ℓ e t) : Set (o ⊔ ℓ ⊔ e ⊔ t) where
  open Bicategory C public

  field
    1-groupoid : ∀ A B → Groupoid (hom A B)
    hom[_,_]⁻¹ : ∀ A B → Functor (hom A B) (hom B A)
    cancel     : ∀ A B → ⊚ ∘F (hom[ A , B ]⁻¹ ※ idF) ≃ const id₁
    cancel′    : ∀ A B → ⊚ ∘F (idF ※ hom[ A , B ]⁻¹) ≃ const id₁

  module hom⁻¹ {A B}   = Functor (hom[ A , B ]⁻¹)
  module cancel {A B}  = NaturalIsomorphism (cancel A B)
  module cancel′ {A B} = NaturalIsomorphism (cancel′ A B)

  infix 13 _⁻¹

  _⁻¹ : ∀ {A B} → A ⇒₁ B → B ⇒₁ A
  _⁻¹ = hom⁻¹.F₀

  open hom.Commutation

  field
    pentagon₁ : ∀ {A B} {f : A ⇒₁ B} →
                  [ (f ∘ₕ f ⁻¹) ∘ₕ f ⇒ f ]⟨
                    associator.from      ⇒⟨ f ∘ₕ f ⁻¹ ∘ₕ f ⟩
                    f ▷ cancel.⇒.η f     ⇒⟨ f ∘ₕ id₁ ⟩
                    unitorʳ.from
                  ≈ cancel′.⇒.η f ◁ f    ⇒⟨ id₁ ∘ₕ f ⟩
                    unitorˡ.from
                  ⟩
    pentagon₂ : ∀ {A B} {f : A ⇒₁ B} →
                  [ (f ⁻¹ ∘ₕ f) ∘ₕ f ⁻¹ ⇒ f ⁻¹ ]⟨
                    associator.from            ⇒⟨ f ⁻¹ ∘ₕ f ∘ₕ f ⁻¹ ⟩
                    f ⁻¹ ▷ cancel′.⇒.η f       ⇒⟨ f ⁻¹ ∘ₕ id₁ ⟩
                    unitorʳ.from
                  ≈ cancel.⇒.η f ◁ f ⁻¹        ⇒⟨ id₁ ∘ₕ f ⁻¹ ⟩
                    unitorˡ.from
                  ⟩
