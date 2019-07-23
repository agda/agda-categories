{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Monoidal where

open import Level
open import Data.Product using (Σ; _,_)

open import Categories.Category
open import Categories.Category.Product
open import Categories.Category.Monoidal

open import Categories.Functor hiding (id)
open import Categories.NaturalTransformation hiding (id)

private
  variable
    o ℓ e : Level
    C D : Category o ℓ e

module _  (MC : Monoidal C) (MD : Monoidal D) where
  private
    module C  = Category C
    module D  = Category D
    module MC = Monoidal MC
    module MD = Monoidal MD

  record MonoidalFunctor : Set (levelOfTerm MC ⊔ levelOfTerm MD) where
    field
      F : Functor C D

    open Functor F public

    field
      ε      : D [ MD.unit , F₀ MC.unit ]
      ⊗-homo : NaturalTransformation (MD.⊗ ∘F (F ⁂ F)) (F ∘F MC.⊗)

    module ⊗-homo = NaturalTransformation ⊗-homo

    -- coherence condition
    open D
    open MD
    open Commutation

    field
      associativity : ∀ {X Y Z} →
                      [ (F₀ X ⊗₀ F₀ Y) ⊗₀ F₀ Z ⇒ F₀ (X MC.⊗₀ Y MC.⊗₀ Z) ]⟨
                        ⊗-homo.η (X , Y) ⊗₁ id                          ⇒⟨ F₀ (X MC.⊗₀ Y) ⊗₀ F₀ Z ⟩
                        ⊗-homo.η (X MC.⊗₀ Y , Z)                        ⇒⟨ F₀ ((X MC.⊗₀ Y) MC.⊗₀ Z) ⟩
                        F₁ MC.associator.from
                      ≈ associator.from                                 ⇒⟨ F₀ X ⊗₀ F₀ Y ⊗₀ F₀ Z ⟩
                        id ⊗₁ ⊗-homo.η (Y , Z)                          ⇒⟨ F₀ X ⊗₀ F₀ (Y MC.⊗₀ Z) ⟩
                        ⊗-homo.η (X , Y MC.⊗₀ Z)
                      ⟩
      unitaryˡ      : ∀ {X} →
                      [ unit ⊗₀ F₀ X ⇒ F₀ X    ]⟨
                        ε ⊗₁ id                ⇒⟨ F₀ MC.unit ⊗₀ F₀ X ⟩
                        ⊗-homo.η (MC.unit , X) ⇒⟨ F₀ (MC.unit MC.⊗₀ X) ⟩
                        F₁ MC.unitorˡ.from
                      ≈ unitorˡ.from
                      ⟩
      unitaryʳ      : ∀ {X} →
                      [ F₀ X ⊗₀ unit ⇒ F₀ X    ]⟨
                        id ⊗₁ ε                ⇒⟨ F₀ X ⊗₀ F₀ MC.unit ⟩
                        ⊗-homo.η (X , MC.unit) ⇒⟨ F₀ (X MC.⊗₀ MC.unit) ⟩
                        F₁ MC.unitorʳ.from
                      ≈ unitorʳ.from
                      ⟩
