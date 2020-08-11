{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Monoidal.Core using (Monoidal)

module Categories.Category.Monoidal.Rigid {o ℓ e} {C : Category o ℓ e} (M : Monoidal C) where

open import Level

open import Categories.Functor.Bifunctor
open import Categories.NaturalTransformation.NaturalIsomorphism

open Category C
open Commutation C

private
  variable
    X : Obj

-- left rigid monoidal category
record LeftRigid : Set (levelOfTerm M) where
  open Monoidal M public

  field
    _⁻¹ : Obj → Obj
    η   : ∀ {X} → unit ⇒ X ⊗₀ X ⁻¹
    ε   : ∀ {X} → X ⁻¹ ⊗₀ X  ⇒ unit

    snake₁ : [ X ⇒ X ]⟨
               unitorˡ.to  ⇒⟨ (unit ⊗₀ X) ⟩
               (η ⊗₁ id)  ⇒⟨ (X ⊗₀ X ⁻¹) ⊗₀ X ⟩
               associator.from  ⇒⟨ X ⊗₀ (X ⁻¹ ⊗₀ X) ⟩
               (id ⊗₁ ε) ⇒⟨ X ⊗₀ unit ⟩
               unitorʳ.from
             ≈ id
             ⟩
    snake₂ : [ X ⁻¹ ⇒ X ⁻¹ ]⟨
               unitorʳ.to  ⇒⟨ X ⁻¹ ⊗₀ unit ⟩
               (id ⊗₁ η)  ⇒⟨ X ⁻¹ ⊗₀ (X ⊗₀ X ⁻¹) ⟩
               associator.to  ⇒⟨ (X ⁻¹ ⊗₀ X) ⊗₀ X ⁻¹ ⟩
               (ε ⊗₁ id) ⇒⟨ unit ⊗₀ X ⁻¹ ⟩
               unitorˡ.from
             ≈ id
             ⟩

-- right rigid monoidal category
record RightRigid : Set (levelOfTerm M) where
  open Monoidal M public

  field
    _⁻¹ : Obj → Obj
    η   : ∀ {X} → unit ⇒ X ⁻¹ ⊗₀ X
    ε   : ∀ {X} → X ⊗₀ X ⁻¹  ⇒ unit

    snake₁ : [ X ⇒ X ]⟨
               unitorʳ.to  ⇒⟨ (X ⊗₀ unit) ⟩
               (id ⊗₁ η)  ⇒⟨ X ⊗₀ (X ⁻¹ ⊗₀ X) ⟩
               associator.to ⇒⟨ (X ⊗₀ X ⁻¹) ⊗₀ X ⟩
               (ε ⊗₁ id) ⇒⟨ unit ⊗₀ X ⟩
               unitorˡ.from
             ≈ id
             ⟩
    snake₂ : [ X ⁻¹ ⇒ X ⁻¹ ]⟨
               unitorˡ.to  ⇒⟨ unit ⊗₀ X ⁻¹ ⟩
               (η ⊗₁ id)  ⇒⟨ (X ⁻¹ ⊗₀ X) ⊗₀ X ⁻¹ ⟩
               associator.from  ⇒⟨ X ⁻¹ ⊗₀ (X ⊗₀ X ⁻¹) ⟩
               (id ⊗₁ ε) ⇒⟨ X ⁻¹ ⊗₀ unit ⟩
               unitorʳ.from
             ≈ id
             ⟩
