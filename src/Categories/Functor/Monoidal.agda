{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Monoidal where

open import Level
open import Data.Product using (Σ; _,_)

open import Categories.Category
open import Categories.Category.Product
open import Categories.Category.Monoidal

open import Categories.Functor hiding (id)
open import Categories.Functor.Properties using ([_]-resp-≅)
open import Categories.NaturalTransformation hiding (id)
open import Categories.NaturalTransformation.NaturalIsomorphism

import Categories.Category.Construction.Core as Core
import Categories.Category.Monoidal.Utilities as ⊗-Utilities
import Categories.Morphism as Mor

private
  variable
    o o′ ℓ ℓ′ e e′ : Level

module _  (C : MonoidalCategory o ℓ e) (D : MonoidalCategory o′ ℓ′ e′) where
  private
    module C = MonoidalCategory C
    module D = MonoidalCategory D
    open Mor D.U

  -- lax monoidal functor
  record IsMonoidalFunctor (F : Functor C.U D.U) : Set (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) where
    open Functor F

    field
      ε      : D.U [ D.unit , F₀ C.unit ]
      ⊗-homo : NaturalTransformation (D.⊗ ∘F (F ⁂ F)) (F ∘F C.⊗)

    module ⊗-homo = NaturalTransformation ⊗-homo

    -- coherence condition
    open D
    open Commutation D.U

    field
      associativity : ∀ {X Y Z} →
                      [ (F₀ X ⊗₀ F₀ Y) ⊗₀ F₀ Z ⇒ F₀ (X C.⊗₀ Y C.⊗₀ Z) ]⟨
                        ⊗-homo.η (X , Y) ⊗₁ id                        ⇒⟨ F₀ (X C.⊗₀ Y) ⊗₀ F₀ Z ⟩
                        ⊗-homo.η (X C.⊗₀ Y , Z)                       ⇒⟨ F₀ ((X C.⊗₀ Y) C.⊗₀ Z) ⟩
                        F₁ C.associator.from
                      ≈ associator.from                               ⇒⟨ F₀ X ⊗₀ F₀ Y ⊗₀ F₀ Z ⟩
                        id ⊗₁ ⊗-homo.η (Y , Z)                        ⇒⟨ F₀ X ⊗₀ F₀ (Y C.⊗₀ Z) ⟩
                        ⊗-homo.η (X , Y C.⊗₀ Z)
                      ⟩
      unitaryˡ      : ∀ {X} →
                      [ unit ⊗₀ F₀ X ⇒ F₀ X   ]⟨
                        ε ⊗₁ id               ⇒⟨ F₀ C.unit ⊗₀ F₀ X ⟩
                        ⊗-homo.η (C.unit , X) ⇒⟨ F₀ (C.unit C.⊗₀ X) ⟩
                        F₁ C.unitorˡ.from
                      ≈ unitorˡ.from
                      ⟩
      unitaryʳ      : ∀ {X} →
                      [ F₀ X ⊗₀ unit ⇒ F₀ X   ]⟨
                        id ⊗₁ ε               ⇒⟨ F₀ X ⊗₀ F₀ C.unit ⟩
                        ⊗-homo.η (X , C.unit) ⇒⟨ F₀ (X C.⊗₀ C.unit) ⟩
                        F₁ C.unitorʳ.from
                      ≈ unitorʳ.from
                      ⟩

  record MonoidalFunctor : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
    field
      F          : Functor C.U D.U
      isMonoidal : IsMonoidalFunctor F

    open Functor F public
    open IsMonoidalFunctor isMonoidal public

module _  (C : MonoidalCategory o ℓ e) (D : MonoidalCategory o′ ℓ′ e′) where
  private
    module C = MonoidalCategory C
    module D = MonoidalCategory D
    open Mor D.U

  -- strong monoidal functor
  record IsStrongMonoidalFunctor (F : Functor C.U D.U) : Set (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) where
    open Functor F

    field
      ε      : D.unit ≅ F₀ C.unit
      ⊗-homo : D.⊗ ∘F (F ⁂ F) ≃ F ∘F C.⊗

    module ε      = _≅_ ε
    module ⊗-homo = NaturalIsomorphism ⊗-homo

    -- coherence condition
    open D
    open Commutation D.U

    field
      associativity : ∀ {X Y Z} →
                      [ (F₀ X ⊗₀ F₀ Y) ⊗₀ F₀ Z ⇒ F₀ (X C.⊗₀ Y C.⊗₀ Z) ]⟨
                        ⊗-homo.⇒.η (X , Y) ⊗₁ id                        ⇒⟨ F₀ (X C.⊗₀ Y) ⊗₀ F₀ Z ⟩
                        ⊗-homo.⇒.η (X C.⊗₀ Y , Z)                      ⇒⟨ F₀ ((X C.⊗₀ Y) C.⊗₀ Z) ⟩
                        F₁ C.associator.from
                      ≈ associator.from                                 ⇒⟨ F₀ X ⊗₀ F₀ Y ⊗₀ F₀ Z ⟩
                        id ⊗₁ ⊗-homo.⇒.η (Y , Z)                        ⇒⟨ F₀ X ⊗₀ F₀ (Y C.⊗₀ Z) ⟩
                        ⊗-homo.⇒.η (X , Y C.⊗₀ Z)
                      ⟩
      unitaryˡ      : ∀ {X} →
                      [ unit ⊗₀ F₀ X ⇒ F₀ X      ]⟨
                        ε.from ⊗₁ id             ⇒⟨ F₀ C.unit ⊗₀ F₀ X ⟩
                        ⊗-homo.⇒.η (C.unit , X) ⇒⟨ F₀ (C.unit C.⊗₀ X) ⟩
                        F₁ C.unitorˡ.from
                      ≈ unitorˡ.from
                      ⟩
      unitaryʳ      : ∀ {X} →
                      [ F₀ X ⊗₀ unit ⇒ F₀ X      ]⟨
                        id ⊗₁ ε.from             ⇒⟨ F₀ X ⊗₀ F₀ C.unit ⟩
                        ⊗-homo.⇒.η (X , C.unit) ⇒⟨ F₀ (X C.⊗₀ C.unit) ⟩
                        F₁ C.unitorʳ.from
                      ≈ unitorʳ.from
                      ⟩

    isLaxMonoidal : IsMonoidalFunctor C D F
    isLaxMonoidal = record
      { ε             = ε.from
      ; ⊗-homo        = ⊗-homo.F⇒G
      ; associativity = associativity
      ; unitaryˡ      = unitaryˡ
      ; unitaryʳ      = unitaryʳ
      }

    private

      module F = Functor F

      φ : {X Y : C.Obj} → F₀ X ⊗₀ F₀ Y ≅ F₀ (X C.⊗₀ Y)
      φ = ⊗-homo.FX≅GX

      Fα : {X Y Z : C.Obj} → F₀ ((X C.⊗₀ Y) C.⊗₀ Z) ≅ F₀ (X C.⊗₀ (Y C.⊗₀ Z))
      Fα = [ F ]-resp-≅ C.associator

      Fλ : {X : C.Obj} → F₀ (C.unit C.⊗₀ X) ≅ F₀ X
      Fλ = [ F ]-resp-≅ C.unitorˡ

      Fρ : {X : C.Obj} → F₀ (X C.⊗₀ C.unit) ≅ F₀ X
      Fρ = [ F ]-resp-≅ C.unitorʳ

      α : {A B C : Obj} → (A ⊗₀ B) ⊗₀ C ≅ A ⊗₀ (B ⊗₀ C)
      α = D.associator

      λ- : {A : Obj} → unit ⊗₀ A ≅ A
      λ- = D.unitorˡ

      ρ : {A : Obj} → A ⊗₀ unit ≅ A
      ρ = D.unitorʳ

    open ⊗-Utilities monoidal using (_⊗ᵢ_)
    open Core.Shorthands U using (⌞_⌟; to-≈; _∘ᵢ_; idᵢ; _≈ᵢ_)

    associativityᵢ : {X Y Z : C.Obj} → Fα {X} {Y} {Z} ∘ᵢ φ ∘ᵢ φ ⊗ᵢ idᵢ ≈ᵢ φ ∘ᵢ idᵢ ⊗ᵢ φ ∘ᵢ α
    associativityᵢ = ⌞ associativity ⌟

    unitaryˡᵢ : {X : C.Obj} → Fλ {X} ∘ᵢ φ ∘ᵢ ε ⊗ᵢ idᵢ ≈ᵢ λ-
    unitaryˡᵢ = ⌞ unitaryˡ ⌟

    unitaryʳᵢ : {X : C.Obj} → Fρ {X} ∘ᵢ φ ∘ᵢ idᵢ ⊗ᵢ ε ≈ᵢ ρ
    unitaryʳᵢ = ⌞ unitaryʳ ⌟

    isOplaxMonoidal : IsMonoidalFunctor C.op D.op F.op
    isOplaxMonoidal = record
      { ε             = ε.to
      ; ⊗-homo        = ⊗-homo.⇐.op
      ; associativity = to-≈ associativityᵢ
      ; unitaryˡ      = to-≈ unitaryˡᵢ
      ; unitaryʳ      = to-≈ unitaryʳᵢ
      }

  record StrongMonoidalFunctor : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
    field
      F : Functor C.U D.U
      isStrongMonoidal : IsStrongMonoidalFunctor F

    open Functor F public
    open IsStrongMonoidalFunctor isStrongMonoidal public

    monoidalFunctor : MonoidalFunctor C D
    monoidalFunctor = record { F = F ; isMonoidal = isLaxMonoidal }
