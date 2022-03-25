{-# OPTIONS --without-K --safe #-}

module Categories.Bicategory.Bigroupoid where

open import Level
open import Function using (_$_)
open import Data.Product using (Σ; _,_)

open import Categories.Adjoint.TwoSided using (_⊣⊢_)
open import Categories.Category
open import Categories.Category.Equivalence using (WeakInverse)
import Categories.Category.Equivalence.Properties as EP
open import Categories.Category.Product
open import Categories.Category.Groupoid using (IsGroupoid)
open import Categories.Bicategory
import Categories.Bicategory.Extras as BicategoryExtras
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Properties
open import Categories.Functor.Bifunctor.Properties
open import Categories.Functor.Construction.Constant
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_; NaturalIsomorphism)

import Categories.Morphism as Mor
import Categories.Morphism.Properties as MP
import Categories.Morphism.Reasoning as MR

-- https://link.springer.com/article/10.1023/A:1011270417127
record IsBigroupoid {o ℓ e t} (C : Bicategory o ℓ e t) : Set (o ⊔ ℓ ⊔ e ⊔ t) where
  open BicategoryExtras C
  open Shorthands

  field
    hom-isGroupoid : ∀ A B → IsGroupoid (hom A B)
    hom[_,_]⁻¹     : ∀ A B → Functor (hom A B) (hom B A)
    cancel         : ∀ A B → ⊚ ∘F (hom[ A , B ]⁻¹ ※ idF) ≃ const id₁
    cancel′        : ∀ A B → ⊚ ∘F (idF ※ hom[ A , B ]⁻¹) ≃ const id₁

  module hom⁻¹ {A B}   = Functor (hom[ A , B ]⁻¹)
  module cancel {A B}  = NaturalIsomorphism (cancel A B)
  module cancel′ {A B} = NaturalIsomorphism (cancel′ A B)

  infix 13 _⁻¹ _⁻¹′

  _⁻¹ : ∀ {A B} → A ⇒₁ B → B ⇒₁ A
  _⁻¹ = hom⁻¹.F₀

  _⁻¹′ : ∀ {A B} {f g : A ⇒₁ B} → f ⇒₂ g → f ⁻¹ ⇒₂ g ⁻¹
  _⁻¹′ = hom⁻¹.F₁

  field
    pentagon₁ : ∀ {A B} {f : A ⇒₁ B} →
                  let open Commutation (hom A B) in
                  [ (f ∘₁ f ⁻¹) ∘₁ f ⇒ f ]⟨
                    α⇒                  ⇒⟨ f ∘₁ f ⁻¹ ∘₁ f ⟩
                    f ▷ cancel.⇒.η f    ⇒⟨ f ∘₁ id₁ ⟩
                    ρ⇒
                  ≈ cancel′.⇒.η f ◁ f   ⇒⟨ id₁ ∘₁ f ⟩
                    λ⇒
                  ⟩
    pentagon₂ : ∀ {A B} {f : A ⇒₁ B} →
                  let open Commutation (hom B A) in
                  [ (f ⁻¹ ∘₁ f) ∘₁ f ⁻¹ ⇒ f ⁻¹ ]⟨
                    α⇒                     ⇒⟨ f ⁻¹ ∘₁ f ∘₁ f ⁻¹ ⟩
                    f ⁻¹ ▷ cancel′.⇒.η f   ⇒⟨ f ⁻¹ ∘₁ id₁ ⟩
                    ρ⇒
                  ≈ cancel.⇒.η f ◁ f ⁻¹    ⇒⟨ id₁ ∘₁ f ⁻¹ ⟩
                    λ⇒
                  ⟩

  private
    variable
      A B : Obj
      f g : A ⇒₁ B
      α β : f ⇒₂ g

    open hom.HomReasoning
    open hom.Equiv
    module MR′ {A B} where
      open MR (hom A B) public
      open Mor (hom A B) public
      open MP (hom A B) public
    open MR′
    module ℱ = Functor

  cancel-comm : ∀ {β : f ⇒₂ g} → cancel.⇒.η g ∘ᵥ (β ⁻¹′ ⊚₁ β) ≈ cancel.⇒.η f
  cancel-comm {β = β} = cancel.⇒.commute β ○ identity₂ˡ

  cancel⁻¹-comm : ∀ {β : f ⇒₂ g} → (β ⁻¹′ ⊚₁ β) ∘ᵥ cancel.⇐.η f ≈ cancel.⇐.η g
  cancel⁻¹-comm {β = β} = ⟺ (cancel.⇐.commute β) ○ identity₂ʳ

  cancel′-comm : ∀ {β : f ⇒₂ g} → cancel′.⇒.η g ∘ᵥ (β ⊚₁ β ⁻¹′) ≈ cancel′.⇒.η f
  cancel′-comm {β = β} = cancel′.⇒.commute β ○ identity₂ˡ

  cancel′⁻¹-comm : ∀ {β : f ⇒₂ g} → (β ⊚₁ β ⁻¹′) ∘ᵥ cancel′.⇐.η f ≈ cancel′.⇐.η g
  cancel′⁻¹-comm {β = β} = ⟺ (cancel′.⇐.commute β) ○ identity₂ʳ

  hom⁻¹⁻¹≃id : ∀ {A B} → hom[ B , A ]⁻¹ ∘F hom[ A , B ]⁻¹ ≃ idF
  hom⁻¹⁻¹≃id {A} {B} = record
    { F⇒G = ntHelper record
      { η       = λ f → (((λ⇒ ∘ᵥ cancel.⇒.η (f ⁻¹) ◁ f) ∘ᵥ α⇐) ∘ᵥ f ⁻¹ ⁻¹ ▷ cancel.⇐.η f) ∘ᵥ ρ⇐
      ; commute = λ {f g} β → begin
        ((((λ⇒ ∘ᵥ cancel.⇒.η (g ⁻¹) ◁ g) ∘ᵥ α⇐) ∘ᵥ g ⁻¹ ⁻¹ ▷ cancel.⇐.η g) ∘ᵥ ρ⇐) ∘ᵥ β ⁻¹′ ⁻¹′
          ≈˘⟨ pushʳ ◁-∘ᵥ-ρ⇐ ⟩
        (((λ⇒ ∘ᵥ cancel.⇒.η (g ⁻¹) ◁ g) ∘ᵥ α⇐) ∘ᵥ g ⁻¹ ⁻¹ ▷ cancel.⇐.η g) ∘ᵥ ((β ⁻¹′ ⁻¹′ ◁ id₁) ∘ᵥ ρ⇐)
          ≈⟨ center ◁-▷-exchg ⟩
        ((λ⇒ ∘ᵥ cancel.⇒.η (g ⁻¹) ◁ g) ∘ᵥ α⇐) ∘ᵥ (β ⁻¹′ ⁻¹′ ◁ (g ⁻¹ ∘₁ g) ∘ᵥ f ⁻¹ ⁻¹ ▷ cancel.⇐.η g) ∘ᵥ ρ⇐
          ≈⟨ center (⟺ assoc₂ ○ hom.∘-resp-≈ α⇐-◁-∘₁ (ℱ.F-resp-≈ ((f ⁻¹ ⁻¹) ⊚-) (⟺ cancel⁻¹-comm))) ⟩
        (λ⇒ ∘ᵥ cancel.⇒.η (g ⁻¹) ◁ g) ∘ᵥ ((β ⁻¹′ ⁻¹′ ◁ g ⁻¹ ◁ g ∘ᵥ α⇐) ∘ᵥ f ⁻¹ ⁻¹ ▷ ((β ⁻¹′ ⊚₁ β) ∘ᵥ cancel.⇐.η f)) ∘ᵥ ρ⇐
          ≈⟨ refl⟩∘⟨ (hom.∘-resp-≈ʳ (ℱ.homomorphism ((f ⁻¹ ⁻¹) ⊚-)) ○ center (⊚-assoc.⇐.commute _) ○ center⁻¹ ([ ⊚ ]-merge (⟺ [ ⊚ ]-decompose₁) identity₂ˡ) refl) ⟩∘⟨refl ⟩
        (λ⇒ ∘ᵥ cancel.⇒.η (g ⁻¹) ◁ g) ∘ᵥ (((β ⁻¹′ ⁻¹′ ⊚₁ β ⁻¹′) ⊚₁ β) ∘ᵥ α⇐ ∘ᵥ f ⁻¹ ⁻¹ ▷ cancel.⇐.η f) ∘ᵥ ρ⇐
          ≈˘⟨ assoc₂ ⟩
        ((λ⇒ ∘ᵥ cancel.⇒.η (g ⁻¹) ◁ g) ∘ᵥ (((β ⁻¹′ ⁻¹′ ⊚₁ β ⁻¹′) ⊚₁ β) ∘ᵥ α⇐ ∘ᵥ f ⁻¹ ⁻¹ ▷ cancel.⇐.η f)) ∘ᵥ ρ⇐
          ≈⟨ center ([ ⊚ ]-merge cancel-comm identity₂ˡ) ⟩∘⟨refl ⟩
        (λ⇒ ∘ᵥ cancel.⇒.η (f ⁻¹) ⊚₁ β ∘ᵥ α⇐ ∘ᵥ f ⁻¹ ⁻¹ ▷ cancel.⇐.η f) ∘ᵥ ρ⇐
          ≈˘⟨ (assoc₂ ○ assoc₂) ⟩∘⟨refl ⟩
        (((λ⇒ ∘ᵥ cancel.⇒.η (f ⁻¹) ⊚₁ β) ∘ᵥ α⇐) ∘ᵥ f ⁻¹ ⁻¹ ▷ cancel.⇐.η f) ∘ᵥ ρ⇐
          ≈⟨ (hom.∘-resp-≈ʳ [ ⊚ ]-decompose₂) ⟩∘⟨refl ⟩∘⟨refl ⟩∘⟨refl ⟩
        (((λ⇒ ∘ᵥ id₁ ▷ β ∘ᵥ cancel.⇒.η (f ⁻¹) ◁ f) ∘ᵥ α⇐) ∘ᵥ f ⁻¹ ⁻¹ ▷ cancel.⇐.η f) ∘ᵥ ρ⇐
          ≈⟨ pullˡ λ⇒-∘ᵥ-▷ ⟩∘⟨refl ⟩∘⟨refl ⟩∘⟨refl ⟩
        ((((β ∘ᵥ λ⇒) ∘ᵥ cancel.⇒.η (f ⁻¹) ◁ f) ∘ᵥ α⇐) ∘ᵥ f ⁻¹ ⁻¹ ▷ cancel.⇐.η f) ∘ᵥ ρ⇐
          ≈⟨ (assoc₂ ○ assoc₂ ○ assoc₂ ○ assoc₂) ⟩
        β ∘ᵥ λ⇒ ∘ᵥ cancel.⇒.η (f ⁻¹) ◁ f ∘ᵥ α⇐ ∘ᵥ f ⁻¹ ⁻¹ ▷ cancel.⇐.η f ∘ᵥ ρ⇐
          ≈˘⟨ refl⟩∘⟨ (assoc₂ ○ assoc₂ ○ assoc₂) ⟩
        β ∘ᵥ (((λ⇒ ∘ᵥ cancel.⇒.η (f ⁻¹) ◁ f) ∘ᵥ α⇐) ∘ᵥ f ⁻¹ ⁻¹ ▷ cancel.⇐.η f) ∘ᵥ ρ⇐
          ∎
      }
    ; F⇐G = ntHelper record
      { η       = λ f → ρ⇒ ∘ᵥ f ⁻¹ ⁻¹ ▷ cancel.⇒.η f ∘ᵥ α⇒ ∘ᵥ cancel.⇐.η (f ⁻¹) ◁ f ∘ᵥ λ⇐
      ; commute = λ {f g} β → begin
        (ρ⇒ ∘ᵥ g ⁻¹ ⁻¹ ▷ cancel.⇒.η g ∘ᵥ α⇒ ∘ᵥ cancel.⇐.η (g ⁻¹) ◁ g ∘ᵥ λ⇐) ∘ᵥ β
          ≈⟨ assoc₂ ○ hom.∘-resp-≈ʳ (assoc₂ ○ hom.∘-resp-≈ʳ (assoc₂ ○ hom.∘-resp-≈ʳ assoc₂)) ⟩
        ρ⇒ ∘ᵥ g ⁻¹ ⁻¹ ▷ cancel.⇒.η g ∘ᵥ α⇒ ∘ᵥ cancel.⇐.η (g ⁻¹) ◁ g ∘ᵥ λ⇐ ∘ᵥ β
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ ▷-∘ᵥ-λ⇐ ⟩
        ρ⇒ ∘ᵥ g ⁻¹ ⁻¹ ▷ cancel.⇒.η g ∘ᵥ α⇒ ∘ᵥ cancel.⇐.η (g ⁻¹) ◁ g ∘ᵥ id₁ ▷ β ∘ᵥ λ⇐
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (⟺ [ ⊚ ]-decompose₁ ○ ⊚-resp-≈ˡ (⟺ cancel⁻¹-comm)) ⟩
        ρ⇒ ∘ᵥ g ⁻¹ ⁻¹ ▷ cancel.⇒.η g ∘ᵥ α⇒ ∘ᵥ (β ⁻¹′ ⁻¹′ ⊚₁ β ⁻¹′ ∘ᵥ cancel.⇐.η (f ⁻¹)) ⊚₁ β ∘ᵥ λ⇐
          ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ [ ⊚ ]-merge refl identity₂ʳ ⟩∘⟨refl ⟩
        ρ⇒ ∘ᵥ g ⁻¹ ⁻¹ ▷ cancel.⇒.η g ∘ᵥ α⇒ ∘ᵥ ((β ⁻¹′ ⁻¹′ ⊚₁ β ⁻¹′) ⊚₁ β ∘ᵥ cancel.⇐.η (f ⁻¹) ◁ f) ∘ᵥ λ⇐
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ center⁻¹ (⊚-assoc.⇒.commute _) refl ⟩
        ρ⇒ ∘ᵥ g ⁻¹ ⁻¹ ▷ cancel.⇒.η g ∘ᵥ (β ⁻¹′ ⁻¹′ ⊚₁ β ⁻¹′ ⊚₁ β ∘ᵥ α⇒) ∘ᵥ cancel.⇐.η (f ⁻¹) ◁ f ∘ᵥ λ⇐
          ≈⟨ refl⟩∘⟨ (hom.∘-resp-≈ʳ assoc₂ ○ pullˡ ([ ⊚ ]-merge identity₂ˡ cancel-comm)) ⟩
        ρ⇒ ∘ᵥ (β ⁻¹′ ⁻¹′) ⊚₁ (cancel.⇒.η f) ∘ᵥ α⇒ ∘ᵥ cancel.⇐.η (f ⁻¹) ◁ f ∘ᵥ λ⇐
          ≈⟨ refl⟩∘⟨ (hom.∘-resp-≈ˡ [ ⊚ ]-decompose₁ ○ assoc₂) ⟩
        ρ⇒ ∘ᵥ (β ⁻¹′ ⁻¹′) ◁ id₁ ∘ᵥ f ⁻¹ ⁻¹ ▷ cancel.⇒.η f ∘ᵥ α⇒ ∘ᵥ cancel.⇐.η (f ⁻¹) ◁ f ∘ᵥ λ⇐
          ≈⟨ (pullˡ ρ⇒-∘ᵥ-◁) ○ assoc₂ ⟩
        β ⁻¹′ ⁻¹′ ∘ᵥ ρ⇒ ∘ᵥ f ⁻¹ ⁻¹ ▷ cancel.⇒.η f ∘ᵥ α⇒ ∘ᵥ cancel.⇐.η (f ⁻¹) ◁ f ∘ᵥ λ⇐
          ∎
      }
    ; iso = λ f → Iso-∘ (Iso-swap (unitʳ.iso _)) $
                  Iso-∘ ([ (f ⁻¹ ⁻¹) ⊚- ]-resp-Iso (Iso-swap (cancel.iso f))) $
                  Iso-∘ (Iso-swap associator.iso) $
                  Iso-∘ ([ -⊚ f ]-resp-Iso (cancel.iso _))
                        (unitˡ.iso _)
    }

  hom⁻¹-weakInverse : ∀ {A B} → WeakInverse hom[ A , B ]⁻¹ hom[ B , A ]⁻¹
  hom⁻¹-weakInverse = record { F∘G≈id = hom⁻¹⁻¹≃id ; G∘F≈id = hom⁻¹⁻¹≃id }

  hom⁻¹-⊣Equivalence : ∀ {A} {B} → hom[ A , B ]⁻¹ ⊣⊢ hom[ B , A ]⁻¹
  hom⁻¹-⊣Equivalence {A} {B} = EP.F⊣⊢G (hom⁻¹-weakInverse {A} {B})

  open Bicategory C public

-- A bigroupoid is a bicategory that has a bigroupoid structure

record Bigroupoid (o ℓ e t : Level) : Set (suc (o ⊔ ℓ ⊔ e ⊔ t)) where
  field
    bicategory   : Bicategory o ℓ e t
    isBigroupoid : IsBigroupoid bicategory

  open IsBigroupoid isBigroupoid public
