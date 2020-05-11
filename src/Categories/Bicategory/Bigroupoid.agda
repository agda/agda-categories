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
open import Categories.Bicategory.Extras
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
  open Bicategory C public
  open Extras C

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
                  [ (f ∘ₕ f ⁻¹) ∘ₕ f ⇒ f ]⟨
                    associator.from      ⇒⟨ f ∘ₕ f ⁻¹ ∘ₕ f ⟩
                    f ▷ cancel.⇒.η f     ⇒⟨ f ∘ₕ id₁ ⟩
                    unitorʳ.from
                  ≈ cancel′.⇒.η f ◁ f    ⇒⟨ id₁ ∘ₕ f ⟩
                    unitorˡ.from
                  ⟩
    pentagon₂ : ∀ {A B} {f : A ⇒₁ B} →
                  let open Commutation (hom B A) in
                  [ (f ⁻¹ ∘ₕ f) ∘ₕ f ⁻¹ ⇒ f ⁻¹ ]⟨
                    associator.from            ⇒⟨ f ⁻¹ ∘ₕ f ∘ₕ f ⁻¹ ⟩
                    f ⁻¹ ▷ cancel′.⇒.η f       ⇒⟨ f ⁻¹ ∘ₕ id₁ ⟩
                    unitorʳ.from
                  ≈ cancel.⇒.η f ◁ f ⁻¹        ⇒⟨ id₁ ∘ₕ f ⁻¹ ⟩
                    unitorˡ.from
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

  cancel-comm : ∀ {α : f ⇒₂ g} → cancel.⇒.η g ∘ᵥ (α ⁻¹′ ⊚₁ α) ≈ cancel.⇒.η f
  cancel-comm {α = α} = cancel.⇒.commute α ○ identity₂ˡ

  cancel⁻¹-comm : ∀ {α : f ⇒₂ g} → (α ⁻¹′ ⊚₁ α) ∘ᵥ cancel.⇐.η f ≈ cancel.⇐.η g
  cancel⁻¹-comm {α = α} = ⟺ (cancel.⇐.commute α) ○ identity₂ʳ

  cancel′-comm : ∀ {α : f ⇒₂ g} → cancel′.⇒.η g ∘ᵥ (α ⊚₁ α ⁻¹′) ≈ cancel′.⇒.η f
  cancel′-comm {α = α} = cancel′.⇒.commute α ○ identity₂ˡ

  cancel′⁻¹-comm : ∀ {α : f ⇒₂ g} → (α ⊚₁ α ⁻¹′) ∘ᵥ cancel′.⇐.η f ≈ cancel′.⇐.η g
  cancel′⁻¹-comm {α = α} = ⟺ (cancel′.⇐.commute α) ○ identity₂ʳ

  hom⁻¹⁻¹≃id : ∀ {A B} → hom[ B , A ]⁻¹ ∘F hom[ A , B ]⁻¹ ≃ idF
  hom⁻¹⁻¹≃id {A} {B} = record
    { F⇒G = ntHelper record
      { η       = λ f → (((unitorˡ.from ∘ᵥ cancel.⇒.η (f ⁻¹) ◁ f) ∘ᵥ associator.to) ∘ᵥ f ⁻¹ ⁻¹ ▷ cancel.⇐.η f) ∘ᵥ unitorʳ.to
      ; commute = λ {f g} α → begin
        ((((unitorˡ.from ∘ᵥ cancel.⇒.η (g ⁻¹) ◁ g) ∘ᵥ associator.to) ∘ᵥ g ⁻¹ ⁻¹ ▷ cancel.⇐.η g) ∘ᵥ unitorʳ.to) ∘ᵥ α ⁻¹′ ⁻¹′
          ≈˘⟨ pushʳ ◁-∘ᵥ-λ⁻¹ ⟩
        (((unitorˡ.from ∘ᵥ cancel.⇒.η (g ⁻¹) ◁ g) ∘ᵥ associator.to) ∘ᵥ g ⁻¹ ⁻¹ ▷ cancel.⇐.η g) ∘ᵥ ((α ⁻¹′ ⁻¹′ ◁ id₁) ∘ᵥ unitorʳ.to)
          ≈⟨ center ◁-▷-exchg ⟩
        ((unitorˡ.from ∘ᵥ cancel.⇒.η (g ⁻¹) ◁ g) ∘ᵥ associator.to) ∘ᵥ (α ⁻¹′ ⁻¹′ ◁ (g ⁻¹ ∘ₕ g) ∘ᵥ f ⁻¹ ⁻¹ ▷ cancel.⇐.η g) ∘ᵥ unitorʳ.to
          ≈⟨ center (⟺ assoc₂ ○ hom.∘-resp-≈ assoc⁻¹-◁-∘ₕ (ℱ.F-resp-≈ ((f ⁻¹ ⁻¹) ⊚-) (⟺ cancel⁻¹-comm))) ⟩
        (unitorˡ.from ∘ᵥ cancel.⇒.η (g ⁻¹) ◁ g) ∘ᵥ ((α ⁻¹′ ⁻¹′ ◁ g ⁻¹ ◁ g ∘ᵥ associator.to) ∘ᵥ f ⁻¹ ⁻¹ ▷ ((α ⁻¹′ ⊚₁ α) ∘ᵥ cancel.⇐.η f)) ∘ᵥ unitorʳ.to
          ≈⟨ refl⟩∘⟨ (hom.∘-resp-≈ʳ (ℱ.homomorphism ((f ⁻¹ ⁻¹) ⊚-)) ○ center (⊚-assoc.⇐.commute _) ○ center⁻¹ ([ ⊚ ]-merge (⟺ [ ⊚ ]-decompose₁) identity₂ˡ) refl) ⟩∘⟨refl ⟩
        (unitorˡ.from ∘ᵥ cancel.⇒.η (g ⁻¹) ◁ g) ∘ᵥ (((α ⁻¹′ ⁻¹′ ⊚₁ α ⁻¹′) ⊚₁ α) ∘ᵥ associator.to ∘ᵥ f ⁻¹ ⁻¹ ▷ cancel.⇐.η f) ∘ᵥ unitorʳ.to
          ≈˘⟨ assoc₂ ⟩
        ((unitorˡ.from ∘ᵥ cancel.⇒.η (g ⁻¹) ◁ g) ∘ᵥ (((α ⁻¹′ ⁻¹′ ⊚₁ α ⁻¹′) ⊚₁ α) ∘ᵥ associator.to ∘ᵥ f ⁻¹ ⁻¹ ▷ cancel.⇐.η f)) ∘ᵥ unitorʳ.to
          ≈⟨ center ([ ⊚ ]-merge cancel-comm identity₂ˡ) ⟩∘⟨refl ⟩
        (unitorˡ.from ∘ᵥ cancel.⇒.η (f ⁻¹) ⊚₁ α ∘ᵥ associator.to ∘ᵥ f ⁻¹ ⁻¹ ▷ cancel.⇐.η f) ∘ᵥ unitorʳ.to
          ≈˘⟨ (assoc₂ ○ assoc₂) ⟩∘⟨refl ⟩
        (((unitorˡ.from ∘ᵥ cancel.⇒.η (f ⁻¹) ⊚₁ α) ∘ᵥ associator.to) ∘ᵥ f ⁻¹ ⁻¹ ▷ cancel.⇐.η f) ∘ᵥ unitorʳ.to
          ≈⟨ (hom.∘-resp-≈ʳ [ ⊚ ]-decompose₂) ⟩∘⟨refl ⟩∘⟨refl ⟩∘⟨refl ⟩
        (((unitorˡ.from ∘ᵥ id₁ ▷ α ∘ᵥ cancel.⇒.η (f ⁻¹) ◁ f) ∘ᵥ associator.to) ∘ᵥ f ⁻¹ ⁻¹ ▷ cancel.⇐.η f) ∘ᵥ unitorʳ.to
          ≈⟨ pullˡ ρ-∘ᵥ-▷ ⟩∘⟨refl ⟩∘⟨refl ⟩∘⟨refl ⟩
        ((((α ∘ᵥ unitorˡ.from) ∘ᵥ cancel.⇒.η (f ⁻¹) ◁ f) ∘ᵥ associator.to) ∘ᵥ f ⁻¹ ⁻¹ ▷ cancel.⇐.η f) ∘ᵥ unitorʳ.to
          ≈⟨ (assoc₂ ○ assoc₂ ○ assoc₂ ○ assoc₂) ⟩
        α ∘ᵥ unitorˡ.from ∘ᵥ cancel.⇒.η (f ⁻¹) ◁ f ∘ᵥ associator.to ∘ᵥ f ⁻¹ ⁻¹ ▷ cancel.⇐.η f ∘ᵥ unitorʳ.to
          ≈˘⟨ refl⟩∘⟨ (assoc₂ ○ assoc₂ ○ assoc₂) ⟩
        α ∘ᵥ (((unitorˡ.from ∘ᵥ cancel.⇒.η (f ⁻¹) ◁ f) ∘ᵥ associator.to) ∘ᵥ f ⁻¹ ⁻¹ ▷ cancel.⇐.η f) ∘ᵥ unitorʳ.to
          ∎
      }
    ; F⇐G = ntHelper record
      { η       = λ f → unitorʳ.from ∘ᵥ f ⁻¹ ⁻¹ ▷ cancel.⇒.η f ∘ᵥ associator.from ∘ᵥ cancel.⇐.η (f ⁻¹) ◁ f ∘ᵥ unitorˡ.to
      ; commute = λ {f g} α → begin
        (unitorʳ.from ∘ᵥ g ⁻¹ ⁻¹ ▷ cancel.⇒.η g ∘ᵥ associator.from ∘ᵥ cancel.⇐.η (g ⁻¹) ◁ g ∘ᵥ unitorˡ.to) ∘ᵥ α
          ≈⟨ assoc₂ ○ hom.∘-resp-≈ʳ (assoc₂ ○ hom.∘-resp-≈ʳ (assoc₂ ○ hom.∘-resp-≈ʳ assoc₂)) ⟩
        unitorʳ.from ∘ᵥ g ⁻¹ ⁻¹ ▷ cancel.⇒.η g ∘ᵥ associator.from ∘ᵥ cancel.⇐.η (g ⁻¹) ◁ g ∘ᵥ unitorˡ.to ∘ᵥ α
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ ▷-∘ᵥ-ρ⁻¹ ⟩
        unitorʳ.from ∘ᵥ g ⁻¹ ⁻¹ ▷ cancel.⇒.η g ∘ᵥ associator.from ∘ᵥ cancel.⇐.η (g ⁻¹) ◁ g ∘ᵥ id₁ ▷ α ∘ᵥ unitorˡ.to
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (⟺ [ ⊚ ]-decompose₁ ○ ⊚.F-resp-≈ (⟺ cancel⁻¹-comm , refl)) ⟩
        unitorʳ.from ∘ᵥ g ⁻¹ ⁻¹ ▷ cancel.⇒.η g ∘ᵥ associator.from ∘ᵥ (α ⁻¹′ ⁻¹′ ⊚₁ α ⁻¹′ ∘ᵥ cancel.⇐.η (f ⁻¹)) ⊚₁ α ∘ᵥ unitorˡ.to
          ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ hom.∘-resp-≈ˡ ([ ⊚ ]-merge refl identity₂ʳ) ⟩
        unitorʳ.from ∘ᵥ g ⁻¹ ⁻¹ ▷ cancel.⇒.η g ∘ᵥ associator.from ∘ᵥ ((α ⁻¹′ ⁻¹′ ⊚₁ α ⁻¹′) ⊚₁ α ∘ᵥ cancel.⇐.η (f ⁻¹) ◁ f) ∘ᵥ unitorˡ.to
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ center⁻¹ (⊚-assoc.⇒.commute _) refl ⟩
        unitorʳ.from ∘ᵥ g ⁻¹ ⁻¹ ▷ cancel.⇒.η g ∘ᵥ (α ⁻¹′ ⁻¹′ ⊚₁ α ⁻¹′ ⊚₁ α ∘ᵥ associator.from) ∘ᵥ cancel.⇐.η (f ⁻¹) ◁ f ∘ᵥ unitorˡ.to
          ≈⟨ refl⟩∘⟨ (hom.∘-resp-≈ʳ assoc₂ ○ pullˡ ([ ⊚ ]-merge identity₂ˡ cancel-comm)) ⟩
        unitorʳ.from ∘ᵥ (α ⁻¹′ ⁻¹′) ⊚₁ (cancel.⇒.η f) ∘ᵥ associator.from ∘ᵥ cancel.⇐.η (f ⁻¹) ◁ f ∘ᵥ unitorˡ.to
          ≈⟨ refl⟩∘⟨ (hom.∘-resp-≈ˡ [ ⊚ ]-decompose₁ ○ assoc₂) ⟩
        unitorʳ.from ∘ᵥ (α ⁻¹′ ⁻¹′) ◁ id₁ ∘ᵥ f ⁻¹ ⁻¹ ▷ cancel.⇒.η f ∘ᵥ associator.from ∘ᵥ cancel.⇐.η (f ⁻¹) ◁ f ∘ᵥ unitorˡ.to
          ≈⟨ (pullˡ λ-∘ᵥ-◁) ○ assoc₂ ⟩
        α ⁻¹′ ⁻¹′ ∘ᵥ unitorʳ.from ∘ᵥ f ⁻¹ ⁻¹ ▷ cancel.⇒.η f ∘ᵥ associator.from ∘ᵥ cancel.⇐.η (f ⁻¹) ◁ f ∘ᵥ unitorˡ.to
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

-- A bigroupoid is a bicategory that has a bigroupoid structure

record Bigroupoid (o ℓ e t : Level) : Set (suc (o ⊔ ℓ ⊔ e ⊔ t)) where
  field
    bicategory   : Bicategory o ℓ e t
    isBigroupoid : IsBigroupoid bicategory

  open IsBigroupoid isBigroupoid public
