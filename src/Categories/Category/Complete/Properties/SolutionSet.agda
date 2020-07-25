{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Complete

module Categories.Category.Complete.Properties.SolutionSet where

open import Level

open import Categories.Functor
open import Categories.Object.Initial
open import Categories.Object.Product.Indexed
open import Categories.Object.Product.Indexed.Properties
open import Categories.Diagram.Equalizer
open import Categories.Diagram.Equalizer.Limit

import Categories.Diagram.Limit as Lim

private
  variable
    o ℓ e : Level
    o′ ℓ′ e′ : Level
    J : Category o ℓ e

module _ (C : Category o ℓ e) where
  open Category C

  record SolutionSet : Set (o ⊔ ℓ) where
    field
      D : Obj → Obj
      arr : ∀ X → D X ⇒ X

module _ {C : Category o ℓ e} (Com : Complete (o ⊔ ℓ ⊔ o′) (o ⊔ ℓ ⊔ ℓ′) (o ⊔ ℓ ⊔ e′) C) (S : SolutionSet C) where
  private
    module S = SolutionSet S
    module C = Category C

    open S
    open Category C

    W : IndexedProductOf C D
    W = Complete⇒IndexedProductOf C {o′ = ℓ ⊔ o′} {ℓ′ = ℓ ⊔ ℓ′} {e′ = ℓ ⊔ e′} Com D
    module W = IndexedProductOf W

    W⇒W : Set ℓ
    W⇒W = W.X ⇒ W.X

    Warr : IndexedProductOf C {I = W⇒W} λ _ → W.X
    Warr = Complete⇒IndexedProductOf C {o′ = o ⊔ o′} {ℓ′ = o ⊔ ℓ′} {e′ = o ⊔ e′} Com _
    module Warr = IndexedProductOf Warr

    Δ : W.X ⇒ Warr.X
    Δ = Warr.⟨ (λ _ → C.id) ⟩

    Γ : W.X ⇒ Warr.X
    Γ = Warr.⟨ (λ f → f) ⟩

    equalizer : Equalizer C Δ Γ
    equalizer = complete⇒equalizer C Com Δ Γ
    module equalizer = Equalizer equalizer

    ! : ∀ A → equalizer.obj ⇒ A
    ! A = arr A ∘ W.π A ∘ equalizer.arr

    module _ {A} (f : equalizer.obj ⇒ A) where

      !-unique : ! A ≈ f
      !-unique = {!!}

  SolutionSet⇒Initial : Initial C
  SolutionSet⇒Initial = record
    { ⊥        = equalizer.obj
    ; !        = ! _
    ; !-unique = !-unique
    }
