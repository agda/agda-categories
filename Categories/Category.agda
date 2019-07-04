{-# OPTIONS --without-K --safe #-}
module Categories.Category where

open import Level
open import Categories.Category.Core public

infix 10  _[_,_] _[_≈_] _[_∘_]

_[_,_] : ∀ {o ℓ e} → (C : Category o ℓ e) → (X : Category.Obj C) → (Y : Category.Obj C) → Set ℓ
_[_,_] = Category._⇒_

_[_≈_] : ∀ {o ℓ e} → (C : Category o ℓ e) → ∀ {X Y} (f g : C [ X , Y ]) → Set e
_[_≈_] = Category._≈_

_[_∘_] : ∀ {o ℓ e} → (C : Category o ℓ e) → ∀ {X Y Z} (f : C [ Y , Z ]) → (g : C [ X , Y ]) → C [ X , Z ]
_[_∘_] = Category._∘_

levelOf : ∀ {o ℓ e} → Category o ℓ e → Level
levelOf {o} {ℓ} {e} _ = o ⊔ ℓ ⊔ e
