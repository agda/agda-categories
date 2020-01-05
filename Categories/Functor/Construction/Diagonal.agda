{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Construction.Diagonal where

-- A variety of Diagonal functors

open import Level
open import Data.Product using (_,_)

open import Categories.Category
open import Categories.Functor
open import Categories.Category.Product
open import Categories.Category.Construction.Functors
open import Categories.Functor.Construction.Constant
open import Categories.NaturalTransformation using (ntHelper)

import Categories.Functor.Power as Power

private
  variable
    o ℓ e o′ ℓ′ e′ : Level

Δ : (C : Category o ℓ e) → Functor C (Product C C)
Δ C = record
  { F₀           = λ x → x , x
  ; F₁           = λ f → f , f
  ; identity     = refl , refl
  ; homomorphism = refl , refl
  ; F-resp-≈     = λ x → x , x
  }
  where
    open Category C
    open Equiv

Δ′ : (I : Set) → (C : Category o ℓ e) → Functor C (Power.Exp C I)
Δ′ I C = record
  { F₀           = λ x _ → x
  ; F₁           = λ f _ → f
  ; identity     = λ _ → refl
  ; homomorphism = λ _ → refl
  ; F-resp-≈     = λ x _ → x
  }
  where open Category.Equiv C

ΔF : {C : Category o ℓ e} (I : Category o′ ℓ′ e′) → Functor C (Functors I C)
ΔF {C = C} I = record
  { F₀           = const
  ; F₁           = λ f → ntHelper record { η = λ _ → f; commute = λ _ → C.identityʳ ○ ⟺ C.identityˡ }
  ; identity     = refl
  ; homomorphism = refl
  ; F-resp-≈     = λ x → x
  }
 where
   module C = Category C
   open C.Equiv
   open C.HomReasoning using (_○_; ⟺)
