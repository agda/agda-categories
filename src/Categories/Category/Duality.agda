{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Duality {o ℓ e} (C : Category o ℓ e) where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Categories.Category.Cartesian
open import Categories.Category.Cocartesian
open import Categories.Category.Complete
open import Categories.Category.Complete.Finitely
open import Categories.Category.Cocomplete
open import Categories.Category.Cocomplete.Finitely

open import Categories.Object.Duality
open import Categories.Diagram.Duality
open import Categories.Functor

private
  module C = Category C
  open C

coCartesian⇒Cocartesian : Cartesian C.op → Cocartesian C
coCartesian⇒Cocartesian Car = record
  { initial     = op⊤⇒⊥ C terminal
  ; coproducts  = record
    { coproduct = coProduct⇒Coproduct C product
    }
  }
  where open Cartesian Car

Cocartesian⇒coCartesian : Cocartesian C → Cartesian C.op
Cocartesian⇒coCartesian Co = record
  { terminal  = ⊥⇒op⊤ C initial
  ; products  = record
    { product = Coproduct⇒coProduct C coproduct
    }
  }
  where open Cocartesian Co

coComplete⇒Cocomplete : ∀ {o′ ℓ′ e′} → Complete o′ ℓ′ e′ C.op → Cocomplete o′ ℓ′ e′ C
coComplete⇒Cocomplete Com F = coLimit⇒Colimit C (Com F.op)
  where module F = Functor F

Cocomplete⇒coComplete : ∀ {o′ ℓ′ e′} → Cocomplete o′ ℓ′ e′ C → Complete o′ ℓ′ e′ C.op
Cocomplete⇒coComplete Coc F = Colimit⇒coLimit C (Coc F.op)
  where module F = Functor F

coFinitelyComplete⇒FinitelyCocomplete : FinitelyComplete C.op → FinitelyCocomplete C
coFinitelyComplete⇒FinitelyCocomplete FC = record
  { cocartesian = coCartesian⇒Cocartesian cartesian
  ; coequalizer = λ f g → coEqualizer⇒Coequalizer C (equalizer f g)
  }
  where open FinitelyComplete FC

FinitelyCocomplete⇒coFinitelyComplete : FinitelyCocomplete C → FinitelyComplete C.op
FinitelyCocomplete⇒coFinitelyComplete FC = record
  { cartesian = Cocartesian⇒coCartesian cocartesian
  ; equalizer = λ f g → Coequalizer⇒coEqualizer C (coequalizer f g)
  }
  where open FinitelyCocomplete FC



module DualityConversionProperties where

  private
    op-involutive : Category.op C.op ≡ C
    op-involutive = refl

    coCartesian⇔Cocartesian : ∀(coCartesian : Cartesian C.op)
                            → Cocartesian⇒coCartesian (coCartesian⇒Cocartesian coCartesian)
                              ≡ coCartesian
    coCartesian⇔Cocartesian _ = refl

    coFinitelyComplete⇔FinitelyCocomplete : ∀(coFinComplete : FinitelyComplete C.op) →
      FinitelyCocomplete⇒coFinitelyComplete
        (coFinitelyComplete⇒FinitelyCocomplete coFinComplete) ≡ coFinComplete
    coFinitelyComplete⇔FinitelyCocomplete _ = refl
