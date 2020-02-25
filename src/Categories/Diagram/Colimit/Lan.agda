{-# OPTIONS --without-K --safe #-}

module Categories.Diagram.Colimit.Lan where

open import Level
open import Categories.Category
open import Categories.Category.Cocomplete
open import Categories.Diagram.Duality
open import Categories.Diagram.Limit.Ran
open import Categories.Functor
open import Categories.Kan
open import Categories.Kan.Duality

private
  variable
    o ℓ e : Level
    C D E : Category o ℓ e

module _ {o ℓ e o′ ℓ′ e′} {C : Category o′ ℓ′ e′} {D : Category o ℓ e}
         (F : Functor C D) (X : Functor C E) (Com : Cocomplete (o′ ⊔ ℓ) (ℓ′ ⊔ e) e′ E) where
  private
    module F = Functor F
    module X = Functor X

  colimit-is-lan : Lan F X
  colimit-is-lan = coRan⇒Lan (limit-is-ran F.op X.op λ G → Colimit⇒coLimit E (Com (Functor.op G)))
