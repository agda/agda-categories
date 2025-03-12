{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Cocomplete.Properties.Construction {o ℓ e} (C : Category o ℓ e) where

open import Level

open import Categories.Category.Construction.Arrow using (Morphism)
open import Categories.Category.Cocomplete
open import Categories.Diagram.Coequalizer C
open import Categories.Diagram.Colimit
open import Categories.Diagram.Colimit.Properties using (build-colim)
open import Categories.Functor
open import Categories.Object.Coproduct.Indexed C
open import Categories.Object.Coproduct.Indexed.Properties C

private
  variable
    o′ ℓ′ e′ : Level

module _ (coprods : AllCoproductsOf (o′ ⊔ ℓ′)) (coequalizer : ∀ {A B} (f g : C [ A , B ]) → Coequalizer f g) where

  AllCoproducts×Coequalizer⇒Cocomplete : Cocomplete o′ ℓ′ e′ C
  AllCoproducts×Coequalizer⇒Cocomplete F = build-colim {OP = OP} {MP = MP} (coequalizer _ _)
    where
      open Functor F
      OP = lowerAllCoproductsOf ℓ′ coprods F₀
      MP = lowerAllCoproductsOf o′ coprods λ f → F₀ (Morphism.dom f)
