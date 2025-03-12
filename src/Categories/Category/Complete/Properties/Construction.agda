{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Complete.Properties.Construction {o ℓ e} (C : Category o ℓ e) where

open import Level

open import Categories.Category.Construction.Arrow using (Morphism)
open import Categories.Category.Complete
open import Categories.Diagram.Equalizer C
open import Categories.Diagram.Limit
open import Categories.Diagram.Limit.Properties using (build-lim)
open import Categories.Object.Product.Indexed C
open import Categories.Object.Product.Indexed.Properties C
open import Categories.Functor

private
  variable
    o′ ℓ′ e′ : Level

module _ (prods : AllProductsOf (o′ ⊔ ℓ′)) (equalizer : ∀ {A B} (f g : C [ A , B ]) → Equalizer f g) where
  private module _ {J : Category o′ ℓ′ e′} (F : Functor J C) where
    open Functor F

    complete : Limit F
    complete = build-lim {OP = lowerAllProductsOf ℓ′ prods F₀} {MP = lowerAllProductsOf o′ prods λ f → F₀ (Morphism.cod f)} (equalizer _ _)

  AllProducts×Equalizer⇒Complete : Complete o′ ℓ′ e′ C
  AllProducts×Equalizer⇒Complete = complete
