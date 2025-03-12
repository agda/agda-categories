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
  private module _ {J : Category o′ ℓ′ e′} (F : Functor J C) where
    open Functor F

    cocomplete : Colimit F
    cocomplete = build-colim {OP = lowerAllCoproductsOf ℓ′ coprods F₀} {MP = lowerAllCoproductsOf o′ coprods (λ f → F₀ (Morphism.dom f))} (coequalizer _ _)

  AllCoproducts×Coequalizer⇒Cocomplete : Cocomplete o′ ℓ′ e′ C
  AllCoproducts×Coequalizer⇒Cocomplete = cocomplete
