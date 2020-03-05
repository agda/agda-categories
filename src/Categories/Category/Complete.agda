{-# OPTIONS --without-K --safe #-}

module Categories.Category.Complete where

open import Level

open import Categories.Category
open import Categories.Category.Construction.Cones
open import Categories.Functor
open import Categories.Diagram.Cone.Properties
open import Categories.Diagram.Limit using (Limit)

Complete : (o ℓ e : Level) {o′ ℓ′ e′ : Level} (C : Category o′ ℓ′ e′) → Set _
Complete o ℓ e C = ∀ {J : Category o ℓ e} (F : Functor J C) → Limit F

-- a functor between diagrams corresponds to a morphism between limits
module _ {o ℓ e o′ ℓ′ e′} {C : Category o′ ℓ′ e′} (Com : Complete o ℓ e C)
  {J J′ : Category o ℓ e} (F : Functor J′ J) (G : Functor J C) where

  private
    module C  = Category C
    module J  = Category J
    module J′ = Category J′
    module F  = Functor F
    module G  = Functor G

  F⇒arr : Cones (G ∘F F) [ F-map-Coneʳ F (Limit.limit (Com G)) , Limit.limit (Com (G ∘F F)) ]
  F⇒arr = Limit.rep-cone (Com (G ∘F F)) (F-map-Coneʳ F (Limit.limit (Com G)))
