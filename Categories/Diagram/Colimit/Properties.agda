{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Functor hiding (id)

module Categories.Diagram.Colimit.Properties
  {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} (F : Functor J C) where

private
    module F = Functor F
    module C = Category C
    open C

open import Categories.Diagram.Limit F.op
open import Categories.Diagram.Colimit F
open import Categories.Category.Construction.Cocones F
open import Categories.Diagram.Duality C

module _ (X : Obj) (coapex₁ : Coapex X) (coapex₂ : Coapex X) (L : Colimit) where
  private
    module coapex₁ = Coapex coapex₁
    module coapex₂ = Coapex coapex₂
    module L = Colimit L

    K₁ : Cocone
    K₁ = record { coapex = coapex₁ }
    module K₁ = Cocone K₁

    K₂ : Cocone
    K₂ = record { coapex = coapex₂ }
    module K₂ = Cocone K₂

  coψ-≈⇒rep-≈ : (∀ A → coapex₁.ψ A ≈ coapex₂.ψ A) → L.rep K₁ ≈ L.rep K₂
  coψ-≈⇒rep-≈ = ψ-≈⇒rep-≈ X (Coapex⇒coApex X coapex₁) (Coapex⇒coApex X coapex₂) (Colimit⇒coLimit L)
