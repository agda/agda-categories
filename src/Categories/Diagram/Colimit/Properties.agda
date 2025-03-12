{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Diagram.Colimit.Properties
  {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {J : Category o′ ℓ′ e′}  where

private
    module C = Category C
    open C

open import Categories.Diagram.Cocone
open import Categories.Diagram.Limit as Lim
open import Categories.Diagram.Colimit
open import Categories.Functor hiding (id)
open import Categories.Diagram.Duality C

module _ (F : Functor J C) (X : Obj) (coapex₁ : Coapex F X) (coapex₂ : Coapex F X) (L : Colimit F) where
  private
    module F = Functor F
    module coapex₁ = Coapex coapex₁
    module coapex₂ = Coapex coapex₂
    module L = Colimit L

    K₁ : Cocone F
    K₁ = record { coapex = coapex₁ }
    module K₁ = Cocone K₁

    K₂ : Cocone F
    K₂ = record { coapex = coapex₂ }
    module K₂ = Cocone K₂

  coψ-≈⇒rep-≈ : (∀ A → coapex₁.ψ A ≈ coapex₂.ψ A) → L.rep K₁ ≈ L.rep K₂
  coψ-≈⇒rep-≈ = ψ-≈⇒rep-≈ F.op X (Coapex⇒coApex X coapex₁) (Coapex⇒coApex X coapex₂) (Colimit⇒coLimit L)
