{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Functor hiding (id)

module Categories.Diagram.Colimit.DualProperties
  {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} where

open import Function.Equality renaming (id to idFun)

open import Categories.Category.Instance.Setoids
open import Categories.Diagram.Duality C
open import Categories.Functor.Hom
open import Categories.Category.Construction.Cocones as Coc
open import Categories.Diagram.Limit as Lim
open import Categories.Diagram.Limit.Properties
open import Categories.Diagram.Colimit as Col
open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.NaturalIsomorphism
open import Categories.Morphism C
open import Categories.Morphism.Duality C

private
    module C = Category C
    module J = Category J
    open C
    open Hom C
    open HomReasoning

-- natural isomorphisms respects limits
module _ {F G : Functor J C} (F≃G : F ≃ G) where
  private
    module F  = Functor F
    module G  = Functor G
    open NaturalIsomorphism F≃G

  ≃-resp-colim : Colimit F → Colimit G
  ≃-resp-colim Cf = coLimit⇒Colimit (≃-resp-lim op′ (Colimit⇒coLimit Cf))

  ≃⇒Cocone⇒ : ∀ (Cf : Colimit F) (Cg : Colimit G) → Cocones G [ Colimit.colimit Cg , Colimit.colimit (≃-resp-colim Cf) ]
  ≃⇒Cocone⇒ Cf Cg = coCone⇒⇒Cocone⇒ (≃⇒Cone⇒ op′ (Colimit⇒coLimit Cf) (Colimit⇒coLimit Cg))

≃⇒colim≅ : ∀ {F G : Functor J C} (F≃G : F ≃ G) (Cf : Colimit F) (Cg : Colimit G) → Colimit.coapex Cf ≅ Colimit.coapex Cg
≃⇒colim≅ F≃G Cf Cg = op-≅⇒≅ (≃⇒lim≅ (NaturalIsomorphism.op′ F≃G) (Colimit⇒coLimit Cf) (Colimit⇒coLimit Cg))
