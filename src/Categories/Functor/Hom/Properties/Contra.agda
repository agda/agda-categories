{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Functor.Hom.Properties.Contra {o ℓ e} (C : Category o ℓ e) where

private
  module C = Category C

open import Level
open import Function.Construct.Identity using () renaming (function to idFun)

open import Categories.Category.Instance.Setoids
open import Categories.Diagram.Limit
open import Categories.Diagram.Limit.Properties
open import Categories.Diagram.Colimit
open import Categories.Diagram.Duality
open import Categories.Functor
open import Categories.Functor.Hom
open import Categories.Functor.Hom.Properties.Covariant C.op
open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.NaturalIsomorphism

private
  variable
    o′ ℓ′ e′ : Level
    J : Category o′ ℓ′ e′

open C
open Hom C

-- contravariant hom functor sends colimit of F to its limit.
module _ (W : Obj) {F : Functor J C} (col : Colimit F) where
  private
    module F = Functor F
    module J = Category J
    open HomReasoning

    HomF : Functor J.op (Setoids ℓ e)
    HomF = Hom[-, W ] ∘F F.op

  hom-colimit⇒limit : Limit HomF
  hom-colimit⇒limit = ≃-resp-lim (Hom≃ ⓘʳ F.op) (hom-resp-limit W (Colimit⇒coLimit _ col))
    where Hom≃ : Hom[ op ][ W ,-] ≃ Hom[-, W ]
          Hom≃ = record
            { F⇒G = ntHelper record
              { η       = λ _ → idFun hom-setoid
              ; commute = λ _ → C.assoc
              }
            ; F⇐G = ntHelper record
              { η       = λ _ → idFun hom-setoid
              ; commute = λ _ → C.sym-assoc
              }
            ; iso = λ _ → record
              { isoˡ = C.Equiv.refl
              ; isoʳ = C.Equiv.refl
              }
            }
