{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Duality where

open import Level
open import Data.Product using (Σ; _,_)

open import Categories.Category
open import Categories.Category.Construction.Cones as Con
open import Categories.Category.Construction.Cocones as Coc
open import Categories.Functor
open import Categories.Functor.Continuous
open import Categories.Functor.Cocontinuous
open import Categories.Diagram.Limit as Lim
open import Categories.Diagram.Colimit as Col
open import Categories.Diagram.Duality
open import Categories.Morphism.Duality as MorD

private
  variable
    o ℓ e : Level
    C D E J : Category o ℓ e

module _ (G : Functor C D) {J : Category o ℓ e} where
  private
    module C = Category C
    module D = Category D
    module G = Functor G
    module J = Category J

  coLimitPreserving⇒ColimitPreserving : ∀ {F : Functor J C} (L : Limit (Functor.op F)) →
                                          LimitPreserving G.op L →
                                          ColimitPreserving G (coLimit⇒Colimit C L)
  coLimitPreserving⇒ColimitPreserving L (L′ , iso) = coLimit⇒Colimit D L′ , op-≅⇒≅ D iso

  ColimitPreserving⇒coLimitPreserving : ∀ {F : Functor J C} (L : Colimit F) →
                                          ColimitPreserving G L →
                                          LimitPreserving G.op (Colimit⇒coLimit C L)
  ColimitPreserving⇒coLimitPreserving L (L′ , iso) = Colimit⇒coLimit D L′ , op-≅⇒≅ D.op iso

module _ {o ℓ e} (G : Functor C D) where
  private
    module G = Functor G

  coContinuous⇒Cocontinuous : Continuous o ℓ e G.op → Cocontinuous o ℓ e G
  coContinuous⇒Cocontinuous Con L =
    coLimitPreserving⇒ColimitPreserving G (Colimit⇒coLimit C L) (Con (Colimit⇒coLimit C L))

  Cocontinuous⇒coContinuous : Cocontinuous o ℓ e G → Continuous o ℓ e G.op
  Cocontinuous⇒coContinuous Coc L =
    ColimitPreserving⇒coLimitPreserving G (coLimit⇒Colimit C L) (Coc (coLimit⇒Colimit C L))
