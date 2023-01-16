{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Duality where

open import Level
open import Data.Product using (Σ; _,_)

open import Categories.Category
open import Categories.Category.Construction.Cones as Con
open import Categories.Category.Construction.Cocones as Coc
open import Categories.Functor
open import Categories.Functor.Limits
open import Categories.Object.Initial
open import Categories.Object.Terminal
open import Categories.Diagram.Limit as Lim
open import Categories.Diagram.Colimit as Col
open import Categories.Diagram.Duality
open import Categories.Morphism.Duality as MorD

open import Categories.Functor.Algebra using (F-Algebra; F-Algebra-Morphism)
open import Categories.Functor.Coalgebra using (F-Coalgebra; F-Coalgebra-Morphism)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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

  coPreservesLimit⇒PreservesCoLimit : ∀ {F : Functor J C} (L : Limit (Functor.op F)) →
                                          PreservesLimit G.op L →
                                          PreservesColimit G (coLimit⇒Colimit C L)
  coPreservesLimit⇒PreservesCoLimit L is⊤ = record
    { !        = λ {K} → coCone⇒⇒Cocone⇒ _ (! {Cocone⇒coCone _ K})
    ; !-unique = λ f → !-unique (Cocone⇒⇒coCone⇒ _ f)
    }
    where open IsTerminal is⊤

  PreservesColimit⇒coPreservesLimit : ∀ {F : Functor J C} (L : Colimit F) →
                                        PreservesColimit G L →
                                        PreservesLimit G.op (Colimit⇒coLimit C L)
  PreservesColimit⇒coPreservesLimit L is⊥ = record
    { !        = λ {K} → Cocone⇒⇒coCone⇒ _ (! {coCone⇒Cocone _ K})
    ; !-unique = λ f → !-unique (coCone⇒⇒Cocone⇒ _ f)
    }
    where open IsInitial is⊥

module _ {o ℓ e} (G : Functor C D) where
  private
    module G = Functor G

  coContinuous⇒Cocontinuous : Continuous o ℓ e G.op → Cocontinuous o ℓ e G
  coContinuous⇒Cocontinuous Con L =
    coPreservesLimit⇒PreservesCoLimit G (Colimit⇒coLimit C L) (Con (Colimit⇒coLimit C L))

  Cocontinuous⇒coContinuous : Cocontinuous o ℓ e G → Continuous o ℓ e G.op
  Cocontinuous⇒coContinuous Coc L =
    PreservesColimit⇒coPreservesLimit G (coLimit⇒Colimit C L) (Coc (coLimit⇒Colimit C L))

module _ {F : Endofunctor C} where
  open Functor F renaming (op to Fop)

  -- Obj conversions

  coF-Algebra⇒F-Coalgebra : F-Algebra Fop → F-Coalgebra F
  coF-Algebra⇒F-Coalgebra algOp = record { A = A algOp; α = α algOp } where
    open F-Algebra

  F-Coalgebra⇒coF-Algebra : F-Coalgebra F → F-Algebra Fop
  F-Coalgebra⇒coF-Algebra algOp = record { A = A algOp; α = α algOp } where
    open F-Coalgebra

  -- Mor conversions

  coF-Algebra-Morphism⇒F-Coalgebra-Morphism : ∀ {X Y : F-Algebra Fop} →
    F-Algebra-Morphism X Y →
      F-Coalgebra-Morphism (coF-Algebra⇒F-Coalgebra Y) (coF-Algebra⇒F-Coalgebra X)
  coF-Algebra-Morphism⇒F-Coalgebra-Morphism morOp =
      record { f = f morOp ; commutes = commutes morOp } where
        open F-Algebra-Morphism

  F-Coalgebra-Morphism⇒coF-Algebra-Morphism : ∀ {X Y : F-Coalgebra F} →
    F-Coalgebra-Morphism X Y →
      F-Algebra-Morphism (F-Coalgebra⇒coF-Algebra Y) (F-Coalgebra⇒coF-Algebra X)
  F-Coalgebra-Morphism⇒coF-Algebra-Morphism morOp =
      record { f = f morOp ; commutes = commutes morOp } where
        open F-Coalgebra-Morphism
