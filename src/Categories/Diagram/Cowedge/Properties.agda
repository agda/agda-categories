{-# OPTIONS --without-K --safe #-}

-- Constructions of a Cocone from the Twisted Arrow function from a Cowedge
-- and vice-versa, by Duality.
-- Note that the proper functioning of this relies crucially on
-- Functor.op (Functor.op F) being definitionally equal to F.

open import Categories.Category using (Category)
open import Categories.Functor.Bifunctor using (Bifunctor)

module Categories.Diagram.Cowedge.Properties {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′}
  (F : Bifunctor (Category.op C) C D) where

open import Level

open import Categories.Category.Construction.TwistedArrow
open import Categories.Diagram.Cocone
open import Categories.Diagram.Cowedge
open import Categories.Diagram.Duality
open import Categories.Diagram.Wedge.Properties
open import Categories.Functor
open import Categories.Functor.Instance.Twisted C D
-- open import Categories.NaturalTransformation.Dinatural

Cowedge-to-Cocone : (W : Cowedge (Functor.op F)) → Cocone (Functor.op (Twist F))
Cowedge-to-Cocone W = coCone⇒Cocone (Category.op D) (Wedge-to-Cone F (Cowedge⇒coWedge (Category.op D) W))

Cocone-to-Cowedge : Cocone (Functor.op (Twist F)) → Cowedge (Functor.op F)
Cocone-to-Cowedge C = coWedge⇒Cowedge (Category.op D) (Cone-to-Wedge F (Cocone⇒coCone (Category.op D) C))
