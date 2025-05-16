{-# OPTIONS --without-K --safe #-}

module Categories.Diagram.Coend.Colimit where

open import Categories.Category.Equivalence as SE using (StrongEquivalence)
open import Categories.Category.Equivalence.Preserves using (pres-Initial)
open import Categories.Category.Core using (Category)
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Functor.Instance.Twisted using (Twist′)
open import Categories.Diagram.Coend using (Coend)
open import Categories.Diagram.Coend.Properties using (Coend⇒Initial; Initial⇒Coend)
open import Categories.Diagram.Colimit using (Colimit)
open import Categories.Diagram.Cowedge using (module Cowedge-Morphism)
open import Categories.Diagram.Cowedge.Properties using (CoconesTwist≅Cowedges)

import Categories.Category.Construction.Cowedges as Cowedges
import Categories.Object.Initial as Initial
import Categories.Morphism as M

module _ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′}
  (F : Bifunctor (Category.op C) C D) where
  private
    Eq = CoconesTwist≅Cowedges F
    module O = M D
  open M (Cowedges.Cowedges F)
  open Functor

  open StrongEquivalence Eq renaming (F to F⇒)

  Coend-yields-colimit : Coend F → Colimit (Twist′ C D F)
  Coend-yields-colimit ef = record { initial = pres-Initial (SE.sym Eq) (Coend⇒Initial F ef) }

  colimit-yields-Coend : Colimit (Twist′ C D F) → Coend F
  colimit-yields-Coend l = Initial⇒Coend F (pres-Initial Eq (Colimit.initial l))

  -- Coends and Colimits are equivalent, in the category Cowedge F
  Coend-as-Colimit : (coend : Coend F) → (cl : Colimit (Twist′ C D F)) → Coend.cowedge coend ≅ F₀ F⇒ (Colimit.initial.⊥ cl)
  Coend-as-Colimit coend cl = Initial.up-to-iso (Cowedges.Cowedges F) (Coend⇒Initial F coend) (pres-Initial Eq initial)
    where
    open Colimit cl

  -- Which then induces that the objects, in D, are also equivalent.
  Coend-as-Colimit-on-Obj : (coend : Coend F) → (cl : Colimit (Twist′ C D F)) → Coend.E coend O.≅ Colimit.coapex cl
  Coend-as-Colimit-on-Obj coend cl = record
    { from = Cowedge-Morphism.u (M._≅_.from X≅Y)
    ; to = Cowedge-Morphism.u (M._≅_.to X≅Y)
    ; iso = record
      { isoˡ = M._≅_.isoˡ X≅Y
      ; isoʳ = M._≅_.isoʳ X≅Y
      }
    }
    where
      X≅Y = Coend-as-Colimit coend cl
      open Category D
