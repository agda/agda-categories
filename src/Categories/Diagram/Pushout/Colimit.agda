{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)

module Categories.Diagram.Pushout.Colimit {o ℓ e} (C : Category o ℓ e) where

open import Categories.Functor.Core using (Functor)
open import Categories.Diagram.Pushout C using (Pushout)
open import Categories.Category.Instance.Span using (Span; SpanObj; SpanArr)

import Categories.Diagram.Colimit as Colim
import Categories.Diagram.Duality as Dual
import Categories.Diagram.Pullback.Limit as PBLim

private
  module C = Category C
  open Category C using (_⇒_; Obj)

module _ {F : Functor Span C} where
  open Functor F using (F₀; F₁)
  open Colim F using (Colimit)
  open Dual C using (coPullback⇒Pushout; Colimit⇒coLimit)
  open PBLim C.op using (limit⇒pullback)

  private
    open SpanObj
    open SpanArr

    W = F₀ center
    A = F₀ left
    B = F₀ right

    W⇒A : W ⇒ A
    W⇒A = F₁ span-arrˡ

    W⇒B : W ⇒ B
    W⇒B = F₁ span-arrʳ

  colimit⇒pushout : Colimit → Pushout W⇒A W⇒B
  colimit⇒pushout colim = coPullback⇒Pushout (limit⇒pullback (Colimit⇒coLimit colim))

module _ {fA fB gA : Obj} {f : fB ⇒ fA} {g : fB ⇒ gA} (p : Pushout f g) where
  open PBLim C.op using (pullback⇒limit-F; pullback⇒limit)
  open Dual C using (coLimit⇒Colimit; Pushout⇒coPullback)

  pushout⇒colimit-F : Functor Span C
  pushout⇒colimit-F = Functor.op (pullback⇒limit-F (Pushout⇒coPullback p))

  open Colim pushout⇒colimit-F using (Colimit)

  pushout⇒colimit : Colimit
  pushout⇒colimit = coLimit⇒Colimit (pullback⇒limit (Pushout⇒coPullback p))
