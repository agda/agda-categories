{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Functor.Bifunctor using (Bifunctor)

-- Note that everything is parametrized by a particular Bifunctor F

module Categories.Diagram.Coend.Properties {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′}
  (F : Bifunctor (Category.op C) C D) where

open import Categories.Category.Construction.Cowedges F
open import Categories.Diagram.Coend F
open import Categories.Object.Initial

-- Being a Coend is the same as being an Initial object in the category of Cowedges
Coend⇒Initial : Coend → Initial Cowedges
Coend⇒Initial c = record
  { ⊥ = cowedge
  ; ! = λ {A} → record { u = factor A ; commute = universal }
  ; !-unique = λ {A} f → unique {A} (Cowedge-Morphism.commute f)
  }
  where
  open Coend c

Initial⇒Coend : Initial Cowedges → Coend
Initial⇒Coend i = record
  { cowedge = ⊥
  ; factor = λ W → u {_} {W} !
  ; universal = commute !
  ; unique = λ {_} {g} x → !-unique (record { u = g ; commute = x })
  }
  where
  open Initial i
  open Cowedge-Morphism
