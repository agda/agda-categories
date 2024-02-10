{-# OPTIONS --safe --without-K #-}

open import Categories.Category
open import Categories.Category.Displayed

module Categories.Morphism.Displayed {o ℓ e o′ ℓ′ e′} {B : Category o ℓ e} (C : Displayed B o′ ℓ′ e′) where

open import Categories.Morphism B

open Category B
open Displayed C

private
  variable
    X Y : Obj
    X′ : Obj[ X ]
    Y′ : Obj[ Y ]

record DisplayedIso {from : X ⇒ Y} {to : Y ⇒ X} (from′ : X′ ⇒[ from ] Y′) (to′ : Y′ ⇒[ to ] X′) (iso : Iso from to) : Set e′ where
  open Iso iso
  field
    isoˡ′ : to′ ∘′ from′ ≈[ isoˡ ] id′
    isoʳ′ : from′ ∘′ to′ ≈[ isoʳ ] id′
