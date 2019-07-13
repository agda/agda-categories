{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Morphism.Duality {o ℓ e} (C : Category o ℓ e) where

open Category C

import Categories.Morphism as M
private
  module Op = M op
open M C

open import Categories.Morphism.Properties C

private
  variable
    A B X Y : Obj
    f g h : A ⇒ B

Mono⇒op-Epi : Mono f → Op.Epi f
Mono⇒op-Epi mono = mono

Epi⇒op-Mono : Epi f → Op.Mono f
Epi⇒op-Mono epi = epi

Iso⇒op-Iso : Iso f g → Op.Iso g f
Iso⇒op-Iso iso = record
  { isoˡ = isoˡ
  ; isoʳ = isoʳ
  }
  where open Iso iso

op-Iso⇒Iso : Op.Iso g f → Iso f g
op-Iso⇒Iso iso = record
  { isoˡ = isoˡ
  ; isoʳ = isoʳ
  }
  where open Op.Iso iso

≅⇒op-≅ : A ≅ B → A Op.≅ B
≅⇒op-≅ A≅B = record
  { from = to
  ; to   = from
  ; iso  = record -- I don't understand why Agda doesn't allow me to apply Iso⇒op-Iso
    { isoˡ = isoˡ
    ; isoʳ = isoʳ
    }
  }
  where open _≅_ A≅B

op-≅⇒≅ : A Op.≅ B → A ≅ B
op-≅⇒≅ A≅B = record
  { from = to
  ; to   = from
  ; iso  = record
    { isoˡ = isoˡ
    ; isoʳ = isoʳ
    }
  }
  where open Op._≅_ A≅B
