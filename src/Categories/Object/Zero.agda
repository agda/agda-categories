{-# OPTIONS --without-K --safe #-}

open import Categories.Category

-- a zero object is both terminal and initial.
module Categories.Object.Zero {o ℓ e} (C : Category o ℓ e) where

open import Level using (_⊔_)

open import Categories.Object.Terminal C
open import Categories.Object.Initial C

open Category C

record Zero : Set (o ⊔ ℓ ⊔ e) where
 field
   zero : Obj
   !    : ∀ {A} → zero ⇒ A
   ¡    : ∀ {A} → A ⇒ zero

 field
   !-unique : ∀ {A} (f : zero ⇒ A) → ! ≈ f
   ¡-unique : ∀ {A} (f : A ⇒ zero) → ¡ ≈ f

 initial : Initial
 initial = record
   { ⊥        = zero
   ; ⊥-is-initial = record
     { !        = !
     ; !-unique = !-unique
     }
   }

 terminal : Terminal
 terminal = record
   { ⊤        = zero
   ; ⊤-is-terminal = record
     { !        = ¡
     ; !-unique = ¡-unique
     }
   }

 module initial  = Initial initial
 module terminal = Terminal terminal
