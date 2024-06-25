{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Object.Initial.Colimit {o ℓ e} (C : Category o ℓ e) where

open import Categories.Category.Construction.Cocones using (Cocone; Cocone⇒)
open import Categories.Category.Finite.Fin.Construction.Discrete using (Discrete)
open import Categories.Category.Lift using (liftC)
open import Categories.Diagram.Colimit using (Colimit)
open import Categories.Functor.Core using (Functor)
open import Categories.Object.Initial C

private
  open module C = Category C

module _ {o′ ℓ′ e′} {F : Functor (liftC o′ ℓ′ e′ (Discrete 0)) C} where
  colimit⇒⊥ : Colimit F → Initial
  colimit⇒⊥ L = record
    { ⊥        = coapex
    ; ⊥-is-initial = record
      { !        = rep record
        { coapex = record
          { ψ       = λ ()
          ; commute = λ { {()} }
          }
        }
      ; !-unique = λ f → initial.!-unique record
        { arr     = f
        ; commute = λ { {()} }
        }
      }
    }
    where open Colimit L

module _ {o′ ℓ′ e′} {F : Functor (liftC o′ ℓ′ e′ (Discrete 0)) C} where

  ⊥⇒colimit : Initial → Colimit F
  ⊥⇒colimit t = record
    { initial = record
      { ⊥        = record
        { N    = ⊥
        ; coapex = record
          { ψ       = λ ()
          ; commute = λ { {()} }
          }
        }
      ; ⊥-is-initial = record
        { !        = λ {K} →
          let open Cocone F K
          in record
          { arr     = !
          ; commute = λ { {()} }
          }
        ; !-unique = λ f →
          let module f = Cocone⇒ F f
          in !-unique f.arr
        }
      }
    }
    where open Initial t
