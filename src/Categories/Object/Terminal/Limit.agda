{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Object.Terminal.Limit {o ℓ e} (C : Category o ℓ e) where

open import Data.Nat using (ℕ)
open import Data.Fin
open import Data.Fin.Patterns

open import Categories.Category.Finite.Fin
open import Categories.Category.Finite.Fin.Construction.Discrete
open import Categories.Object.Terminal C
open import Categories.Diagram.Limit
open import Categories.Functor

import Categories.Category.Construction.Cones as Co
import Categories.Morphism.Reasoning as MR

private
  module C = Category C
  open C

module _ {F : Functor (Discrete 0) C} where
  private
    module F = Functor F
    open F
    open MR C
    open HomReasoning

  limit⇒⊥ : Limit F → Terminal
  limit⇒⊥ L = record
    { ⊤        = apex
    ; !        = rep record
      { apex = record
        { ψ       = λ ()
        ; commute = λ { {()} }
        }
      }
    ; !-unique = λ f → terminal.!-unique record
      { arr     = f
      ; commute = λ { {()} }
      }
    }
    where open Limit L

  ⊥⇒limit : Terminal → Limit F
  ⊥⇒limit t = record
    { terminal = record
      { ⊤        = record
        { N    = ⊤
        ; apex = record
          { ψ       = λ ()
          ; commute = λ { {()} }
          }
        }
      ; !        = λ {K} →
        let open Co.Cone F K
        in record
        { arr     = !
        ; commute = λ { {()} }
        }
      ; !-unique = λ f →
        let module f = Co.Cone⇒ F f
        in !-unique f.arr
      }
    }
    where open Terminal t
