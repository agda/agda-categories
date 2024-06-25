{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Object.Terminal.Limit {o ℓ e} (C : Category o ℓ e) where

open import Categories.Category.Construction.Empty using (Empty)
open import Categories.Diagram.Limit
open import Categories.Functor.Core
open import Categories.Object.Terminal C

import Categories.Category.Construction.Cones as Co

private
  module C = Category C
  open C

module _ {o′ ℓ′ e′} {F : Functor (Empty {o′} {ℓ′} {e′}) C} where
  limit⇒⊤ : Limit F → Terminal
  limit⇒⊤ L = record
    { ⊤        = apex
    ; ⊤-is-terminal = record
      { !        = rep record
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
    }
    where open Limit L

module _ {o′ ℓ′ e′} {F : Functor (Empty {o′} {ℓ′} {e′}) C} where
  ⊤⇒limit : Terminal → Limit F
  ⊤⇒limit t = record
    { terminal = record
      { ⊤        = record
        { N    = ⊤
        ; apex = record
          { ψ       = λ ()
          ; commute = λ { {()} }
          }
        }
      ; ⊤-is-terminal = record
        { !        = λ {K} →
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
    }
    where open Terminal t
