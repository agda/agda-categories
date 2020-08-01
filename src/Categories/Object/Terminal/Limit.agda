{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Object.Terminal.Limit {o ℓ e} (C : Category o ℓ e) where

open import Categories.Category.Lift
open import Categories.Category.Finite.Fin.Construction.Discrete
open import Categories.Object.Terminal C
open import Categories.Diagram.Limit
open import Categories.Functor.Core

import Categories.Category.Construction.Cones as Co

private
  module C = Category C
  open C

module _ {o′ ℓ′ e′} {F : Functor (liftC o′ ℓ′ e′ (Discrete 0)) C} where
  limit⇒⊥ : Limit F → Terminal
  limit⇒⊥ L = record
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

module _ o′ ℓ′ e′ where

  ⊥⇒limit-F : Functor (liftC o′ ℓ′ e′ (Discrete 0)) C
  ⊥⇒limit-F = record
    { F₀           = λ ()
    ; F₁           = λ { {()} }
    ; identity     = λ { {()} }
    ; homomorphism = λ { {()} }
    ; F-resp-≈     = λ { {()} }
    }

  ⊥⇒limit : Terminal → Limit ⊥⇒limit-F
  ⊥⇒limit t = record
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
          let open Co.Cone ⊥⇒limit-F K
          in record
          { arr     = !
          ; commute = λ { {()} }
          }
        ; !-unique = λ f →
          let module f = Co.Cone⇒ ⊥⇒limit-F f
          in !-unique f.arr
        }
      }
    }
    where open Terminal t
