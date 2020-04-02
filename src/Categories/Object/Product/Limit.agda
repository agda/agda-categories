{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Object.Product.Limit {o ℓ e} (C : Category o ℓ e) where

open import Data.Nat using (ℕ)
open import Data.Fin
open import Data.Fin.Patterns

open import Categories.Category.Finite.Fin
open import Categories.Category.Finite.Fin.Construction.Discrete
open import Categories.Object.Product C
open import Categories.Diagram.Limit
open import Categories.Functor

import Categories.Category.Construction.Cones as Co
import Categories.Morphism.Reasoning as MR

private
  module C = Category C
  open C

module _ {F : Functor (Discrete 2) C} where
  private
    module F = Functor F
    open F
    open MR C
    open HomReasoning

  limit⇒product : Limit F → Product (F₀ 0F) (F₀ 1F)
  limit⇒product L = record
    { A×B      = apex
    ; π₁       = proj 0F
    ; π₂       = proj 1F
    ; ⟨_,_⟩    = λ f g → rep record
      { apex = record
        { ψ       = λ { 0F → f
                      ; 1F → g }
        ; commute = λ { {0F} {0F} 0F → elimˡ identity
                      ; {1F} {1F} 0F → elimˡ identity }
        }
      }
    ; project₁ = commute
    ; project₂ = commute
    ; unique   = λ {_} {h} eq eq′ → terminal.!-unique record
      { arr     = h
      ; commute = λ { {0F} → eq
                    ; {1F} → eq′ }
      }
    }
    where open Limit L

  product⇒limit : Product (F₀ 0F) (F₀ 1F) → Limit F
  product⇒limit p = record
    { terminal = record
      { ⊤        = record
        { N    = A×B
        ; apex = record
          { ψ       = λ { 0F → π₁
                        ; 1F → π₂ }
          ; commute = λ { {0F} {0F} 0F → elimˡ identity
                        ; {1F} {1F} 0F → elimˡ identity }
          }
        }
      ; !        = λ {K} →
        let open Co.Cone F K
        in record
        { arr     = ⟨ ψ 0F , ψ 1F ⟩
        ; commute = λ { {0F} → project₁
                      ; {1F} → project₂ }
        }
      ; !-unique = λ {K} f →
        let module K = Co.Cone F K
            module f = Co.Cone⇒ F f
        in begin
          ⟨ K.ψ 0F , K.ψ 1F ⟩         ≈˘⟨ ⟨⟩-cong₂ f.commute f.commute ⟩
          ⟨ π₁ ∘ f.arr , π₂ ∘ f.arr ⟩ ≈⟨ g-η ⟩
          f.arr                       ∎
      }
    }
    where open Product p
