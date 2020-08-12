{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core

module Categories.Object.Product.Limit {o ℓ e} (C : Category o ℓ e) where

open import Level
open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Patterns

open import Categories.Category.Lift
open import Categories.Category.Finite.Fin
open import Categories.Category.Finite.Fin.Construction.Discrete
open import Categories.Object.Product C
open import Categories.Diagram.Limit
open import Categories.Functor.Core

import Categories.Category.Construction.Cones as Co
import Categories.Morphism.Reasoning as MR

private
  module C = Category C
  open C
  open MR C
  open HomReasoning

module _ {o′ ℓ′ e′} {F : Functor (liftC o′ ℓ′ e′ (Discrete 2)) C} where
  private
    module F = Functor F
    open F

  limit⇒product : Limit F → Product (F₀ (lift 0F)) (F₀ (lift 1F))
  limit⇒product L = record
    { A×B      = apex
    ; π₁       = proj (lift 0F)
    ; π₂       = proj (lift 1F)
    ; ⟨_,_⟩    = λ f g → rep record
      { apex = record
        { ψ       = λ { (lift 0F) → f
                      ; (lift 1F) → g }
        ; commute = λ { {lift 0F} {lift 0F} (lift 0F) → elimˡ identity
                      ; {lift 1F} {lift 1F} (lift 0F) → elimˡ identity }
        }
      }
    ; project₁ = commute
    ; project₂ = commute
    ; unique   = λ {_} {h} eq eq′ → terminal.!-unique record
      { arr     = h
      ; commute = λ { {lift 0F} → eq
                    ; {lift 1F} → eq′ }
      }
    }
    where open Limit L

module _ o′ ℓ′ e′ A B where
  open Equiv

  product⇒limit-F : Functor (liftC o′ ℓ′ e′ (Discrete 2)) C
  product⇒limit-F = record
    { F₀           = λ { (lift 0F) → A
                       ; (lift 1F) → B }
    ; F₁           = λ { {lift 0F} {lift 0F} _ → C.id
                       ; {lift 1F} {lift 1F} _ → C.id }
    ; identity     = λ { {lift 0F} → refl
                       ; {lift 1F} → refl }
    ; homomorphism = λ { {lift 0F} {lift 0F} {lift 0F} → sym identity²
                       ; {lift 1F} {lift 1F} {lift 1F} → sym identity² }
    ; F-resp-≈     = λ { {lift 0F} {lift 0F} _ → refl
                       ; {lift 1F} {lift 1F} _ → refl }
    }

module _ o′ ℓ′ e′ {A B} (p : Product A B) where
  open Product p
  private
    F = product⇒limit-F o′ ℓ′ e′ A B
    open Functor F

  product⇒limit : Limit F
  product⇒limit = record
    { terminal = record
      { ⊤        = record
        { N    = A×B
        ; apex = record
          { ψ       = λ { (lift 0F) → π₁
                        ; (lift 1F) → π₂ }
          ; commute = λ { {lift 0F} {lift 0F} (lift 0F) → identityˡ
                        ; {lift 1F} {lift 1F} (lift 0F) → identityˡ }
          }
        }
      ; ⊤-is-terminal = record
        { !        = λ {K} →
          let open Co.Cone F K
          in record
          { arr     = ⟨ ψ (lift 0F) , ψ (lift 1F) ⟩
          ; commute = λ { {lift 0F} → project₁
                        ; {lift 1F} → project₂ }
          }
        ; !-unique = λ {K} f →
          let module K = Co.Cone F K
              module f = Co.Cone⇒ F f
          in begin
            ⟨ K.ψ (lift 0F) , K.ψ (lift 1F) ⟩ ≈˘⟨ ⟨⟩-cong₂ f.commute f.commute ⟩
            ⟨ π₁ ∘ f.arr , π₂ ∘ f.arr ⟩       ≈⟨ g-η ⟩
            f.arr                             ∎
        }
      }
    }
