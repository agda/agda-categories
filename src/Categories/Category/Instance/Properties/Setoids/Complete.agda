{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Properties.Setoids.Complete where

open import Level using (Level; _⊔_)
open import Data.Product using (Σ; proj₁; proj₂; _,_; Σ-syntax; _×_; -,_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Core using (Rel)
open Func

open import Categories.Category using (Category; _[_,_])
open import Categories.Functor
open import Categories.Category.Instance.Setoids
open import Categories.Category.Complete

import Categories.Category.Construction.Cones as Co

Setoids-Complete : (o ℓ e c ℓ′ : Level) → Complete o ℓ e (Setoids (c ⊔ ℓ ⊔ o ⊔ ℓ′) (o ⊔ ℓ′))
Setoids-Complete o ℓ e c ℓ′ {J} F =
  record
  { terminal = record
    { ⊤        = record
      { N     = record
        { Carrier       = Σ (∀ j → F₀.Carrier j)
                            (λ S → ∀ {X Y} (f : J [ X , Y ]) → [ F₀ Y ] F₁ f ⟨$⟩ S X ≈ S Y)
        ; _≈_           = λ { (S₁ , _) (S₂ , _) → ∀ j → [ F₀ j ] S₁ j ≈ S₂ j }
        ; isEquivalence = record
          { refl  = λ j → F₀.refl j
          ; sym   = λ a≈b j → F₀.sym j (a≈b j)
          ; trans = λ a≈b b≈c j → F₀.trans j (a≈b j) (b≈c j)
          }
        }
      ;  apex = record
        { ψ = λ j → record
          { to = λ { (S , _) → S j }
          ; cong  = λ eq → eq j
          }
        ; commute = λ { {X} {Y} X⇒Y {_ , eq} {y} f≈g → F₀.trans Y (eq X⇒Y) (f≈g Y) }
        }
      }
    ; ⊤-is-terminal = record
      { !        = λ {K} →
        let module K = Cone K
        in record
        { arr     = record
          { to = λ x → (λ j → K.ψ j ⟨$⟩ x) , λ f → K.commute f (Setoid.refl K.N)
          ; cong  = λ a≈b j → cong (K.ψ j) a≈b
          }
        ; commute = λ x≈y → cong (K.ψ _) x≈y
        }
      ; !-unique = λ {K} f x≈y j →
        let module K = Cone K
        in F₀.sym j (Cone⇒.commute f (Setoid.sym K.N x≈y))
      }
    }
  }
  where open Functor F
        open Co F
        module J    = Category J
        module F₀ j = Setoid (F₀ j)
        [_]_≈_ = Setoid._≈_
