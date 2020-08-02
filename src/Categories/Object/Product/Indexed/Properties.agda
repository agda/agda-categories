{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Object.Product.Indexed.Properties {o ℓ e} (C : Category o ℓ e) where

open import Level

open import Categories.Category.Discrete
open import Categories.Category.Complete
open import Categories.Category.Construction.Cones
open import Categories.Category.Lift
open import Categories.Object.Product.Indexed C
open import Categories.Diagram.Limit
open import Categories.Functor

import Relation.Binary.PropositionalEquality as ≡

private
  variable
    o′ ℓ′ e′ : Level
  open Category C

module _ {i} (Com : Complete (i ⊔ o′) (i ⊔ ℓ′) (i ⊔ e′) C) where

  module _ {I : Set i} (P : I → Obj) where
    private
      Z = liftC o′ ℓ′ e′ (Discrete I)
      F = lift-func C P ∘F unliftF o′ ℓ′ e′ (Discrete I)
      module L = Limit (Com F)

      K : ∀ {Y} → (∀ i → Y ⇒ P i) → Cone F
      K f = record
        { apex = record
          { ψ       = λ i → f (lower i)
          ; commute = λ { (lift ≡.refl) → identityˡ }
          }
        }

    Complete⇒IndexedProductOf : IndexedProductOf P
    Complete⇒IndexedProductOf = record
      { X       = L.apex
      ; π       = λ i → L.proj (lift i)
      ; ⟨_⟩     = λ f → L.rep (K f)
      ; commute = λ f _ → Cone⇒.commute (L.rep-cone (K f))
      ; unique  = λ f g eq → L.terminal.!-unique {A = K g} record
        { arr     = f
        ; commute = eq _
        }
      }
