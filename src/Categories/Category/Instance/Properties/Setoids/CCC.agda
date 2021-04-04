{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Properties.Setoids.CCC where

open import Level
open import Data.Product using (Σ ; _,_)
open import Function.Equality as ⟶ using (Π; _⟶_)
open import Relation.Binary using (Setoid)

open import Categories.Category
open import Categories.Category.Monoidal.Instance.Setoids
open import Categories.Category.CartesianClosed
open import Categories.Category.CartesianClosed.Canonical renaming (CartesianClosed to CCartesianClosed)
open import Categories.Category.Instance.Setoids

open Π

module _ ℓ where
  private
    S = Setoids ℓ ℓ
    module S = Category S

  Setoids-Canonical : CCartesianClosed S
  Setoids-Canonical = record
    { ⊤            = ⊤
    ; _×_          = _×_
    ; !            = !
    ; π₁           = π₁
    ; π₂           = π₂
    ; ⟨_,_⟩        = ⟨_,_⟩
    ; !-unique     = !-unique
    ; π₁-comp      = λ {_ _ f _ g} → project₁ {h = f} {g}
    ; π₂-comp      = λ {_ _ f _ g} → project₂ {h = f} {g}
    ; ⟨,⟩-unique   = λ {_ _ _ f g h} → unique {h = h} {f} {g}
    ; _^_          = λ X Y → Y ⟶.⇨ X
    ; eval         = λ {X Y} → record
      { _⟨$⟩_ = λ { (f , x) → f ⟨$⟩ x }
      ; cong  = λ { (eq₁ , eq₂) → eq₁ eq₂ }
      }
    ; curry        = λ {C A B} f → record
      { _⟨$⟩_ = λ c → record
        { _⟨$⟩_ = λ a → f ⟨$⟩ (c , a)
        ; cong  = λ eq → cong f (Setoid.refl C , eq)
        }
      ; cong  = λ eq₁ eq₂ → cong f (eq₁ , eq₂)
      }
    ; eval-comp    = λ {_ _ _ f} → cong f
    ; curry-resp-≈ = λ eq₁ eq₂ eq → eq₁ (eq₂ , eq)
    ; curry-unique = λ eq₁ eq₂ eq → eq₁ (eq₂ , eq)
    }
    where open Setoids-Cartesian

  Setoids-CCC : CartesianClosed S
  Setoids-CCC = Equivalence.fromCanonical S Setoids-Canonical
