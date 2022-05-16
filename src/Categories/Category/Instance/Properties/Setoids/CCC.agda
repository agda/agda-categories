{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Properties.Setoids.CCC where

open import Level
open import Data.Product using (Σ ; _,_)
open import Function.Equality as ⟶ using (Π; _⟶_)
open import Relation.Binary using (Setoid)

open import Categories.Category.Core using (Category)
open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.CartesianClosed using (CartesianClosed)
open import Categories.Category.CartesianClosed.Canonical renaming (CartesianClosed to CCartesianClosed)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cartesian)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Object.Terminal using (Terminal)

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
    ; curry-unique = λ eq₁ eq₂ eq → eq₁ (eq₂ , eq)
    }
    where
      open Setoids-Cartesian
      open BinaryProducts products using (_×_; π₁; π₂; ⟨_,_⟩; project₁; project₂; unique)
      open Terminal terminal using (⊤; !; !-unique)

  Setoids-CCC : CartesianClosed S
  Setoids-CCC = Equivalence.fromCanonical S Setoids-Canonical
