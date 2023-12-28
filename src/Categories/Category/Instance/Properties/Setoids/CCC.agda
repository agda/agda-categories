{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Properties.Setoids.CCC where

open import Level
open import Data.Product using (Σ ; _,_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Function.Construct.Setoid using (setoid)
open import Relation.Binary using (Setoid)

open import Categories.Category.Core using (Category)
open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.CartesianClosed using (CartesianClosed)
open import Categories.Category.CartesianClosed.Canonical renaming (CartesianClosed to CCartesianClosed)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cartesian)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Object.Terminal using (Terminal)

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
    ; _^_          = λ X Y → setoid Y X
    ; eval         = λ {X Y} →
      let module X = Setoid X in record
      { to = λ { (f , x) → f ⟨$⟩ x }
      ; cong  = λ { {( f₁ , x₁)} {(f₂ , x₂)} (eq₁ , eq₂) → 
          X.trans (eq₁ {x₁}) (Func.cong f₂ eq₂)}
      }
    ; curry        = λ {C A B} f → record
      { to = λ c → record
        { to = λ a → f ⟨$⟩ (c , a)
        ; cong  = λ eq → Func.cong f (Setoid.refl C , eq)
        }
      ; cong  = λ eq₁ → Func.cong f (eq₁ , (Setoid.refl A))
      }
    ; eval-comp    = λ {C A B f} → Func.cong f (Setoid.refl B , Setoid.refl A)
    ; curry-unique = λ eq → eq
    }
    where
      open Setoids-Cartesian
      open BinaryProducts products using (_×_; π₁; π₂; ⟨_,_⟩; project₁; project₂; unique)
      open Terminal terminal using (⊤; !; !-unique)

  Setoids-CCC : CartesianClosed S
  Setoids-CCC = Equivalence.fromCanonical S Setoids-Canonical
