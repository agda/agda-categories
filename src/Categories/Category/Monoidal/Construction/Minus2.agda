{-# OPTIONS --without-K --safe #-}

module Categories.Category.Monoidal.Construction.Minus2 where

-- Any -2-Category is Monoidal.  Of course, One is Monoidal, but
-- we don't need to shrink to do this, it can be done directly.
-- The assumptions in the construction of a -2-Category are all
-- needed to make things work properly.

open import Data.Product using (proj₁; proj₂)

open import Categories.Minus2-Category
open import Categories.Category.Monoidal
import Categories.Morphism as M

-- Doing it manually is just as easy as going through Cartesian here
-2-Monoidal : ∀ {o ℓ e} → (C : -2-Category {o} {ℓ} {e}) → Monoidal (-2-Category.cat C)
-2-Monoidal C = record
  { ⊗ = record
    { F₀ = proj₁
    ; F₁ = proj₁
    ; identity = Hom-Conn
    ; homomorphism = Hom-Conn
    ; F-resp-≈ = λ _ → Hom-Conn
    }
  ; unit = proj₁ Obj-Contr
  ; unitorˡ = λ {X} → proj₂ Obj-Contr X
  ; unitorʳ = M.≅.refl cat
  ; associator = M.≅.refl cat
  ; unitorˡ-commute-from = Hom-Conn
  ; unitorˡ-commute-to = Hom-Conn
  ; unitorʳ-commute-from = Hom-Conn
  ; unitorʳ-commute-to = Hom-Conn
  ; assoc-commute-from = Hom-Conn
  ; assoc-commute-to = Hom-Conn
  ; triangle = Hom-Conn
  ; pentagon = Hom-Conn
  }
  where
    open -2-Category C
