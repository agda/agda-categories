{-# OPTIONS --without-K --safe #-}

module Categories.Minus2-Category.Properties where

-- All -2-Categories are equivalent to One

open import Level
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

open import Categories.Minus2-Category
open import Categories.Category
import Categories.Morphism as M
open import Categories.Category.Monoidal
open import Categories.Category.Instance.One
open import Categories.Category.Equivalence hiding (refl)
open import Categories.NaturalTransformation using (ntHelper)

private
  variable
    o ℓ e : Level

shrink-them-all : (X : -2-Category {o} {ℓ} {e}) → StrongEquivalence (-2-Category.cat X) (One {o} {ℓ} {e})
shrink-them-all X = record
  { F = record
    { F₀ = λ _ → lift tt
    ; F₁ = λ _ → lift tt
    }
  ; G = record
    { F₀ = λ _ → proj₁ Obj-Contr
    ; F₁ = λ _ → M._≅_.from (proj₂ Obj-Contr (proj₁ Obj-Contr))
    ; identity = Hom-Conn
    ; homomorphism = Hom-Conn
    ; F-resp-≈ = λ _ → Hom-Conn
    }
  ; weak-inverse = record
    { F∘G≈id = _
    ; G∘F≈id = record
      { F⇒G = ntHelper (record
        { η = λ y → M._≅_.from (proj₂ Obj-Contr y)
        ; commute = λ _ → Hom-Conn
        })
      ; F⇐G = ntHelper (record
        { η = λ y → M._≅_.to (proj₂ Obj-Contr y)
        ; commute = λ _ → Hom-Conn
        })
      ; iso = λ Z → record
        { isoˡ = M._≅_.isoˡ (proj₂ Obj-Contr Z)
        ; isoʳ = M._≅_.isoʳ (proj₂ Obj-Contr Z)
        }
      }
    }
  }
  where
    open -2-Category X
    open Category cat
