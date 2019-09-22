{-# OPTIONS --without-K --safe #-}

-- 'Traditionally', meaning in nLab and in
-- "Lectures on n-Categories and Cohomology" by Baez and Shulman
-- https://arxiv.org/abs/math/0608420
-- (-2)-Categories are defined to be just a single value, with trivial Hom

-- But that's hardly a definition of a class of things, it's a definition of
-- a single structure!  What we want is the definition of a class which turns
-- out to be (essentially) unique. Rather like the reals are (essentially) the
-- only ordered complete archimedean field.

-- So we will take a -2-Category to be a full-fledge Category, but where
-- 1. |Obj| is (Categorically) contractible
-- 2. |Hom| is connected (all arrows are equal)
-- Note that we don't need to say anything at all about ≈

module Categories.Minus2-Category where

open import Level
open import Categories.Category
open import Data.Product using (Σ; _,_; proj₁; proj₂)
import Categories.Morphism as M
open import Categories.Category.Monoidal

-- for sanity checks
open import Categories.Category.Instance.One
open import Categories.Category.Groupoid
open import Data.Unit using (⊤; tt)
open import Categories.Category.Equivalence hiding (refl)

private
  variable
    o ℓ e : Level

record -2-Category : Set (suc (o ⊔ ℓ ⊔ e)) where
   field
     cat : Category o ℓ e
   open Category cat
   open M cat using (_≅_)

   field
     Obj-Contr : Σ Obj (λ x → (y : Obj) → x ≅ y)
     Hom-Conn  : {x y : Obj} {f g : x ⇒ y} → f ≈ g

-- For sanity checking, but will need to go elsewhere
⊤-is-2-Category : -2-Category {o} {ℓ} {e}
⊤-is-2-Category = record
  { cat = One
  ; Obj-Contr = _ , λ _ → _
  ; Hom-Conn = _
  }

-- More sanity check
private
  data Two : Set₀ where Z O : Two

-- so straightforward, Agda can provide most of it on its own
2-pt-cat : Category zero zero zero
2-pt-cat = record
  { Obj = Two
  ; _⇒_ = λ _ _ → ⊤ -- a single arrow between any two objects
  ; _≈_ = λ _ _ → ⊤ -- which are of course equal
  }

-- Note that there are no canonical witnesses of |Obj-Contr|, there are two choices, neither more
-- canonical than the other.
2-pt-is-2-Category : -2-Category
2-pt-is-2-Category = record
  { cat = 2-pt-cat
  ; Obj-Contr = Z , λ y → record { from = tt ; to = tt ; iso = record { isoˡ = tt ; isoʳ = tt } }
  }

-- The 'point' is that, as categories, One and 2-pt-cat are equivalent.

--- We can indeed prove that all -2 categories are (strongly) equivalent to One.
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
    { F∘G≈id = record
      { F⇒G = record { η = λ _ → _ ; commute = λ _ → _ }
      ; F⇐G = record { η = λ _ → _ ; commute = λ _ → _ }
      ; iso = λ _ → _
      }
    ; G∘F≈id = record
      { F⇒G = record
        { η = λ y → M._≅_.from (proj₂ Obj-Contr y)
        ; commute = λ _ → Hom-Conn
        }
      ; F⇐G = record
        { η = λ y → M._≅_.to (proj₂ Obj-Contr y)
        ; commute = λ _ → Hom-Conn
        }
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

-- Doing it manually is just as easy as going through Cartesian here
-2-Monoidal : (C : -2-Category {o} {ℓ} {e}) → Monoidal (-2-Category.cat C)
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
