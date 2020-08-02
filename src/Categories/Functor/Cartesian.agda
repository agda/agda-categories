{-# OPTIONS --without-K --safe #-}

-- A cartesian functor preserves products (of cartesian categories)
module Categories.Functor.Cartesian where

open import Data.Product using (Σ; _,_)
open import Level

open import Categories.Category.Cartesian
open import Categories.Category using (Category; _[_,_])
open import Categories.Category.Product
open import Categories.Functor using (Functor; _∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation)

private
  variable
    o ℓ e o′ ℓ′ e′ : Level

record CartesianF {A : Category o ℓ e} {B : Category o′ ℓ′ e′} (CA : Cartesian A) (CB : Cartesian B)
  (F : Functor A B) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private
    module CA = Cartesian CA
    module CB = Cartesian CB
  field
    -- F is product preserving
    ε : B [ CB.⊤ , Functor.F₀ F CA.⊤ ]
    ⊗-homo : NaturalTransformation (CB.⊗ ∘F (F ⁂ F)) (F ∘F CA.⊗)
