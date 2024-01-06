{-# OPTIONS --without-K --safe #-}

module Categories.Category.Monoidal.Construction.Reverse where

-- The reverse monoidal category of a monoidal category V has the same
-- underlying category and unit as V but reversed monoidal product,
-- and similarly for tensors of morphisms.
--
-- https://ncatlab.org/nlab/show/reverse+monoidal+category

open import Level using (_⊔_)
open import Data.Product using (_,_; swap)
import Function

open import Categories.Category using (Category)
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Braided using (Braided)
import Categories.Category.Monoidal.Braided.Properties as BraidedProperties
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
import Categories.Category.Monoidal.Utilities as MonoidalUtils
import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning as MorphismReasoning
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)

open Category using (Obj)

module _ {o ℓ e} {C : Category o ℓ e} (M : Monoidal C) where

  private module M = Monoidal M

  open Function using (_∘_)
  open Category C using (sym-assoc)
  open Category.HomReasoning C using (⟺; _○_)
  open Morphism C using (module ≅)
  open MorphismReasoning C using (switch-fromtoʳ)
  open MonoidalUtils M using (pentagon-inv)

  ⊗ : Bifunctor C C C
  ⊗ = record
    { F₀           = M.⊗.₀ ∘ swap
    ; F₁           = M.⊗.₁ ∘ swap
    ; identity     = M.⊗.identity
    ; homomorphism = M.⊗.homomorphism
    ; F-resp-≈     = M.⊗.F-resp-≈ ∘ swap
    }

  Reverse-Monoidal : Monoidal C
  Reverse-Monoidal = record
    { ⊗                    = ⊗
    ; unit                 = M.unit
    ; unitorˡ              = M.unitorʳ
    ; unitorʳ              = M.unitorˡ
    ; associator           = ≅.sym M.associator
    ; unitorˡ-commute-from = M.unitorʳ-commute-from
    ; unitorˡ-commute-to   = M.unitorʳ-commute-to
    ; unitorʳ-commute-from = M.unitorˡ-commute-from
    ; unitorʳ-commute-to   = M.unitorˡ-commute-to
    ; assoc-commute-from   = M.assoc-commute-to
    ; assoc-commute-to     = M.assoc-commute-from
    ; triangle             = ⟺ (switch-fromtoʳ M.associator M.triangle)
    ; pentagon             = sym-assoc ○ pentagon-inv
    }

module _ {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} where

  open Category C using (assoc; sym-assoc)
  open Category.HomReasoning C using (_○_)

  -- The reverse of a braided category is again braided.

  Reverse-Braided : Braided M → Braided (Reverse-Monoidal M)
  Reverse-Braided BM = record
    { braiding  = niHelper (record
      { η       = braiding.⇐.η
      ; η⁻¹     = braiding.⇒.η
      ; commute = braiding.⇐.commute
      ; iso     = λ XY → record
        { isoˡ  = braiding.iso.isoʳ XY
        ; isoʳ  = braiding.iso.isoˡ XY }
      })
    ; hexagon₁  = sym-assoc ○ hexagon₁-inv ○ assoc
    ; hexagon₂  = assoc ○ hexagon₂-inv ○ sym-assoc
    }
    where
      open Braided BM
      open BraidedProperties BM using (hexagon₁-inv; hexagon₂-inv)

  -- The reverse of a symmetric category is again symmetric.

  Reverse-Symmetric : Symmetric M → Symmetric (Reverse-Monoidal M)
  Reverse-Symmetric SM = record
    { braided     = Reverse-Braided braided
    ; commutative = commutative′
    }
    where
      open Symmetric SM

      -- FIXME: the below should probably go into
      -- Categories.Monoidal.Symmetric.Properties, but we currently
      -- have no such module.

      open Category C
      open MorphismReasoning C using (introʳ; cancelˡ)

      braiding-selfInverse : ∀ {X Y} → braiding.⇐.η (X , Y) ≈ braiding.⇒.η (Y , X)
      braiding-selfInverse = introʳ commutative ○ cancelˡ (braiding.iso.isoˡ _)

      commutative′ : ∀ {X Y} → braiding.⇐.η (X , Y) ∘ braiding.⇐.η (Y , X) ≈ id
      commutative′ = ∘-resp-≈ braiding-selfInverse braiding-selfInverse ○ commutative

-- Bundled versions of the above

Reverse-MonoidalCategory : ∀ {o ℓ e} → MonoidalCategory o ℓ e → MonoidalCategory o ℓ e
Reverse-MonoidalCategory C = record
  { U        = U
  ; monoidal = Reverse-Monoidal monoidal
  }
  where open MonoidalCategory C

Reverse-BraidedMonoidalCategory : ∀ {o ℓ e} →
  BraidedMonoidalCategory o ℓ e → BraidedMonoidalCategory o ℓ e
Reverse-BraidedMonoidalCategory C = record
  { U        = U
  ; monoidal = Reverse-Monoidal monoidal
  ; braided  = Reverse-Braided braided
  }
  where open BraidedMonoidalCategory C

Reverse-SymmetricMonoidalCategory : ∀ {o ℓ e} →
  SymmetricMonoidalCategory o ℓ e → SymmetricMonoidalCategory o ℓ e
Reverse-SymmetricMonoidalCategory C = record
  { U         = U
  ; monoidal  = Reverse-Monoidal monoidal
  ; symmetric = Reverse-Symmetric symmetric
  }
  where open SymmetricMonoidalCategory C
