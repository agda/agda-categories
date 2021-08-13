{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)

-- The tensor product of certain monoidal categories is a monoidal functor.

module Categories.Functor.Monoidal.Tensor {o ℓ e} {C : Category o ℓ e}
  {M : Monoidal C} where

open import Data.Product using (_,_)

open import Categories.Category.Product using (Product)
open import Categories.Category.Monoidal.Braided using (Braided)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory; SymmetricMonoidalCategory)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.Monoidal.Construction.Product hiding (⊗)
open import Categories.Category.Monoidal.Interchange using (HasInterchange)
import Categories.Category.Monoidal.Interchange.Braided as BraidedInterchange
import Categories.Category.Monoidal.Interchange.Symmetric as SymmetricInterchange
open import Categories.Morphism using (module ≅)
open import Categories.Functor.Monoidal
import Categories.Functor.Monoidal.Braided as BMF
import Categories.Functor.Monoidal.Symmetric as SMF
open import Categories.NaturalTransformation.NaturalIsomorphism
   using (NaturalIsomorphism)

open NaturalIsomorphism
private
  C-monoidal : MonoidalCategory o ℓ e
  C-monoidal = record { U = C; monoidal = M }

  C×C          = Product C C
  C×C-monoidal = Product-MonoidalCategory C-monoidal C-monoidal

open MonoidalCategory C-monoidal

-- By definition, the tensor product ⊗ of a monoidal category C is a
-- binary functor ⊗ : C × C → C.  The product category C × C of a
-- monoidal category C is again monoidal.  Thus we may ask:
--
--   Is the functor ⊗ a monoidal functor, i.e. does it preserve the
--   monoidal structure in a suitable way (lax or strong)?
--
-- The answer is "yes", provided ⊗ comes equipped with a (coherent)
-- interchange map, aka a "four-middle interchange", which is the case
-- e.g. when C is braided.

module Lax (hasInterchange : HasInterchange M) where
  private module interchange = HasInterchange hasInterchange

  ⊗-isMonoidalFunctor : IsMonoidalFunctor C×C-monoidal C-monoidal ⊗
  ⊗-isMonoidalFunctor = record
    { ε             = unitorˡ.to
    ; ⊗-homo        = F⇒G interchange.naturalIso
    ; associativity = interchange.assoc
    ; unitaryˡ      = interchange.unitˡ
    ; unitaryʳ      = interchange.unitʳ
    }

  ⊗-MonoidalFunctor : MonoidalFunctor C×C-monoidal C-monoidal
  ⊗-MonoidalFunctor = record { F = ⊗ ; isMonoidal = ⊗-isMonoidalFunctor }

module LaxBraided (B : Braided M) where
  open Lax (BraidedInterchange.hasInterchange B) public

module LaxSymmetric (S : Symmetric M) where
  open BraidedInterchange (Symmetric.braided S) using (hasInterchange)
  open SymmetricInterchange S
  open Lax hasInterchange public
  open SymmetricMonoidalCategory using ()
    renaming (braidedMonoidalCategory to bmc)
  private
    C-symmetric : SymmetricMonoidalCategory o ℓ e
    C-symmetric = record { symmetric = S }

    C×C-symmetric = Product-SymmetricMonoidalCategory C-symmetric C-symmetric

  open BMF.Lax (bmc C×C-symmetric) (bmc C-symmetric)
  open SMF.Lax C×C-symmetric C-symmetric

  ⊗-isBraidedMonoidalFunctor : IsBraidedMonoidalFunctor ⊗
  ⊗-isBraidedMonoidalFunctor = record
    { isMonoidal      = ⊗-isMonoidalFunctor
    ; braiding-compat = swapInner-braiding′
    }

  ⊗-SymmetricMonoidalFunctor : SymmetricMonoidalFunctor
  ⊗-SymmetricMonoidalFunctor = record
    { isBraidedMonoidal = ⊗-isBraidedMonoidalFunctor }

module Strong (hasInterchange : HasInterchange M) where
  private module interchange = HasInterchange hasInterchange

  ⊗-isMonoidalFunctor : IsStrongMonoidalFunctor C×C-monoidal C-monoidal ⊗
  ⊗-isMonoidalFunctor = record
    { ε             = ≅.sym C unitorˡ
    ; ⊗-homo        = interchange.naturalIso
    ; associativity = interchange.assoc
    ; unitaryˡ      = interchange.unitˡ
    ; unitaryʳ      = interchange.unitʳ
    }

  ⊗-MonoidalFunctor : StrongMonoidalFunctor C×C-monoidal C-monoidal
  ⊗-MonoidalFunctor = record { isStrongMonoidal = ⊗-isMonoidalFunctor }

-- TODO: implement the missing bits in Categories.Category.Monoidal.Interchange.

module StrongBraided (B : Braided M) where
  open Strong (BraidedInterchange.hasInterchange B) public

module StrongSymmetric (S : Symmetric M) where
  open BraidedInterchange (Symmetric.braided S) using (hasInterchange)
  open SymmetricInterchange S
  open Strong hasInterchange public
  open SymmetricMonoidalCategory using ()
    renaming (braidedMonoidalCategory to bmc)
  private
    C-symmetric : SymmetricMonoidalCategory o ℓ e
    C-symmetric = record { symmetric = S }

    C×C-symmetric = Product-SymmetricMonoidalCategory C-symmetric C-symmetric

  open BMF.Strong (bmc C×C-symmetric) (bmc C-symmetric)
  open SMF.Strong C×C-symmetric C-symmetric

  ⊗-isBraidedMonoidalFunctor : IsBraidedMonoidalFunctor ⊗
  ⊗-isBraidedMonoidalFunctor = record
    { isStrongMonoidal = ⊗-isMonoidalFunctor
    ; braiding-compat  = swapInner-braiding′
    }

  ⊗-SymmetricMonoidalFunctor : SymmetricMonoidalFunctor
  ⊗-SymmetricMonoidalFunctor = record
    { isBraidedMonoidal = ⊗-isBraidedMonoidalFunctor }
