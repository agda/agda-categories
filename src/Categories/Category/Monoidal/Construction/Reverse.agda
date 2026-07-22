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

import Categories.Category.Construction.Core as Core
open import Categories.Category using (Category)
open import Categories.Category.Product using (_⁂_)
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Braided using (Braided)
import Categories.Category.Monoidal.Braided.Properties as BraidedProperties
import Categories.Category.Monoidal.Symmetric.Properties as SymmetricProperties
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
import Categories.Category.Monoidal.Utilities as MonoidalUtils
import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning as MorphismReasoning
open import Categories.Functor using (_∘F_) renaming (id to idF)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Functor.Monoidal.Symmetric using (module Strong)
open import Categories.Functor.Monoidal.Symmetric.Properties
  using (∘-StrongSymmetricMonoidal)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (_≃_; NaturalIsomorphism; niHelper)

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
    ; commutative = inv-commutative
    }
    where
      open Symmetric SM using (braided)
      open SymmetricProperties SM using (inv-commutative)

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

-- The identity functor from the reverse of a symmetric monoidal category
-- is strong symmetric monoidal.

module _ {o ℓ e} (C : SymmetricMonoidalCategory o ℓ e) where
  open SymmetricMonoidalCategory C
  open HomReasoning
  private module BraidProps = BraidedProperties braided
  private module MonoidalProps = MonoidalUtils monoidal
  open BraidProps using
    (assoc-reverse; braiding-coherence; braiding-coherence′)
  open BraidProps.Shorthands
  open Core.Shorthands U using (idᵢ)
  open MonoidalProps using (_⊗ᵢ_)
  open MonoidalProps.Shorthands
  open Morphism U using (module ≅)
  open MorphismReasoning U

  private module Reverse = SymmetricMonoidalCategory (Reverse-SymmetricMonoidalCategory C)

  private
    ⊗-homo :
      SymmetricMonoidalCategory.⊗ C ∘F (idF ⁂ idF)
      ≃ idF ∘F Reverse.⊗
    ⊗-homo = niHelper record
      { η       = λ _ → σ⇒
      ; η⁻¹     = λ _ → σ⇐
      ; commute = λ _ → braiding.⇒.commute _
      ; iso     = braiding.iso
      }

    module φ = NaturalIsomorphism ⊗-homo

    associativity : ∀ {X Y Z} →
      Reverse.associator.from ∘ φ.⇒.η (X Reverse.⊗₀ Y , Z) ∘ (φ.⇒.η (X , Y) ⊗₁ id)
      ≈ φ.⇒.η (X , Y Reverse.⊗₀ Z) ∘ (id ⊗₁ φ.⇒.η (Y , Z)) ∘ α⇒
    associativity {X} {Y} {Z} = begin
      α⇐ ∘ σ⇒ ∘ (σ⇒ ⊗₁ id)                      ≈⟨ refl⟩∘⟨ σ⇒-comm ⟩
      α⇐ ∘ (id ⊗₁ σ⇒) ∘ σ⇒                      ≈⟨ introʳ associator.isoˡ ⟩
      (α⇐ ∘ (id ⊗₁ σ⇒) ∘ σ⇒) ∘ α⇐ ∘ α⇒          ≈⟨ sym-assoc ⟩
      ((α⇐ ∘ (id ⊗₁ σ⇒) ∘ σ⇒) ∘ α⇐) ∘ α⇒        ≈⟨ assoc²βε ⟩∘⟨refl ⟩
      (α⇐ ∘ (id ⊗₁ σ⇒) ∘ σ⇒ ∘ α⇐) ∘ α⇒          ≈⟨ reverse-assoc ⟩∘⟨refl ⟩
      (σ⇒ ∘ (id ⊗₁ σ⇒)) ∘ α⇒                    ≈⟨ assoc ⟩
      σ⇒ ∘ (id ⊗₁ σ⇒) ∘ α⇒                      ∎
      where
        reverse-assoc :
          α⇐ ∘ (id ⊗₁ σ⇒) ∘ σ⇒ ∘ α⇐ ≈ σ⇒ ∘ (id ⊗₁ σ⇒)
        reverse-assoc = ⟺ (switch-fromtoˡ associator
          (switch-tofromˡ (idᵢ ⊗ᵢ σ) (switch-tofromˡ σ assoc-reverse)))

  reverse-idF-StrongSymmetricMonoidal :
    Strong.SymmetricMonoidalFunctor (Reverse-SymmetricMonoidalCategory C) C
  reverse-idF-StrongSymmetricMonoidal = record
    { F = idF
    ; isBraidedMonoidal = record
      { isStrongMonoidal = record
        { ε             = ≅.refl
        ; ⊗-homo        = ⊗-homo
        ; associativity = associativity
        ; unitaryˡ      = begin
          ρ⇒ ∘ σ⇒ ∘ id ⊗₁ id      ≈⟨ refl⟩∘⟨ elimʳ ⊗.identity ⟩
          ρ⇒ ∘ σ⇒                 ≈⟨ braiding-coherence′ ⟩
          λ⇒                      ∎
        ; unitaryʳ      = begin
          λ⇒ ∘ σ⇒ ∘ id ⊗₁ id      ≈⟨ refl⟩∘⟨ elimʳ ⊗.identity ⟩
          λ⇒ ∘ σ⇒                 ≈⟨ braiding-coherence ⟩
          ρ⇒                      ∎
        }
      ; braiding-compat = braiding.iso.isoˡ _ ○ ⟺ commutative
      }
    }

unreverse-StrongSymmetricMonoidal : ∀ {o ℓ e} {A C : SymmetricMonoidalCategory o ℓ e} →
  Strong.SymmetricMonoidalFunctor A (Reverse-SymmetricMonoidalCategory C) →
  Strong.SymmetricMonoidalFunctor A C
unreverse-StrongSymmetricMonoidal {C = C} H =
  ∘-StrongSymmetricMonoidal (reverse-idF-StrongSymmetricMonoidal C) H
