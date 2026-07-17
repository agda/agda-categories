{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)

-- Defines the induced Monoidal structure of a Cocartesian Category

module Categories.Category.Cocartesian.Monoidal {o ℓ e} {𝒞 : Category o ℓ e} where

open Category 𝒞
open HomReasoning

open import Categories.Category.Cocartesian 𝒞
open import Categories.Category.Cartesian.Monoidal using (module CartesianMonoidal)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Morphism 𝒞
open import Categories.Morphism.Properties 𝒞
open import Categories.Morphism.Duality 𝒞
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)

open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Properties

private
  variable
    A : Obj

-- The cocartesian structure induces a monoidal one: 𝒞 is cocartesian monoidal.

module CocartesianMonoidal (cocartesian : Cocartesian) where
  open Cocartesian cocartesian using (⊥; _+_; _+-; -+_; -+-; +-assoc; module Dual)
  private module op-cartesianMonoidal = CartesianMonoidal Dual.op-cartesian

  ⊥+A≅A : ⊥ + A ≅ A
  ⊥+A≅A = op-≅⇒≅ (op-cartesianMonoidal.⊤×A≅A)

  A+⊥≅A : A + ⊥ ≅ A
  A+⊥≅A = op-≅⇒≅ (op-cartesianMonoidal.A×⊤≅A)

  open op-cartesianMonoidal using (monoidal; ⊤×--id; -×⊤-id)
  open NaturalIsomorphism using (op′)

  ⊥+--id : NaturalIsomorphism (⊥ +-) idF
  ⊥+--id = op′ ⊤×--id

  -+⊥-id : NaturalIsomorphism (-+ ⊥) idF
  -+⊥-id = op′ -×⊤-id

  open Monoidal monoidal using (unit; unitorˡ-commute-to; unitorˡ-commute-from; unitorʳ-commute-to;
    unitorʳ-commute-from; assoc-commute-to; assoc-commute-from; triangle; pentagon)

  +-monoidal : Monoidal 𝒞
  +-monoidal = record
    { ⊗                    = -+-
    ; unit                 = unit
    ; unitorˡ              = ⊥+A≅A
    ; unitorʳ              = A+⊥≅A
    ; associator           = ≅.sym +-assoc
    ; unitorˡ-commute-from = ⟺ unitorˡ-commute-to
    ; unitorˡ-commute-to   = ⟺ unitorˡ-commute-from
    ; unitorʳ-commute-from = ⟺ unitorʳ-commute-to
    ; unitorʳ-commute-to   = ⟺ unitorʳ-commute-from
    ; assoc-commute-from   = ⟺ assoc-commute-to
    ; assoc-commute-to     = ⟺ assoc-commute-from
    -- the proof idea of triangle is that the opposite triangle is obtained for free,
    -- but notice that triangle and the opposite triangle form isomorphism.
    ; triangle             = triangle'
    ; pentagon             = λ {X Y Z W} → pentagon' {X} {Y} {Z} {W}
    }
    where 
    open op-cartesianMonoidal
    open _≅_
    triangle' = λ {X Y} →
                          Iso-≈ triangle
                                (Iso-∘ ([ X +- ]-resp-Iso (Iso-swap (iso ⊥+A≅A)))
                                      (iso +-assoc))
                                ([ -+ Y ]-resp-Iso (Iso-swap (iso A+⊥≅A)))
    pentagon' = λ {X Y Z W} →
                          Iso-≈ pentagon
                                (Iso-∘ ([ X +- ]-resp-Iso (iso +-assoc))
                                (Iso-∘ (iso +-assoc)
                                      ([ -+ W ]-resp-Iso (iso +-assoc))))
                                (Iso-∘ (iso +-assoc) (iso +-assoc))