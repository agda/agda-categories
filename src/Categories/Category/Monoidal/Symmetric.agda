{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Monoidal

module Categories.Category.Monoidal.Symmetric {o ℓ e} {C : Category o ℓ e} (M : Monoidal C) where

open import Level

open import Data.Product using (Σ; _,_)

open import Categories.Functor.Bifunctor
open import Categories.Functor.Properties
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)

open import Categories.Morphism C
open import Categories.Morphism.Properties C
open import Categories.Category.Monoidal.Braided M
open Category C
open Commutation C

private
  variable
    X Y Z : Obj

-- symmetric monoidal category
-- commutative braided monoidal category
--
-- the reason why we define symmetric categories via braided monoidal categories could
-- be not obvious, but it is the right definition: it requires again a redundant
-- hexagon proof which allows achieves definitional equality of the opposite.
record Symmetric : Set (levelOfTerm M) where
  field
    braided : Braided

  module braided = Braided braided
  open braided public

  private
    B : ∀ {X Y} → X ⊗₀ Y ⇒ Y ⊗₀ X
    B {X} {Y} = braiding.⇒.η (X , Y)

  field
    commutative : B {X} {Y} ∘ B {Y} {X} ≈ id

  braided-iso : X ⊗₀ Y ≅ Y ⊗₀ X
  braided-iso = record
    { from = B
    ; to   = B
    ; iso  = record
      { isoˡ = commutative
      ; isoʳ = commutative
      }
    }

  module braided-iso {X Y} = _≅_ (braided-iso {X} {Y})

private
  record Symmetric′ : Set (levelOfTerm M) where
    open Monoidal M

    field
      braiding : NaturalIsomorphism ⊗ (flip-bifunctor ⊗)

    module braiding = NaturalIsomorphism braiding

    private
      B : ∀ {X Y} → X ⊗₀ Y ⇒ Y ⊗₀ X
      B {X} {Y} = braiding.⇒.η (X , Y)

    field
      commutative : B {X} {Y} ∘ B {Y} {X} ≈ id
      hexagon     : [ (X ⊗₀ Y) ⊗₀ Z ⇒ Y ⊗₀ Z ⊗₀ X ]⟨
                      B  ⊗₁ id                    ⇒⟨ (Y ⊗₀ X) ⊗₀ Z ⟩
                      associator.from             ⇒⟨ Y ⊗₀ X ⊗₀ Z ⟩
                      id ⊗₁ B
                    ≈ associator.from             ⇒⟨ X ⊗₀ Y ⊗₀ Z ⟩
                      B                           ⇒⟨ (Y ⊗₀ Z) ⊗₀ X ⟩
                      associator.from
                    ⟩

    braided-iso : X ⊗₀ Y ≅ Y ⊗₀ X
    braided-iso = record
      { from = B
      ; to   = B
      ; iso  = record
        { isoˡ = commutative
        ; isoʳ = commutative
        }
      }

    module braided-iso {X Y} = _≅_ (braided-iso {X} {Y})

    -- we don't define [Symmetric] from [Braided] because we want to avoid asking
    -- [hexagon₂], which can readily be proven using the [hexagon] and [commutative].
    braided : Braided
    braided = record
      { braiding = braiding
      ; hexagon₁ = hexagon
      ; hexagon₂ = λ {X Y Z} →
                     Iso-≈ hexagon
                           (Iso-∘ (Iso-∘ ([ -⊗ Y ]-resp-Iso braided-iso.iso) associator.iso)
                                  ([ X ⊗- ]-resp-Iso braided-iso.iso))
                           (Iso-∘ (Iso-∘ associator.iso braided-iso.iso)
                                  associator.iso)
      }


symmetricHelper : Symmetric′ → Symmetric
symmetricHelper S = record
  { braided     = braided
  ; commutative = commutative
  }
  where open Symmetric′ S
