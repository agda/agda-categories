{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Morphism.Lifts.Properties {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level
open import Data.Product using (_,_; proj₁; proj₂)

open import Categories.Category.Construction.Arrow 𝒞

open import Categories.Diagram.Pullback 𝒞
open import Categories.Diagram.Pushout 𝒞

open import Categories.Morphism.Lifts 𝒞

open import Categories.Morphism.Reasoning 𝒞 renaming (glue to glue-■)
import Categories.Morphism as Mor

open Category 𝒞
open Definitions 𝒞
open HomReasoning

-- We want to talk about retracts of morphisms, so
-- we don't use the definition of 'Retract' applied to '𝒞'
open Mor 𝒞 hiding (Retract)
open Mor using (Retract)
open Morphism⇒

--------------------------------------------------------------------------------
-- Lifting and Retractions

module _ {X Y T} {f : X ⇒ Y} {i : X ⇒ T} {p : T ⇒ Y} (factors : f ≈ p ∘ i) where

  -- If 'f' factors into 'p ∘ i' and 'f' has the left lifting property
  -- with respect to 'p', then 'f' is a retraction of 'i' in the arrow
  -- category of 𝒞.
  retract-liftˡ : Lifts f p → Retract Arrow (mor f) (mor i)
  retract-liftˡ lifts = record
    { section = mor⇒ (fill-commˡ ○ ⟺ identityʳ)
    ; retract = mor⇒ (⟺ factors ○ ⟺ identityʳ)
    ; is-retract = identity² , fill-commʳ
    }
    where
      open Filler (lifts (identityˡ ○ factors))

  -- We have an analogous situation for right lifts.
  retract-liftʳ : Lifts i f → Retract Arrow (mor f) (mor p)
  retract-liftʳ lifts = record
    { section = mor⇒ (identityˡ ○ factors)
    ; retract = mor⇒ (identityˡ ○ ⟺ fill-commʳ)
    ; is-retract = fill-commˡ , identity²
    }
    where
      open Filler (lifts (⟺ factors ○ ⟺ identityʳ))

--------------------------------------------------------------------------------
-- Uniqueness of Diagonals

module _ {A B X Y : Obj} {i : A ⇒ B} {f : A ⇒ X}
         {g : B ⇒ Y} {p : X ⇒ Y} where
  Mono⇒UniqueDiagonal : Mono p
                      → CommutativeSquare i f g p
                      → (d : B ⇒ X)
                      → p ∘ d ≈ g
                      → UniqueDiagonal i f g p
  Mono⇒UniqueDiagonal p-mono g∘i≈p∘f d p∘d≈g = record
    { diagonal = diag
    ; unique = λ v → p-mono d (Diagonal.d v) (diag .commʳ ○ ⟺ (v .commʳ))
    }
    where
      diag : Diagonal _ _ _ _
      diag = record
        { d = d
        ; commˡ = p-mono (d ∘ i) f (pullˡ p∘d≈g ○ g∘i≈p∘f)
        ; commʳ = p∘d≈g
        }
      open Diagonal hiding (d)

  Epi⇒UniqueDiagonal : Epi i
                     → CommutativeSquare i f g p
                     → (d : B ⇒ X)
                     → d ∘ i ≈ f
                     → UniqueDiagonal i f g p
  Epi⇒UniqueDiagonal p-epi g∘i≈p∘f d d∘i≈f = record
    { diagonal = diag
    ; unique = λ v → p-epi d (Diagonal.d v) (diag .commˡ ○ ⟺ (v .commˡ))
    }
    where
      diag : Diagonal _ _ _ _
      diag = record
        { d = d
        ; commˡ = d∘i≈f
        ; commʳ = p-epi (p ∘ d) g (pullʳ d∘i≈f ○ ⟺ g∘i≈p∘f)
        }
      open Diagonal hiding (d)

--------------------------------------------------------------------------------
-- Closure Properties of Injective and Projective morphisms.

module _ {j} (J : MorphismClass j) where
  private
    variable
      X Y Z : Obj
      f g h i p : X ⇒ Y

  -- If 'f' is an isomorphism, then it must be J-Projective.
  iso-proj : ∀ {X Y} (f : X ⇒ Y) → IsIso f → Proj J f
  iso-proj f f-iso g g∈J {h} {i} comm = record
    { filler = h ∘ inv
    ; fill-commˡ = cancelʳ isoˡ
    ; fill-commʳ = extendʳ (⟺ comm) ○ elimʳ isoʳ
    }
    where
      open IsIso f-iso

  -- Dually, If 'f' is an isomorphism, then it must be J-Injective.
  iso-inj : ∀ {X Y} (f : X ⇒ Y) → IsIso f → Inj J f
  iso-inj f f-iso g g∈J {h} {i} comm = record
    { filler = inv ∘ i
    ; fill-commˡ = extendˡ comm ○ elimˡ isoˡ
    ; fill-commʳ = cancelˡ isoʳ
    }
    where
      open IsIso f-iso

  -- J-Projective morphisms are closed under composition.
  proj-∘ : ∀ {X Y Z} {f : Y ⇒ Z} {g : X ⇒ Y} → Proj J f → Proj J g → Proj J (f ∘ g)
  proj-∘ {f = f} {g = g} f-proj g-proj h h∈J {k} {i} comm = record
    { filler = UpperFiller.filler
    ; fill-commˡ = begin
        UpperFiller.filler ∘ f ∘ g
      ≈⟨ pullˡ UpperFiller.fill-commˡ ⟩
        LowerFiller.filler ∘ g
      ≈⟨ LowerFiller.fill-commˡ ⟩
        k
      ∎

    ; fill-commʳ = UpperFiller.fill-commʳ
    }
    where
      module LowerFiller = Filler (g-proj h h∈J (assoc ○ comm))
      module UpperFiller = Filler (f-proj h h∈J (⟺ LowerFiller.fill-commʳ))

  -- J-Injective morphisms are closed under composition.
  inj-∘ : ∀ {X Y Z} {f : Y ⇒ Z} {g : X ⇒ Y} → Inj J f → Inj J g → Inj J (f ∘ g)
  inj-∘ {f = f} {g = g} f-inj g-inj h h∈J {k} {i} comm = record
    { filler = LowerFiller.filler
    ; fill-commˡ = LowerFiller.fill-commˡ
    ; fill-commʳ = begin
        (f ∘ g) ∘ LowerFiller.filler
      ≈⟨ pullʳ LowerFiller.fill-commʳ ⟩
        f ∘ UpperFiller.filler
      ≈⟨ UpperFiller.fill-commʳ ⟩
        i
      ∎
    }
    where
      module UpperFiller = Filler (f-inj h h∈J (comm ○ assoc))
      module LowerFiller = Filler (g-inj h h∈J UpperFiller.fill-commˡ)

  -- J-Projective morphisms are stable under pushout.
  proj-pushout : ∀ {X Y Z} {p : X ⇒ Y} {f : X ⇒ Z} → (P : Pushout p f) → Proj J p → Proj J (Pushout.i₂ P)
  proj-pushout {p = p} {f = f} po p-proj h h∈J sq = record
    { filler = universal fill-commˡ
    ; fill-commˡ = universal∘i₂≈h₂
    ; fill-commʳ = unique-diagram (pullʳ universal∘i₁≈h₁ ○ fill-commʳ) (pullʳ universal∘i₂≈h₂ ○ ⟺ sq)
    }
    where
      open Pushout po
      open Filler (p-proj h h∈J (glue-■ sq commute))

  -- J-Injective morphisms are stable under pullback.
  inj-pullback : ∀ {X Y Z} {i : X ⇒ Z} {f : Y ⇒ Z} → (P : Pullback i f) → Inj J i → Inj J (Pullback.p₂ P)
  inj-pullback {i = i} {f = f} pb i-inj h h∈J sq = record
    { filler = universal fill-commʳ
    ; fill-commˡ = unique-diagram (pullˡ p₁∘universal≈h₁ ○ fill-commˡ) (pullˡ p₂∘universal≈h₂ ○ sq)
    ; fill-commʳ = p₂∘universal≈h₂
    }
    where
      open Pullback pb
      open Filler (i-inj h h∈J (glue-■ (⟺ commute) sq))

  -- J-Projective morphisms are stable under retractions.
  proj-retract : Proj J p → Retract Arrow (mor f) (mor p) → Proj J f
  proj-retract {p = p} {f = f} p-proj f-retracts h h∈J {g} {k} sq = record
    { filler = filler ∘ cod⇒ section
    ; fill-commˡ = begin
        (filler ∘ cod⇒ section) ∘ f
      ≈⟨ extendˡ (square section) ⟩
        (filler ∘ p) ∘ dom⇒ section
      ≈⟨ fill-commˡ ⟩∘⟨refl ⟩
        (g ∘ dom⇒ retract) ∘ dom⇒ section
      ≈⟨ cancelʳ (proj₁ is-retract) ⟩
        g
      ∎
    ; fill-commʳ = begin
        h ∘ filler ∘ cod⇒ section
      ≈⟨ extendʳ fill-commʳ ⟩
        k ∘ (cod⇒ retract ∘ cod⇒ section)
      ≈⟨ elimʳ (proj₂ is-retract) ⟩
        k
      ∎
    }
    where
      open Retract f-retracts
      open Filler (p-proj h h∈J (glue-■ sq (square retract)))

  -- J-Injective morphisms are stable under retractions.
  inj-retract : Inj J i → Retract Arrow (mor f) (mor i) → Inj J f
  inj-retract {i = i} {f = f} i-inj f-retracts h h∈J {g} {k} sq = record
    { filler = dom⇒ retract ∘ filler
    ; fill-commˡ = begin
        (dom⇒ retract ∘ filler) ∘ h
      ≈⟨ extendˡ fill-commˡ ⟩
        (dom⇒ retract ∘ dom⇒ section) ∘ g
      ≈⟨ elimˡ (proj₁ is-retract) ⟩
        g
      ∎
    ; fill-commʳ = begin
        f ∘ dom⇒ retract ∘ filler
      ≈⟨ extendʳ (⟺ (square retract)) ⟩
        cod⇒ retract ∘ i ∘ filler
      ≈⟨ refl⟩∘⟨ fill-commʳ ⟩
        cod⇒ retract ∘ cod⇒ section ∘ k
      ≈⟨ cancelˡ (proj₂ is-retract) ⟩
        k
      ∎
    }
    where
      open Retract f-retracts
      open Filler (i-inj h h∈J (glue-■ (square section) sq))
