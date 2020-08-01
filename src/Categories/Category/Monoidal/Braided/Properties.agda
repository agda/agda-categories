{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category; module Commutation)
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Braided using (Braided)

module Categories.Category.Monoidal.Braided.Properties
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (BM : Braided M) where

open import Data.Product using (_,_)

open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Utilities M
open import Categories.Functor using (Functor)
open import Categories.Morphism.Reasoning C hiding (push-eq)
open import Categories.NaturalTransformation.NaturalIsomorphism.Properties
  using (push-eq)

open Category C
open Braided BM
open Commutation C

private
  variable
    X Y Z : Obj

  -- A shorthand for the braiding
  B : ∀ {X Y} → X ⊗₀ Y ⇒ Y ⊗₀ X
  B {X} {Y} = braiding.⇒.η (X , Y)


  -- It's easier to prove the following lemma, which is the desired
  -- coherence theorem moduolo application of the |-⊗ unit| functor.
  -- Because |-⊗ unit| is equivalent to the identity functor, the
  -- lemma and the theorem are equivalent.

  -- The following diagram illustrates the hexagon that we are
  -- operating on. The main outer hexagon is hexagon₁, the braiding
  -- coherence, instantiated with X, 1 and 1 (Here we denote the unit
  -- by 1 for brevity).
  -- In the middle are X1 and 1X along with morphisms towards them.
  -- The lower hexagon (given by the double lines) commutes and is
  -- an intermediary in the final proof. It is there to effectively
  -- get rid of the top half of the main hexagon.
  -- The rest of the proof is isolating the bottom left triangle
  -- which represents our desired identity. It is doing that by
  -- proving that the pentagon to the right of it commutes.
  -- The pentagon commuting is, in turn, proved by gluing the
  -- rightmost "square" onto the middle triangle.
  --
  --
  --       ┌─────>  X(11)  ─────────>  (11)X ──────┐
  --      ┌┘ α        │        B         │       α └┐
  --     ┌┘           │id⊗λ              │λ⊗id     └┐
  --    ┌┘            V                  V           V
  --  (X1)1 ═══════> X1  ════════════>  1X <══════ 1(1X)
  --    ╚╗   ρ⊗id     Λ <───┐  B              λ      Λ
  --     ╚╗           │λ⊗id └────────┐              ╔╝
  --      ╚╗          │           λ   └┐           ╔╝
  --       ╚═════>  (1X)1  ═════════>  1(X1)  ═════╝
  --       B⊗id                α                id⊗B

  braiding-coherence⊗unit : [ (X ⊗₀ unit) ⊗₀ unit ⇒ X ⊗₀ unit ]⟨
               B ⊗₁ id                       ⇒⟨ (unit ⊗₀ X) ⊗₀ unit ⟩
               unitorˡ.from ⊗₁ id
             ≈ unitorʳ.from ⊗₁ id
             ⟩
  braiding-coherence⊗unit = cancel-fromˡ braiding.FX≅GX (
    begin
      B ∘ unitorˡ.from ⊗₁ id ∘ B ⊗₁ id                               ≈⟨ pullˡ (⟺ (glue◽◃ unitorˡ-commute-from coherence₁)) ⟩
      (unitorˡ.from ∘ id ⊗₁ B ∘ associator.from) ∘ B ⊗₁ id           ≈⟨ assoc²' ⟩
      unitorˡ.from ∘ id ⊗₁ B ∘ associator.from ∘ B ⊗₁ id             ≈⟨ refl⟩∘⟨ hexagon₁ ⟩
      unitorˡ.from ∘ associator.from ∘ B ∘ associator.from            ≈⟨ pullˡ coherence₁ ⟩
      unitorˡ.from ⊗₁ id ∘ B ∘ associator.from                       ≈˘⟨ pushˡ (braiding.⇒.commute _) ⟩
      (B ∘ id ⊗₁ unitorˡ.from) ∘ associator.from                     ≈⟨ pullʳ triangle ⟩
      B ∘ unitorʳ.from ⊗₁ id
    ∎)

-- The desired theorem follows from |braiding-coherence⊗unit| by
-- translating it along the right unitor (which is a natural iso).

braiding-coherence : [ X ⊗₀ unit ⇒ X ]⟨
                       B              ⇒⟨ unit ⊗₀ X ⟩
                       unitorˡ.from
                     ≈ unitorʳ.from
                     ⟩
braiding-coherence = push-eq unitorʳ-naturalIsomorphism (begin
  (unitorˡ.from ∘ B) ⊗₁ id           ≈⟨ homomorphism ⟩
  (unitorˡ.from ⊗₁ id) ∘ (B ⊗₁ id)   ≈⟨ braiding-coherence⊗unit ⟩
  unitorʳ.from  ⊗₁ id                ∎)
  where open Functor (-⊗ unit)
