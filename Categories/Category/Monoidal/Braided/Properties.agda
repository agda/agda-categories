{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Braided using (Braided)

module Categories.Category.Monoidal.Braided.Properties
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (BM : Braided M) where

open import Data.Product using (_,_)

open import Categories.Category.Monoidal.Properties M
open import Categories.Functor using (Functor)
open import Categories.Morphism.Reasoning C
open import Categories.NaturalTransformation.NaturalIsomorphism.Properties
  using (push-eq)

open Category C
open Braided BM
open Commutation
open MonoidalReasoning

private
  variable
    X Y Z : Obj

  -- A shorthand for the braiding
  B : ∀ {X Y} → X ⊗₀ Y ⇒ Y ⊗₀ X
  B {X} {Y} = braiding.⇒.η (X , Y)

  -- sstucki: the structure of this proof is not obvious, and there
  -- are no references to the literature.  It would be nice to give a
  -- high-level, informal explanation of the proof.  For example, what
  -- is the intuition behind the following lemma?  Why is it
  -- necessary/useful in the final proof?

  hexagon-lemma : [ (X ⊗₀ unit) ⊗₀ unit ⇒ unit ⊗₀ X ]⟨
                    B  ⊗₁ id                    ⇒⟨ (unit ⊗₀ X) ⊗₀ unit ⟩
                    associator.from             ⇒⟨ unit ⊗₀ X ⊗₀ unit ⟩
                    id ⊗₁ B                     ⇒⟨ unit ⊗₀ unit ⊗₀ X ⟩
                    unitorˡ.from
                  ≈ unitorʳ.from                ⇒⟨ X ⊗₀ unit ⟩
                    B
                  ⟩
  hexagon-lemma = begin
                  unitorˡ.from ∘ id ⊗₁ B ∘ associator.from ∘ B ⊗₁ id      ≈⟨ refl⟩∘⟨ hexagon₁ ⟩
                  unitorˡ.from ∘ associator.from ∘ B ∘ associator.from    ≈⟨ pullˡ coherence₁ ⟩
                  unitorˡ.from ⊗₁ id ∘ B ∘ associator.from                ≈˘⟨ pushˡ (braiding.⇒.commute _) ⟩
                  (B ∘ id ⊗₁ unitorˡ.from) ∘ associator.from              ≈⟨ pullʳ triangle ⟩
                  B ∘ unitorʳ.from ⊗₁ id                                  ≈⟨ refl⟩∘⟨ unitor-coherenceʳ ⟩
                  B ∘ unitorʳ.from
                  ∎

  -- It's easier to prove the following lemma, which is the desired
  -- coherence theorem moduolo application of the |-⊗ unit| functor.
  -- Because |-⊗ unit| is equivalent to the identity functor, the
  -- lemma and the theorem are equivalent.

  braiding-coherence⊗unit : [ (X ⊗₀ unit) ⊗₀ unit ⇒ X ⊗₀ unit ]⟨
               B ⊗₁ id                       ⇒⟨ (unit ⊗₀ X) ⊗₀ unit ⟩
               unitorˡ.from ⊗₁ id
             ≈ unitorʳ.from ⊗₁ id
             ⟩
  braiding-coherence⊗unit = cancel-fromˡ braiding.FX≅GX (
    begin
      B ∘ unitorˡ.from ⊗₁ id ∘ B ⊗₁ id                               ≈⟨ pullˡ (⟺ (glue◽◃ unitorˡ-commute-from coherence₁)) ⟩
      (unitorˡ.from ∘ id ⊗₁ B ∘ associator.from) ∘ B ⊗₁ id           ≈⟨ assoc²' ⟩
      unitorˡ.from ∘ id ⊗₁ B ∘ associator.from ∘ B ⊗₁ id             ≈⟨ hexagon-lemma ⟩
      B ∘ unitorʳ.from                                               ≈˘⟨ refl⟩∘⟨ unitor-coherenceʳ ⟩
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
