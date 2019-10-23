{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Monoidal
import Categories.Category.Monoidal.Properties as MProperties
import Categories.Morphism.Reasoning as Reasoning

module Categories.Category.Monoidal.Braided {o ℓ e} {C : Category o ℓ e} (M : Monoidal C) where

open import Level

open import Data.Product using (Σ; _,_)

open import Categories.Functor.Bifunctor
open import Categories.NaturalTransformation.NaturalIsomorphism

open Category C
open Commutation

private
  variable
    X Y Z W : Obj
    f g h : X ⇒ Y

-- braided monoidal category
-- it has a braiding natural isomorphism has two hexagon identities.
-- these two identities are directly expressed in the morphism level.
record Braided : Set (levelOfTerm M) where
  open Monoidal M public

  field
    braiding : NaturalIsomorphism ⊗ (flip-bifunctor ⊗)

  module braiding = NaturalIsomorphism braiding
  
  private
    B : ∀ {X Y} → X ⊗₀ Y ⇒ Y ⊗₀ X
    B {X} {Y} = braiding.⇒.η (X , Y)

    B-commute : ∀ {X Y Z W} → {f : X ⇒ Y} → {g : Z ⇒ W} → CommutativeSquare (f ⊗₁ g) B B (g ⊗₁ f)
    B-commute {_} {_} {_} {_} {f} {g} = braiding.⇒.commute (f , g)

  field
    hexagon₁ : [ (X ⊗₀ Y) ⊗₀ Z ⇒ Y ⊗₀ Z ⊗₀ X ]⟨
                 B  ⊗₁ id                    ⇒⟨ (Y ⊗₀ X) ⊗₀ Z ⟩
                 associator.from             ⇒⟨ Y ⊗₀ X ⊗₀ Z ⟩
                 id ⊗₁ B
               ≈ associator.from             ⇒⟨ X ⊗₀ Y ⊗₀ Z ⟩
                 B                           ⇒⟨ (Y ⊗₀ Z) ⊗₀ X ⟩
                 associator.from
               ⟩
    hexagon₂ : [ X ⊗₀ Y ⊗₀ Z ⇒ (Z ⊗₀ X) ⊗₀ Y ]⟨
                 id ⊗₁ B                     ⇒⟨ X ⊗₀ Z ⊗₀ Y ⟩
                 associator.to               ⇒⟨ (X ⊗₀ Z) ⊗₀ Y ⟩
                 B ⊗₁ id                 
               ≈ associator.to               ⇒⟨ (X ⊗₀ Y) ⊗₀ Z ⟩
                 B                           ⇒⟨ Z ⊗₀ X ⊗₀ Y ⟩
                 associator.to
               ⟩

  module Properties where
    open MProperties M
    open Reasoning C
    open MonoidalReasoning

    hexagon-lemma : [ (X ⊗₀ unit) ⊗₀ unit ⇒ unit ⊗₀ X ]⟨
                      B  ⊗₁ id                    ⇒⟨ (unit ⊗₀ X) ⊗₀ unit ⟩
                      associator.from             ⇒⟨ unit ⊗₀ X ⊗₀ unit ⟩
                      id ⊗₁ B                     ⇒⟨ unit ⊗₀ unit ⊗₀ X ⟩
                      unitorˡ.from
                    ≈ unitorʳ.from                 ⇒⟨ X ⊗₀ unit ⟩
                      B
                    ⟩
    hexagon-lemma = begin
                    unitorˡ.from ∘ id ⊗₁ B ∘ associator.from ∘ B ⊗₁ id      ≈⟨ refl⟩∘⟨ hexagon₁ ⟩
                    unitorˡ.from ∘ associator.from ∘ B ∘ associator.from     ≈⟨ pullˡ coherence₁ ⟩
                    unitorˡ.from ⊗₁ id ∘ B ∘ associator.from                ≈⟨ pullˡ (⟺ B-commute) ⟩
                    (B ∘ id ⊗₁ unitorˡ.from) ∘ associator.from              ≈⟨ pullʳ triangle ⟩
                    B ∘ unitorʳ.from ⊗₁ id                                  ≈⟨ refl⟩∘⟨ unitor-coherenceʳ ⟩
                    B ∘ unitorʳ.from
                    ∎
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
        B ∘ unitorʳ.from                                                ≈˘⟨ refl⟩∘⟨ unitor-coherenceʳ ⟩
        B ∘ unitorʳ.from ⊗₁ id
      ∎)
