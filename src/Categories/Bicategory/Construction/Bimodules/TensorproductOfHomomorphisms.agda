{-# OPTIONS --without-K --safe --lossy-unification #-}

open import Categories.Bicategory
open import Categories.Bicategory.LocalCoequalizers
open import Categories.Bicategory.Monad
open import Categories.Bicategory.Monad.Bimodule
open import Categories.Bicategory.Monad.Bimodule.Homomorphism using (Bimodulehomomorphism)

module Categories.Bicategory.Construction.Bimodules.TensorproductOfHomomorphisms
  {o ℓ e t} {𝒞 : Bicategory o ℓ e t} {localCoeq : LocalCoequalizers 𝒞}
  {M₁ M₂ M₃ : Monad 𝒞} {B₂ B'₂ : Bimodule M₂ M₃} {B₁ B'₁ : Bimodule M₁ M₂}
  (h₂ : Bimodulehomomorphism B₂ B'₂) (h₁ : Bimodulehomomorphism B₁ B'₁) where

open import Level
import Categories.Category.Construction.Bimodules
open Categories.Category.Construction.Bimodules {o} {ℓ} {e} {t} {𝒞} renaming (Bimodules to Bimodules₁)
import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞
open import Categories.Category
open import Categories.Diagram.Coequalizer
import Categories.Diagram.Coequalizer.Properties as CoeqProperties

private
  module Bimodules₁ M₁ M₂ = Category (Bimodules₁ M₁ M₂)

open LocalCoequalizers localCoeq
open ComposeWithLocalCoequalizer 𝒞 localCoeq using (_coeq-◁_; _▷-coeq_)


open Monad M₁ using () renaming (C to C₁; T to T₁; μ to μ₁; η to η₁)
open Monad M₂ using () renaming (C to C₂; T to T₂; μ to μ₂; η to η₂)
open Monad M₃ using () renaming (C to C₃; T to T₃; μ to μ₃; η to η₃)
open Bimodule B₁ using () renaming (F to F₁; actionʳ to actionʳ₁; actionˡ to actionˡ₁)
open Bimodule B'₁ using () renaming (F to F'₁; actionʳ to actionʳ'₁; actionˡ to actionˡ'₁)
open Bimodule B₂ using () renaming (F to F₂; actionʳ to actionʳ₂; actionˡ to actionˡ₂)
open Bimodule B'₂ using () renaming (F to F'₂; actionʳ to actionʳ'₂; actionˡ to actionˡ'₂)
import Categories.Bicategory.Construction.Bimodules.TensorproductOfBimodules {𝒞 = 𝒞} {localCoeq} {M₁} {M₂} {M₃} as TensorproductOfBimodules
open TensorproductOfBimodules using (CoeqBimods)
open TensorproductOfBimodules B₂ B₁ using (B₂⊗B₁; act-to-the-left; act-to-the-right)
open TensorproductOfBimodules B'₂ B'₁ using ()
  renaming (B₂⊗B₁ to B'₂⊗B'₁; act-to-the-left to act-to-the-left'; act-to-the-right to act-to-the-right')
open Bimodule B₂⊗B₁ using (F; actionˡ; actionʳ)
open Bimodule B'₂⊗B'₁ using () renaming (F to F'; actionˡ to actionˡ'; actionʳ to actionʳ')
open Bimodulehomomorphism h₁ using () renaming (α to α₁; linearˡ to linearˡ₁; linearʳ to linearʳ₁)
open Bimodulehomomorphism h₂ using () renaming (α to α₂; linearˡ to linearˡ₂; linearʳ to linearʳ₂)

open Definitions (hom C₁ C₃) -- for Commutative Squares

sq₁ : CommutativeSquare (α₂ ⊚₁ id₂ ⊚₁ α₁)
                        (act-to-the-left)
                        (act-to-the-left')
                        (α₂ ⊚₁ α₁)
sq₁ = begin
  act-to-the-left' ∘ᵥ α₂ ⊚₁ id₂ ⊚₁ α₁ ≈⟨ ⟺ ∘ᵥ-distr-⊚ ⟩
  (id₂ ∘ᵥ α₂) ⊚₁ (actionʳ'₁ ∘ᵥ id₂ ⊚₁ α₁) ≈⟨ identity₂ˡ ⟩⊚⟨ linearʳ₁ ⟩
  α₂ ⊚₁ (α₁ ∘ᵥ actionʳ₁) ≈⟨ ⟺ identity₂ʳ ⟩⊚⟨refl ⟩
  (α₂ ∘ᵥ id₂) ⊚₁ (α₁ ∘ᵥ actionʳ₁) ≈⟨ ∘ᵥ-distr-⊚ ⟩
  α₂ ⊚₁ α₁ ∘ᵥ act-to-the-left ∎
  where
    open hom.HomReasoning

sq₂ : CommutativeSquare (α₂ ⊚₁ id₂ ⊚₁ α₁)
                        (act-to-the-right)
                        (act-to-the-right')
                        (α₂ ⊚₁ α₁)
sq₂ = begin
  act-to-the-right' ∘ᵥ α₂ ⊚₁ id₂ ⊚₁ α₁ ≈⟨ assoc₂ ⟩
  actionˡ'₂ ◁ F'₁ ∘ᵥ associator.to ∘ᵥ α₂ ⊚₁ id₂ ⊚₁ α₁ ≈⟨ refl⟩∘⟨ α⇐-⊚ ⟩
  actionˡ'₂ ◁ F'₁ ∘ᵥ (α₂ ⊚₁ id₂) ⊚₁ α₁ ∘ᵥ associator.to ≈⟨ sym-assoc₂ ⟩
  (actionˡ'₂ ◁ F'₁ ∘ᵥ (α₂ ⊚₁ id₂) ⊚₁ α₁) ∘ᵥ associator.to ≈⟨ ⟺ ∘ᵥ-distr-⊚ ⟩∘⟨refl ⟩
  ((actionˡ'₂ ∘ᵥ (α₂ ⊚₁ id₂)) ⊚₁ (id₂ ∘ᵥ α₁)) ∘ᵥ associator.to ≈⟨ linearˡ₂ ⟩⊚⟨refl ⟩∘⟨refl ⟩
  ((α₂ ∘ᵥ actionˡ₂) ⊚₁ (id₂ ∘ᵥ α₁)) ∘ᵥ associator.to ≈⟨ refl⟩⊚⟨ identity₂ˡ ⟩∘⟨refl ⟩
  ((α₂ ∘ᵥ actionˡ₂) ⊚₁ α₁) ∘ᵥ associator.to ≈⟨ refl⟩⊚⟨ ⟺ identity₂ʳ ⟩∘⟨refl ⟩
  ((α₂ ∘ᵥ actionˡ₂) ⊚₁ (α₁ ∘ᵥ id₂)) ∘ᵥ associator.to ≈⟨ ∘ᵥ-distr-⊚ ⟩∘⟨refl ⟩
  (α₂ ⊚₁ α₁ ∘ᵥ actionˡ₂ ◁ F₁) ∘ᵥ associator.to ≈⟨ assoc₂ ⟩
  α₂ ⊚₁ α₁ ∘ᵥ act-to-the-right ∎
  where
    open hom.HomReasoning

α : F ⇒₂ F'
α = ⇒MapBetweenCoeq (α₂ ⊚₁ id₂ ⊚₁  α₁) (α₂ ⊚₁ α₁) sq₁ sq₂ (CoeqBimods B₂ B₁) (CoeqBimods B'₂ B'₁)
  where
    open CoeqProperties (hom C₁ C₃)

αSq : CommutativeSquare (α₂ ⊚₁ α₁) (Coequalizer.arr (CoeqBimods B₂ B₁)) (Coequalizer.arr (CoeqBimods B'₂ B'₁)) α
αSq = ⇒MapBetweenCoeqSq (α₂ ⊚₁ id₂ ⊚₁  α₁) (α₂ ⊚₁ α₁) sq₁ sq₂ (CoeqBimods B₂ B₁) (CoeqBimods B'₂ B'₁)
  where
    open CoeqProperties (hom C₁ C₃)

open TensorproductOfBimodules.Left-Action B₂ B₁ using (F∘T₁Coequalizer; F₂▷actionˡ₁; actionˡSq)
open TensorproductOfBimodules.Left-Action B'₂ B'₁ using ()
  renaming (F₂▷actionˡ₁ to F'₂▷actionˡ'₁; actionˡSq to actionˡ'Sq)

linearˡ-square :  F'₂▷actionˡ'₁ ∘ᵥ (α₂ ⊚₁ α₁) ◁ T₁ ≈ (α₂ ⊚₁ α₁) ∘ᵥ F₂▷actionˡ₁
linearˡ-square = begin
  F'₂▷actionˡ'₁ ∘ᵥ (α₂ ⊚₁ α₁) ◁ T₁ ≈⟨ assoc₂ ⟩
  F'₂ ▷ actionˡ'₁ ∘ᵥ associator.from ∘ᵥ (α₂ ⊚₁ α₁) ◁ T₁ ≈⟨ refl⟩∘⟨ α⇒-⊚ ⟩
  F'₂ ▷ actionˡ'₁ ∘ᵥ α₂ ⊚₁ (α₁ ◁ T₁) ∘ᵥ associator.from ≈⟨ sym-assoc₂ ⟩
  (F'₂ ▷ actionˡ'₁ ∘ᵥ α₂ ⊚₁ (α₁ ◁ T₁)) ∘ᵥ associator.from ≈⟨ ⟺ ∘ᵥ-distr-⊚ ⟩∘⟨refl ⟩
  ((id₂ ∘ᵥ α₂) ⊚₁ (actionˡ'₁ ∘ᵥ α₁ ◁ T₁)) ∘ᵥ associator.from ≈⟨ identity₂ˡ ⟩⊚⟨ linearˡ₁ ⟩∘⟨refl ⟩
  (α₂ ⊚₁ (α₁ ∘ᵥ actionˡ₁)) ∘ᵥ associator.from ≈⟨ ⟺ identity₂ʳ ⟩⊚⟨refl ⟩∘⟨refl ⟩
  ((α₂ ∘ᵥ id₂) ⊚₁ (α₁ ∘ᵥ actionˡ₁)) ∘ᵥ associator.from ≈⟨ ∘ᵥ-distr-⊚ ⟩∘⟨refl ⟩
  ((α₂ ⊚₁ α₁) ∘ᵥ F₂ ▷ actionˡ₁) ∘ᵥ associator.from ≈⟨ assoc₂ ⟩
  (α₂ ⊚₁ α₁) ∘ᵥ F₂▷actionˡ₁ ∎
  where
    open hom.HomReasoning

linearˡ∘arr : (actionˡ' ∘ᵥ α ◁ T₁) ∘ᵥ Coequalizer.arr F∘T₁Coequalizer
              ≈ (α ∘ᵥ actionˡ) ∘ᵥ Coequalizer.arr F∘T₁Coequalizer
linearˡ∘arr = begin
  (actionˡ' ∘ᵥ α ◁ T₁) ∘ᵥ Coequalizer.arr F∘T₁Coequalizer ≈⟨ assoc₂ ⟩
  actionˡ' ∘ᵥ α ◁ T₁ ∘ᵥ Coequalizer.arr F∘T₁Coequalizer ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-◁ ⟩
  actionˡ' ∘ᵥ (α ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁)) ◁ T₁ ≈⟨ refl⟩∘⟨ ◁-resp-≈ (⟺ αSq) ⟩
  actionˡ' ∘ᵥ (Coequalizer.arr (CoeqBimods B'₂ B'₁) ∘ᵥ (α₂ ⊚₁ α₁)) ◁ T₁ ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-◁ ⟩
  actionˡ' ∘ᵥ Coequalizer.arr (CoeqBimods B'₂ B'₁) ◁ T₁ ∘ᵥ (α₂ ⊚₁ α₁) ◁ T₁ ≈⟨ sym-assoc₂ ⟩
  (actionˡ' ∘ᵥ Coequalizer.arr (CoeqBimods B'₂ B'₁) ◁ T₁) ∘ᵥ (α₂ ⊚₁ α₁) ◁ T₁ ≈⟨ ⟺ actionˡ'Sq ⟩∘⟨refl ⟩
  (Coequalizer.arr (CoeqBimods B'₂ B'₁) ∘ᵥ F'₂▷actionˡ'₁) ∘ᵥ (α₂ ⊚₁ α₁) ◁ T₁ ≈⟨ assoc₂ ⟩
  Coequalizer.arr (CoeqBimods B'₂ B'₁) ∘ᵥ F'₂▷actionˡ'₁ ∘ᵥ (α₂ ⊚₁ α₁) ◁ T₁ ≈⟨ refl⟩∘⟨ linearˡ-square ⟩
  Coequalizer.arr (CoeqBimods B'₂ B'₁) ∘ᵥ (α₂ ⊚₁ α₁) ∘ᵥ F₂▷actionˡ₁ ≈⟨ sym-assoc₂ ⟩
  (Coequalizer.arr (CoeqBimods B'₂ B'₁) ∘ᵥ (α₂ ⊚₁ α₁)) ∘ᵥ F₂▷actionˡ₁ ≈⟨ αSq ⟩∘⟨refl ⟩
  (α ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁)) ∘ᵥ F₂▷actionˡ₁ ≈⟨ assoc₂ ⟩
  α ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁) ∘ᵥ F₂▷actionˡ₁ ≈⟨ refl⟩∘⟨ actionˡSq ⟩
  α ∘ᵥ actionˡ ∘ᵥ Coequalizer.arr F∘T₁Coequalizer ≈⟨ sym-assoc₂ ⟩
  (α ∘ᵥ actionˡ) ∘ᵥ Coequalizer.arr F∘T₁Coequalizer ∎
  where
    open hom.HomReasoning

linearˡ : actionˡ' ∘ᵥ α ◁ T₁ ≈ α ∘ᵥ actionˡ
linearˡ = Coequalizer⇒Epi (hom C₁ C₃) F∘T₁Coequalizer
                          (actionˡ' ∘ᵥ α ◁ T₁) (α ∘ᵥ actionˡ)
                          linearˡ∘arr


open TensorproductOfBimodules.Right-Action B₂ B₁ using (T₃∘FCoequalizer; actionʳ₂◁F₁; actionʳSq)
open TensorproductOfBimodules.Right-Action B'₂ B'₁ using () renaming (actionʳ₂◁F₁ to actionʳ'₂◁F'₁; actionʳSq to actionʳ'Sq)

linearʳ-square : actionʳ'₂◁F'₁ ∘ᵥ T₃ ▷ (α₂ ⊚₁ α₁) ≈ (α₂ ⊚₁ α₁) ∘ᵥ actionʳ₂◁F₁
linearʳ-square = begin
  actionʳ'₂◁F'₁ ∘ᵥ T₃ ▷ (α₂ ⊚₁ α₁) ≈⟨ assoc₂ ⟩
  actionʳ'₂ ◁ F'₁ ∘ᵥ associator.to ∘ᵥ T₃ ▷ (α₂ ⊚₁ α₁) ≈⟨ refl⟩∘⟨ α⇐-⊚ ⟩
  actionʳ'₂ ◁ F'₁ ∘ᵥ ((T₃ ▷ α₂) ⊚₁ α₁) ∘ᵥ associator.to ≈⟨ sym-assoc₂ ⟩
  (actionʳ'₂ ◁ F'₁ ∘ᵥ ((T₃ ▷ α₂) ⊚₁ α₁)) ∘ᵥ associator.to ≈⟨ ⟺ ∘ᵥ-distr-⊚ ⟩∘⟨refl ⟩
  ((actionʳ'₂ ∘ᵥ T₃ ▷ α₂) ⊚₁ (id₂ ∘ᵥ α₁)) ∘ᵥ associator.to ≈⟨ linearʳ₂ ⟩⊚⟨ identity₂ˡ ⟩∘⟨refl ⟩
  ((α₂ ∘ᵥ actionʳ₂) ⊚₁ α₁) ∘ᵥ associator.to ≈⟨ refl⟩⊚⟨ ⟺ identity₂ʳ ⟩∘⟨refl ⟩
  ((α₂ ∘ᵥ actionʳ₂) ⊚₁ (α₁ ∘ᵥ id₂)) ∘ᵥ associator.to ≈⟨ ∘ᵥ-distr-⊚ ⟩∘⟨refl ⟩
  ((α₂ ⊚₁ α₁) ∘ᵥ actionʳ₂ ◁ F₁) ∘ᵥ associator.to ≈⟨ assoc₂ ⟩
  (α₂ ⊚₁ α₁) ∘ᵥ actionʳ₂◁F₁ ∎
  where
    open hom.HomReasoning

linearʳ∘arr : (actionʳ' ∘ᵥ T₃ ▷ α) ∘ᵥ Coequalizer.arr T₃∘FCoequalizer ≈ (α ∘ᵥ actionʳ) ∘ᵥ Coequalizer.arr T₃∘FCoequalizer
linearʳ∘arr = begin
  (actionʳ' ∘ᵥ T₃ ▷ α) ∘ᵥ Coequalizer.arr T₃∘FCoequalizer ≈⟨ assoc₂ ⟩
  actionʳ' ∘ᵥ T₃ ▷ α ∘ᵥ Coequalizer.arr T₃∘FCoequalizer ≈⟨ refl⟩∘⟨ ∘ᵥ-distr-▷ ⟩
  actionʳ' ∘ᵥ T₃ ▷ (α ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁)) ≈⟨ refl⟩∘⟨ ▷-resp-≈ (⟺ αSq) ⟩
  actionʳ' ∘ᵥ T₃ ▷ (Coequalizer.arr (CoeqBimods B'₂ B'₁) ∘ᵥ (α₂ ⊚₁ α₁)) ≈⟨ refl⟩∘⟨ ⟺ ∘ᵥ-distr-▷ ⟩
  actionʳ' ∘ᵥ T₃ ▷ Coequalizer.arr (CoeqBimods B'₂ B'₁) ∘ᵥ T₃ ▷ (α₂ ⊚₁ α₁) ≈⟨ sym-assoc₂ ⟩
  (actionʳ' ∘ᵥ T₃ ▷ Coequalizer.arr (CoeqBimods B'₂ B'₁)) ∘ᵥ T₃ ▷ (α₂ ⊚₁ α₁) ≈⟨ ⟺ actionʳ'Sq ⟩∘⟨refl ⟩
  (Coequalizer.arr (CoeqBimods B'₂ B'₁) ∘ᵥ actionʳ'₂◁F'₁) ∘ᵥ T₃ ▷ (α₂ ⊚₁ α₁) ≈⟨ assoc₂ ⟩
  Coequalizer.arr (CoeqBimods B'₂ B'₁) ∘ᵥ actionʳ'₂◁F'₁ ∘ᵥ T₃ ▷ (α₂ ⊚₁ α₁) ≈⟨ refl⟩∘⟨ linearʳ-square ⟩
  Coequalizer.arr (CoeqBimods B'₂ B'₁) ∘ᵥ (α₂ ⊚₁ α₁) ∘ᵥ actionʳ₂◁F₁ ≈⟨ sym-assoc₂ ⟩
  (Coequalizer.arr (CoeqBimods B'₂ B'₁) ∘ᵥ (α₂ ⊚₁ α₁)) ∘ᵥ actionʳ₂◁F₁ ≈⟨ αSq ⟩∘⟨refl ⟩
  (α ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁)) ∘ᵥ actionʳ₂◁F₁ ≈⟨ assoc₂ ⟩
  α ∘ᵥ Coequalizer.arr (CoeqBimods B₂ B₁) ∘ᵥ actionʳ₂◁F₁ ≈⟨ refl⟩∘⟨ actionʳSq ⟩
  α ∘ᵥ actionʳ ∘ᵥ Coequalizer.arr T₃∘FCoequalizer ≈⟨ sym-assoc₂ ⟩
  (α ∘ᵥ actionʳ) ∘ᵥ Coequalizer.arr T₃∘FCoequalizer ∎
  where
    open hom.HomReasoning

linearʳ : actionʳ' ∘ᵥ T₃ ▷ α ≈ α ∘ᵥ actionʳ
linearʳ = Coequalizer⇒Epi (hom C₁ C₃) T₃∘FCoequalizer
                          (actionʳ' ∘ᵥ T₃ ▷ α) (α ∘ᵥ actionʳ)
                          linearʳ∘arr

h₂⊗h₁ : Bimodulehomomorphism B₂⊗B₁ B'₂⊗B'₁
h₂⊗h₁ = record
  { α = α
  ; linearˡ = linearˡ
  ; linearʳ = linearʳ
  }
