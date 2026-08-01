{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Interchange using (HasInterchange)

-- The tensor product of enriched categories.  Composition exchanges the two
-- middle hom objects once, then composes independently in each factor.

module Categories.Enriched.Category.TensorProduct
  {o ℓ e} {V : Category o ℓ e} {M : Monoidal V} (I : HasInterchange M) where

open import Level using (_⊔_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open Category V renaming (id to idV)
open Monoidal M
open HasInterchange I using (module swapInner)
  renaming (natural to int-natural; assoc to int-assoc; unitˡ to int-unitˡ; unitʳ to int-unitʳ)
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Utilities M
open import Categories.Morphism.Reasoning V
import Categories.Enriched.Category as Enriched
open Shorthands

private
  i⇒ = swapInner.from

module _ {a b} (𝒜 : Enriched.Category M a) (ℬ : Enriched.Category M b) where

  infixr 7 _⊠_

  private
    module 𝒜 = Enriched.Category 𝒜
    module ℬ = Enriched.Category ℬ

    variable
      A B C Z : 𝒜.Obj × ℬ.Obj -- source, intermediate, and target pairs

    hom : 𝒜.Obj × ℬ.Obj → 𝒜.Obj × ℬ.Obj → Category.Obj V
    hom A B = 𝒜.hom (proj₁ A) (proj₁ B) ⊗₀ ℬ.hom (proj₂ A) (proj₂ B)

    id× : unit ⇒ hom A A
    id× = (𝒜.id ⊗₁ ℬ.id) ∘ λ⇐

    ⊚× : hom B C ⊗₀ hom A B ⇒ hom A C
    ⊚× = (𝒜.⊚ ⊗₁ ℬ.⊚) ∘ i⇒

  private abstract
    ⊚×-assoc : ⊚× {B} {Z} {A} ∘ (⊚× {C} ⊗₁ idV)
               ≈ ⊚× ∘ (idV ⊗₁ ⊚×) ∘ α⇒
    ⊚×-assoc = begin
      ⊚× ∘ (⊚× ⊗₁ idV)                                   ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
      ⊚× ∘ ((𝒜.⊚ ⊗₁ ℬ.⊚) ⊗₁ idV) ∘ (i⇒ ⊗₁ idV)          ≈˘⟨ refl⟩∘⟨ refl⟩⊗⟨ ⊗.identity ⟩∘⟨refl ⟩
      ⊚× ∘ ((𝒜.⊚ ⊗₁ ℬ.⊚) ⊗₁ (idV ⊗₁ idV)) ∘ (i⇒ ⊗₁ idV) ≈⟨ extend² int-natural ⟩
      ((𝒜.⊚ ⊗₁ ℬ.⊚) ∘ ((𝒜.⊚ ⊗₁ idV) ⊗₁ (ℬ.⊚ ⊗₁ idV)))
        ∘ (i⇒ ∘ (i⇒ ⊗₁ idV))
        ≈⟨ parallel 𝒜.⊚-assoc ℬ.⊚-assoc ⟩∘⟨refl ⟩
      ((𝒜.⊚ ⊗₁ ℬ.⊚) ∘
        (((idV ⊗₁ 𝒜.⊚) ∘ α⇒) ⊗₁ ((idV ⊗₁ ℬ.⊚) ∘ α⇒)))
        ∘ (i⇒ ∘ (i⇒ ⊗₁ idV))
        ≈⟨ pullʳ (pushˡ ⊗.homomorphism) ⟩
      (𝒜.⊚ ⊗₁ ℬ.⊚) ∘
        ((idV ⊗₁ 𝒜.⊚) ⊗₁ (idV ⊗₁ ℬ.⊚)) ∘
        (α⇒ ⊗₁ α⇒) ∘ i⇒ ∘ (i⇒ ⊗₁ idV)
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ int-assoc ⟩
      (𝒜.⊚ ⊗₁ ℬ.⊚) ∘
        ((idV ⊗₁ 𝒜.⊚) ⊗₁ (idV ⊗₁ ℬ.⊚)) ∘
        i⇒ ∘ (idV ⊗₁ i⇒) ∘ α⇒
        ≈˘⟨ refl⟩∘⟨ extendʳ int-natural ⟩
      (𝒜.⊚ ⊗₁ ℬ.⊚) ∘ i⇒ ∘
        ((idV ⊗₁ idV) ⊗₁ (𝒜.⊚ ⊗₁ ℬ.⊚)) ∘ (idV ⊗₁ i⇒) ∘ α⇒
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ merge₂ʳ ⟩
      (𝒜.⊚ ⊗₁ ℬ.⊚) ∘ i⇒ ∘ ((idV ⊗₁ idV) ⊗₁ ⊚×) ∘ α⇒
        ≈⟨ pushʳ (refl⟩∘⟨ ⊗.identity ⟩⊗⟨refl ⟩∘⟨refl) ⟩
      ⊚× ∘ (idV ⊗₁ ⊚×) ∘ α⇒  ∎

    ⊚×-unitˡ : ⊚× {B} {B} {A} ∘ (id× ⊗₁ idV) ≈ λ⇒
    ⊚×-unitˡ = begin
      ⊚× ∘ (id× ⊗₁ idV)                                   ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
      ⊚× ∘ ((𝒜.id ⊗₁ ℬ.id) ⊗₁ idV) ∘ (λ⇐ ⊗₁ idV)          ≈˘⟨ refl⟩∘⟨ refl⟩⊗⟨ ⊗.identity ⟩∘⟨refl ⟩
      ⊚× ∘ ((𝒜.id ⊗₁ ℬ.id) ⊗₁ (idV ⊗₁ idV)) ∘ (λ⇐ ⊗₁ idV) ≈⟨ extend² int-natural ⟩
      ((𝒜.⊚ ⊗₁ ℬ.⊚) ∘ ((𝒜.id ⊗₁ idV) ⊗₁ (ℬ.id ⊗₁ idV)))
        ∘ (i⇒ ∘ (λ⇐ ⊗₁ idV))
        ≈˘⟨ ⊗.homomorphism ⟩∘⟨refl ⟩
      ((𝒜.⊚ ∘ (𝒜.id ⊗₁ idV)) ⊗₁ (ℬ.⊚ ∘ (ℬ.id ⊗₁ idV)))
        ∘ (i⇒ ∘ (λ⇐ ⊗₁ idV))
        ≈⟨ 𝒜.unitˡ ⟩⊗⟨ ℬ.unitˡ ⟩∘⟨refl ⟩
      (λ⇒ ⊗₁ λ⇒) ∘ i⇒ ∘ (λ⇐ ⊗₁ idV)                       ≈⟨ int-unitˡ ⟩
      λ⇒                                                  ∎

    ⊚×-unitʳ : ⊚× {A} {B} ∘ (idV ⊗₁ id×) ≈ ρ⇒
    ⊚×-unitʳ = begin
      ⊚× ∘ (idV ⊗₁ id×)                                   ≈⟨ refl⟩∘⟨ split₂ˡ ⟩
      ⊚× ∘ (idV ⊗₁ (𝒜.id ⊗₁ ℬ.id)) ∘ (idV ⊗₁ λ⇐)          ≈˘⟨ refl⟩∘⟨ ⊗.identity ⟩⊗⟨refl ⟩∘⟨refl ⟩
      ⊚× ∘ ((idV ⊗₁ idV) ⊗₁ (𝒜.id ⊗₁ ℬ.id)) ∘ (idV ⊗₁ λ⇐) ≈⟨ extend² int-natural ⟩
      ((𝒜.⊚ ⊗₁ ℬ.⊚) ∘ ((idV ⊗₁ 𝒜.id) ⊗₁ (idV ⊗₁ ℬ.id)))
        ∘ (i⇒ ∘ (idV ⊗₁ λ⇐))
        ≈˘⟨ ⊗.homomorphism ⟩∘⟨refl ⟩
      ((𝒜.⊚ ∘ (idV ⊗₁ 𝒜.id)) ⊗₁ (ℬ.⊚ ∘ (idV ⊗₁ ℬ.id)))
        ∘ (i⇒ ∘ (idV ⊗₁ λ⇐))
        ≈⟨ 𝒜.unitʳ ⟩⊗⟨ ℬ.unitʳ ⟩∘⟨refl ⟩
      (ρ⇒ ⊗₁ ρ⇒) ∘ i⇒ ∘ (idV ⊗₁ λ⇐)  ≈⟨ int-unitʳ ⟩
      ρ⇒                                                       ∎

  _⊠_ : Enriched.Category M (a ⊔ b)
  _⊠_ = record
    { Obj = 𝒜.Obj × ℬ.Obj
    ; hom = hom
    ; id = id×
    ; ⊚ = ⊚×
    ; ⊚-assoc = ⊚×-assoc
    ; unitˡ = ⊚×-unitˡ
    ; unitʳ = ⊚×-unitʳ
    }
