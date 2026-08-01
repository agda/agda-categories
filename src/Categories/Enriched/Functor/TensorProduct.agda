{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (module Commutation) renaming (Category to Setoid-Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Interchange using (HasInterchange)

-- Tensor products of enriched functors.

module Categories.Enriched.Functor.TensorProduct
  {o ℓ e} {V : Setoid-Category o ℓ e} {M : Monoidal V} (I : HasInterchange M) where

open import Data.Product using (_,_)

import Categories.Enriched.Category as Enriched
open Enriched using () renaming (Category to EnrichedCat)
open import Categories.Enriched.Category M using (_[_,_])
open import Categories.Enriched.Functor as EnrichedFunctor renaming (Functor to EnrichedFunctor)

open Setoid-Category V
open Commutation V
open Monoidal M
open HasInterchange I using (module swapInner) renaming (natural to interchange-natural)
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Utilities M
open import Categories.Enriched.Category.TensorProduct I using (_⊠_)
open import Categories.Morphism.Reasoning V
open Shorthands

private
  i⇒ = swapInner.from

module _ {a b c d}
        {𝒜 : EnrichedCat M a} {ℬ : EnrichedCat M b}
        {𝒞 : EnrichedCat M c} {𝒟 : EnrichedCat M d}
        where

  infixr 7 _⊠F_

  private
    module 𝒜 = EnrichedCat 𝒜
    module ℬ = EnrichedCat ℬ
    module 𝒞 = EnrichedCat 𝒞
    module 𝒟 = EnrichedCat 𝒟

  _⊠F_ : (F : EnrichedFunctor M 𝒜 𝒞) (G : EnrichedFunctor M ℬ 𝒟) →
         EnrichedFunctor M (𝒜 ⊠ ℬ) (𝒞 ⊠ 𝒟)
  F ⊠F G = record
    { map₀ = λ (A , B) → F.₀ A , G.₀ B
    ; map₁ = F.₁ ⊗₁ G.₁
    ; identity = identity
    ; homomorphism = homomorphism
    }
    where
    module F = EnrichedFunctor.Functor F
    module G = EnrichedFunctor.Functor G
    module 𝒜⊠ℬ = EnrichedCat (𝒜 ⊠ ℬ)
    module 𝒞⊠𝒟 = EnrichedCat (𝒞 ⊠ 𝒟)

    variable
      A B C : 𝒜.Obj
      X Y Z : ℬ.Obj

    abstract
      identity : (F.₁ ⊗₁ G.₁) ∘ 𝒜⊠ℬ.id {A , X} ≈ 𝒞⊠𝒟.id
      identity = begin
        (F.₁ ⊗₁ G.₁) ∘ (𝒜.id ⊗₁ ℬ.id) ∘ λ⇐    ≈⟨ pullˡ (⟺ ⊗.homomorphism) ⟩
        ((F.₁ ∘ 𝒜.id) ⊗₁ (G.₁ ∘ ℬ.id)) ∘ λ⇐   ≈⟨ F.identity ⟩⊗⟨ G.identity ⟩∘⟨refl ⟩
        (𝒞.id ⊗₁ 𝒟.id) ∘ λ⇐                   ∎

      homomorphism :
        [ (𝒜 [ B , C ] ⊗₀ ℬ [ Y , Z ]) ⊗₀ (𝒜 [ A , B ] ⊗₀ ℬ [ X , Y ]) ⇒
          𝒞 [ F.₀ A , F.₀ C ] ⊗₀ 𝒟 [ G.₀ X , G.₀ Z ] ]⟨
            𝒜⊠ℬ.⊚         ⇒⟨ 𝒜 [ A , C ] ⊗₀ ℬ [ X , Z ] ⟩
            F.₁ ⊗₁ G.₁
          ≈ (F.₁ ⊗₁ G.₁) ⊗₁ (F.₁ ⊗₁ G.₁)
                            ⇒⟨ (𝒞 [ F.₀ B , F.₀ C ] ⊗₀ 𝒟 [ G.₀ Y , G.₀ Z ]) ⊗₀
                                (𝒞 [ F.₀ A , F.₀ B ] ⊗₀ 𝒟 [ G.₀ X , G.₀ Y ]) ⟩
            𝒞⊠𝒟.⊚
          ⟩
      homomorphism = let F⊗G-homo = F.homomorphism ⟩⊗⟨ G.homomorphism in begin
        (F.₁ ⊗₁ G.₁) ∘ (𝒜.⊚ ⊗₁ ℬ.⊚) ∘ i⇒                      ≈⟨ pullˡ (⟺ ⊗.homomorphism) ⟩
        ((F.₁ ∘ 𝒜.⊚) ⊗₁ (G.₁ ∘ ℬ.⊚)) ∘ i⇒                     ≈⟨ F⊗G-homo ⟩∘⟨refl ⟩
        ((𝒞.⊚ ∘ (F.₁ ⊗₁ F.₁)) ⊗₁ (𝒟.⊚ ∘ (G.₁ ⊗₁ G.₁))) ∘ i⇒   ≈⟨ pushˡ ⊗.homomorphism ⟩
        (𝒞.⊚ ⊗₁ 𝒟.⊚) ∘ (((F.₁ ⊗₁ F.₁) ⊗₁ (G.₁ ⊗₁ G.₁)) ∘ i⇒)  ≈⟨ pushʳ (⟺ interchange-natural) ⟩
        𝒞⊠𝒟.⊚ ∘ ((F.₁ ⊗₁ G.₁) ⊗₁ (F.₁ ⊗₁ G.₁)) ∎
