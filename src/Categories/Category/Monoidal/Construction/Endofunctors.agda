{-# OPTIONS --without-K --safe #-}
open import Categories.Category using (Category; _[_,_])

-- The functor category [ C , C ] with functor composition as its tensor.

module Categories.Category.Monoidal.Construction.Endofunctors
  {o ℓ e} (C : Category o ℓ e) where

open import Level using (_⊔_)

open import Categories.Category.Construction.Functors using (Functors; product)
open import Categories.Category.Monoidal
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning as MorphismReasoning
import Categories.NaturalTransformation.NaturalIsomorphism as NI
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.NaturalTransformation.NaturalIsomorphism.Functors
  using (NI⇒Functors-iso)

private [C,C] = Functors C C
open Functor renaming (F₀ to _$₀_; F₁ to _$₁_)
open NI.NaturalIsomorphism
open NaturalTransformation
open Morphism [C,C] using (_≅_)
open Category C
open HomReasoning
open MorphismReasoning C

Endofunctors-Monoidal : Monoidal [C,C]
Endofunctors-Monoidal = monoidalHelper [C,C] (record
  { ⊗               = product
  ; unit            = idF
  ; unitorˡ         = NI⇒Functors-iso NI.unitorˡ
  ; unitorʳ         = NI⇒Functors-iso NI.unitorʳ
  ; associator      = λ {F G H} → NI⇒Functors-iso (NI.associator H G F)
  ; unitorˡ-commute = identityˡ
  ; unitorʳ-commute = λ {_ _ α} → unitorʳ-commute α
  ; assoc-commute   = λ {_ _ α _ _ β _ _ γ} → assoc-commute α β γ
  ; triangle        = identityʳ
  ; pentagon        = λ {F G H I} → pentagon F G H
  })
  where
    unitorʳ-commute : ∀ {F G : Functor C C} (α : [C,C] [ F , G ]) {X} →
                      id ∘ G $₁ id ∘ η α X ≈ η α X ∘ id
    unitorʳ-commute {F} {G} α {X} = begin
      id ∘ G $₁ id ∘ η α X   ≈⟨ refl⟩∘⟨ elimˡ (identity G) ⟩
      id ∘ η α X             ≈⟨ id-comm-sym ⟩
      η α X ∘ id             ∎

    assoc-commute : ∀ {F₁ F₂ G₁ G₂ H₁ H₂} (α : [C,C] [ F₁ , F₂ ])
                      (β : [C,C] [ G₁ , G₂ ]) (γ : [C,C] [ H₁ , H₂ ]) {X} →
                    id ∘ F₂ $₁ (G₂ $₁ (η γ X)) ∘
                    F₂ $₁ (η β (H₁ $₀ X)) ∘ η α (G₁ $₀ (H₁ $₀ X))
                    ≈
                    ((F₂ $₁ (G₂ $₁ (η γ X) ∘ η β (H₁ $₀ X))) ∘
                    η α (G₁ $₀ (H₁ $₀ X))) ∘ id
    assoc-commute {F₁} {F₂} {G₁} {G₂} {H₁} {H₂} α β γ = begin
      id ∘ F₂ $₁ (G₂ $₁ (η γ _)) ∘ F₂ $₁ (η β _) ∘ η α _  ≈˘⟨ refl⟩∘⟨ pushˡ (homomorphism F₂) ⟩
      id ∘ (F₂ $₁ (G₂ $₁ (η γ _) ∘ η β _)) ∘ η α _        ≈⟨ id-comm-sym ⟩
      ((F₂ $₁ (G₂ $₁ (η γ _) ∘ η β _)) ∘ η α _) ∘ id      ∎

    pentagon : ∀ (F G H : Functor C C) {X} →
               ((F $₁ id) ∘ id) ∘ id ∘ (F $₁ (G $₁ (H $₁ id))) ∘ id ≈
               id ∘ id {F $₀ (G $₀ (H $₀ X))}
    pentagon F G H = begin
        ((F $₁ id) ∘ id) ∘ id ∘ (F $₁ (G $₁ (H $₁ id))) ∘ id
      ≈⟨ elimˡ (identity F) ⟩∘⟨ refl⟩∘⟨ F-resp-≈ F (F-resp-≈ G (identity H)) ⟩∘⟨refl ⟩
        id ∘ id ∘ (F $₁ (G $₁ id)) ∘ id
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ F-resp-≈ F (identity G) ⟩∘⟨refl ⟩
        id ∘ id ∘ (F $₁ id) ∘ id
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ elimˡ (identity F) ⟩
        id ∘ id ∘ id
      ≈⟨ identityˡ ⟩
        id ∘ id
      ∎

Endofunctors : MonoidalCategory (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) (o ⊔ e)
Endofunctors = record { U = [C,C] ; monoidal = Endofunctors-Monoidal }
