{-# OPTIONS --without-K --safe #-}

module Categories.NaturalTransformation.NaturalIsomorphism.Properties where

open import Level

open import Categories.Category
open import Categories.Functor renaming (id to idF)
open import Categories.NaturalTransformation.NaturalIsomorphism

import Categories.Morphism as Mor
import Categories.Morphism.Properties as Morₚ
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level
    C D : Category o ℓ e



module _ {F G : Functor C D} (α : NaturalIsomorphism F G) where
  private module C = Category C
  open Category D
  open Mor D
  private module MRD = MR D
  open Functor F
  open Functor G renaming (F₀ to G₀; F₁ to G₁)
  open NaturalIsomorphism α

  -- We can move equations along natural isomorphism.

  module _ {A B} {f g : A C.⇒ B} where

    push-eq : F₁ f ≈ F₁ g → G₁ f ≈ G₁ g
    push-eq hyp = MRD.push-eq FX≅GX (⇒.commute f) (⇒.commute g) hyp

    pull-eq : G₁ f ≈ G₁ g → F₁ f ≈ F₁ g
    pull-eq hyp = MRD.push-eq (≅.sym FX≅GX) (⇐.commute f) (⇐.commute g) hyp

-- properties of natural isomorphisms over an endofunctor
module _ {F : Endofunctor C} where
  private
    module C = Category C
    module F = Functor F
    module MC = Mor C

  module _ (α : F ≃ idF) where
    open C
    open HomReasoning
    open F
    open MC
    open MR C
    open Mor C
    open Morₚ C
    open NaturalIsomorphism α

    F≃id-comm₁ : ∀ {A} → ⇒.η (F₀ A) ≈ F₁ (⇒.η A)
    F≃id-comm₁ {A} = begin
      ⇒.η (F₀ A)                           ≈⟨ introʳ (F-resp-≈ (iso.isoˡ _) ○ identity) ⟩
      ⇒.η (F₀ A) ∘ F₁ (⇐.η A ∘ ⇒.η A)      ≈⟨ refl⟩∘⟨ homomorphism ⟩
      ⇒.η (F₀ A) ∘ F₁ (⇐.η A) ∘ F₁ (⇒.η A) ≈⟨ cancelˡ (⇒.commute _ ○ iso.isoˡ _) ⟩
      F₁ (⇒.η A)                           ∎

    F≃id-comm₂ : ∀ {A} → ⇐.η (F₀ A) ≈ F₁ (⇐.η A)
    F≃id-comm₂ {A} = begin
      ⇐.η (F₀ A)                             ≈⟨ introˡ (F-resp-≈ (iso.isoˡ _) ○ identity) ⟩
      F₁ (⇐.η A ∘ ⇒.η A) ∘ ⇐.η (F₀ A)        ≈⟨ homomorphism ⟩∘⟨refl ⟩
      (F₁ (⇐.η A) ∘ F₁ (⇒.η A)) ∘ ⇐.η (F₀ A) ≈⟨ cancelʳ (⟺ (⇐.commute _) ○ iso.isoˡ _) ⟩
      F₁ (⇐.η A)                             ∎

    F≃id⇒id : ∀ {A} {f : A ⇒ A} → F₁ f ≈ id → f ≈ id
    F≃id⇒id {A} {f} eq = Iso⇒Mono (Iso-swap (iso A)) _ _ helper
      where helper : ⇐.η A ∘ f ≈ ⇐.η A ∘ id
            helper = begin
              ⇐.η A ∘ f    ≈⟨ ⇐.commute f ⟩
              F₁ f ∘ ⇐.η A ≈⟨ eq ⟩∘⟨refl ⟩
              id ∘ ⇐.η A   ≈˘⟨ id-comm ⟩
              ⇐.η A ∘ id   ∎
