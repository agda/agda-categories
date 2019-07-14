{-# OPTIONS --without-K --safe #-}
module Categories.Yoneda where

open import Level
-- open import Data.Product

open import Categories.Category using (Category; _[_,_])
open import Categories.Functor using (Functor)
open import Categories.Functor.Hom using (module Hom; Hom[_][-,_])
open import Categories.Category.Construction.Presheaves
open import Categories.NaturalTransformation using (NaturalTransformation)

-- The Yoneda embedding functor
embed : ∀ {o ℓ e} → (C : Category o ℓ e) → Functor C (Presheaves C)
embed C = record
  { F₀ = Hom[ C ][-,_]
  ; F₁ = Hom[A,C]⇒Hom[B,C] -- A⇒B induces a NatTrans on the Homs.
  ; identity = identityˡ ○_
  ; homomorphism = λ h₁≈h₂ → ∘-resp-≈ʳ h₁≈h₂ ○ assoc
  ; F-resp-≈ = λ f≈g h≈i → ∘-resp-≈ f≈g h≈i
  }
  where
    open Category C
    open HomReasoning
    -- This NaturalTransformation should probably got into NaturalTransformation.Hom,
    -- in analogy with Functor.Hom above
    Hom[A,C]⇒Hom[B,C] : {A B : Obj} → (A ⇒ B) → NaturalTransformation (Hom.Hom[-, C ] A) (Hom.Hom[-, C ] B)
    Hom[A,C]⇒Hom[B,C] {A} A⇒B = record
      { η = λ X → record { _⟨$⟩_ = λ X⇒A → A⇒B ∘ X⇒A ; cong = ∘-resp-≈ʳ }
      ; commute = λ {X} {Y} f {g} {h} g≈h → begin
          A⇒B ∘ id ∘ g ∘ f ≈˘⟨ assoc ⟩
          (A⇒B ∘ id) ∘ g ∘ f ≈⟨ ∘-resp-≈ id-comm (∘-resp-≈ˡ g≈h) ⟩
          (id ∘ A⇒B) ∘ h ∘ f ≈⟨ assoc ○ ⟺ (∘-resp-≈ʳ assoc) ⟩ -- TODO: MR.Reassociate
          id ∘ (A⇒B ∘ h) ∘ f ∎
      }

-- Using the adjunction between product and product, we get a kind of contravariant Bifunctor
