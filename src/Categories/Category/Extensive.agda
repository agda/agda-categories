{-# OPTIONS --without-K --safe #-}

module Categories.Category.Extensive where

-- https://ncatlab.org/nlab/show/extensive+category

open import Level
open import Function using (_$_)

open import Categories.Category.Core using (Category)
open import Categories.Diagram.Pullback using (Pullback; IsPullback; up-to-iso)
open import Categories.Diagram.Pullback.Properties using (module IsoPb)
open import Categories.Category.Cocartesian using (Cocartesian)
open import Categories.Object.Coproduct using (IsCoproduct)
open import Categories.Morphism
import Categories.Morphism.Reasoning as MR

record Extensive {o ℓ e : Level} (𝒞 : Category o ℓ e) : Set (suc (o ⊔ ℓ ⊔ e)) where
  open Category 𝒞
  open Pullback using (p₁)

  field
    cocartesian : Cocartesian 𝒞

  module CC = Cocartesian cocartesian
  open CC using (_+_; i₁; i₂; ¡)

  field
    pullback₁ : {A B C : Obj} (f : A ⇒ B + C) → Pullback 𝒞 f i₁
    pullback₂ : {A B C : Obj} (f : A ⇒ B + C) → Pullback 𝒞 f i₂
    pullback-of-cp-is-cp : {A B C : Obj} (f : A ⇒ B + C) → IsCoproduct 𝒞 (p₁ (pullback₁ f)) (p₁ (pullback₂ f))

    pullback₁-is-mono : ∀ {A B : Obj} → Mono 𝒞 (i₁ {A = A}{B = B})
    pullback₂-is-mono : ∀ {A B : Obj} → Mono 𝒞 (i₂ {A = A}{B = B})

    disjoint : ∀ {A B : Obj} → IsPullback 𝒞 ¡ ¡ (i₁ {A = A}{B = B}) i₂

  -- a version with non-canonical pullbacks
  module _ {A B C : Obj} {f : A ⇒ B + C} (pb₁ : Pullback 𝒞 f i₁) (pb₂ : Pullback 𝒞 f i₂) where
      private
        open IsCoproduct (pullback-of-cp-is-cp f)
        open HomReasoning; open MR 𝒞

        open IsoPb 𝒞 (pullback₁ f) pb₁ renaming (P₀⇒P₁ to pb₁-to-can; p₁-≈ to p₁-≈₁)
        open IsoPb 𝒞 (pullback₂ f) pb₂ renaming (P₀⇒P₁ to pb₂-to-can; p₁-≈ to p₁-≈₂)

        can-to-pb₁ = _≅_.from $ up-to-iso 𝒞 pb₁ (pullback₁ f)
        can-to-pb₂ = _≅_.from $ up-to-iso 𝒞 pb₂ (pullback₂ f)

      pullback-of-cp-is-cp' : IsCoproduct 𝒞 (p₁ pb₁) (p₁ pb₂)

      IsCoproduct.[_,_] pullback-of-cp-is-cp' g h  = [ g ∘ pb₁-to-can , h ∘ pb₂-to-can ]
      IsCoproduct.inject₁ pullback-of-cp-is-cp' {_}{g}{h}  = begin
         [ g ∘ pb₁-to-can , h ∘ pb₂-to-can ] ∘ p₁ pb₁                               ≈˘⟨ refl⟩∘⟨ cancelʳ (Iso.isoˡ $ _≅_.iso $ up-to-iso 𝒞 pb₁ (pullback₁ f)) ⟩
         [ g ∘ pb₁-to-can , h ∘ pb₂-to-can ] ∘ (p₁ pb₁ ∘ pb₁-to-can) ∘ can-to-pb₁    ≈⟨ refl⟩∘⟨ p₁-≈₁ ⟩∘⟨refl ⟩
         [ g ∘ pb₁-to-can , h ∘ pb₂-to-can ] ∘ p₁ (pullback₁ f) ∘ can-to-pb₁         ≈⟨ pullˡ inject₁ ⟩
         (g ∘ pb₁-to-can) ∘ can-to-pb₁                                               ≈⟨ cancelʳ (Iso.isoˡ $ _≅_.iso $ up-to-iso 𝒞 pb₁ (pullback₁ f)) ⟩
         g                                                                           ∎

      IsCoproduct.inject₂ pullback-of-cp-is-cp' {_}{g}{h} = begin
         [ g ∘ pb₁-to-can , h ∘ pb₂-to-can ] ∘ p₁ pb₂                               ≈˘⟨ refl⟩∘⟨ cancelʳ (Iso.isoˡ $ _≅_.iso $ up-to-iso 𝒞 pb₂ (pullback₂ f)) ⟩
         [ g ∘ pb₁-to-can , h ∘ pb₂-to-can ] ∘ (p₁ pb₂ ∘ pb₂-to-can) ∘ can-to-pb₂    ≈⟨ refl⟩∘⟨ p₁-≈₂ ⟩∘⟨refl ⟩
         [ g ∘ pb₁-to-can , h ∘ pb₂-to-can ] ∘ p₁ (pullback₂ f) ∘ can-to-pb₂         ≈⟨ pullˡ inject₂ ⟩
         (h ∘ pb₂-to-can) ∘ can-to-pb₂                                               ≈⟨ cancelʳ (Iso.isoˡ $ _≅_.iso $ up-to-iso 𝒞 pb₂ (pullback₂ f)) ⟩
         h                                                                           ∎

      IsCoproduct.unique pullback-of-cp-is-cp'   {_}{u}{g}{h}  u∘p₁pb₁≈g u∘p₁pb₂≈h  = unique
        (begin
                     u ∘ p₁ (pullback₁ f)            ≈˘⟨ pullʳ p₁-≈₁ ⟩
                     (u ∘ p₁ pb₁) ∘ pb₁-to-can       ≈⟨ u∘p₁pb₁≈g ⟩∘⟨refl ⟩
                     g ∘ pb₁-to-can                  ∎)
        (begin
                     u ∘ p₁ (pullback₂ f)           ≈˘⟨ pullʳ p₁-≈₂ ⟩
                     (u ∘ p₁ pb₂) ∘ pb₂-to-can       ≈⟨ u∘p₁pb₂≈h ⟩∘⟨refl ⟩
                     h ∘ pb₂-to-can                  ∎)

