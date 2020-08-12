{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Hom where

-- The Hom Functor from C.op × C to Setoids,
-- the two 1-argument version fixing one object
-- and some notation for the version where the category must be made explicit

open import Data.Product
open import Function using () renaming (_∘_ to _∙_)

open import Categories.Category
open import Categories.Functor hiding (id)
open import Categories.Functor.Properties
open import Categories.Functor.Bifunctor
open import Categories.Category.Instance.Setoids
import Categories.Morphism.Reasoning as MR

open import Relation.Binary using (Setoid)

module Hom {o ℓ e} (C : Category o ℓ e) where
  open Category C
  open MR C

  Hom[-,-] : Bifunctor (Category.op C) C (Setoids ℓ e)
  Hom[-,-] = record
    { F₀           = F₀′
    ; F₁           = λ where
      (f , g) → record
        { _⟨$⟩_ = λ h → g ∘ h ∘ f
        ; cong  = ∘-resp-≈ʳ ∙ ∘-resp-≈ˡ
        }
    ; identity     = identity′
    ; homomorphism = homomorphism′
    ; F-resp-≈     = F-resp-≈′
    }
    where F₀′ : Obj × Obj → Setoid ℓ e
          F₀′ (A , B) = hom-setoid {A} {B}
          open HomReasoning

          identity′ : {A : Obj × Obj} {x y : uncurry _⇒_ A} → x ≈ y → id ∘ x ∘ id ≈ y
          identity′ {A} {x} {y} x≈y = begin
            id ∘ x ∘ id ≈⟨ identityˡ ⟩
            x ∘ id      ≈⟨ identityʳ ⟩
            x           ≈⟨ x≈y ⟩
            y           ∎

          homomorphism′ : ∀ {X Y Z : Σ Obj (λ x → Obj)}
                            {f : proj₁ Y ⇒ proj₁ X × proj₂ X ⇒ proj₂ Y}
                            {g : proj₁ Z ⇒ proj₁ Y × proj₂ Y ⇒ proj₂ Z}
                            {x y : proj₁ X ⇒ proj₂ X} →
                            x ≈ y →
                            (proj₂ g ∘ proj₂ f) ∘ x ∘ proj₁ f ∘ proj₁ g ≈
                            proj₂ g ∘ (proj₂ f ∘ y ∘ proj₁ f) ∘ proj₁ g
          homomorphism′ {f = f₁ , f₂} {g₁ , g₂} {x} {y} x≈y = begin
            (g₂ ∘ f₂) ∘ x ∘ f₁ ∘ g₁   ≈⟨ refl⟩∘⟨ sym-assoc ⟩
            (g₂ ∘ f₂) ∘ (x ∘ f₁) ∘ g₁ ≈⟨ pullʳ (pullˡ (∘-resp-≈ʳ (∘-resp-≈ˡ x≈y))) ⟩
            g₂ ∘ (f₂ ∘ y ∘ f₁) ∘ g₁   ∎

          F-resp-≈′ : ∀ {A B : Σ Obj (λ x → Obj)}
                        {f g : Σ (proj₁ B ⇒ proj₁ A) (λ x → proj₂ A ⇒ proj₂ B)} →
                        Σ (proj₁ f ≈ proj₁ g) (λ x → proj₂ f ≈ proj₂ g) →
                        {x y : proj₁ A ⇒ proj₂ A} →
                        x ≈ y → proj₂ f ∘ x ∘ proj₁ f ≈ proj₂ g ∘ y ∘ proj₁ g
          F-resp-≈′ {f = f₁ , f₂} {g₁ , g₂} (f₁≈g₁ , f₂≈g₂) {x} {y} x≈y = begin
            f₂ ∘ x ∘ f₁ ≈⟨ f₂≈g₂ ⟩∘⟨ x≈y ⟩∘⟨ f₁≈g₁ ⟩
            g₂ ∘ y ∘ g₁ ∎

  Hom[_,-] : Obj → Functor C (Setoids ℓ e)
  Hom[_,-] = appˡ Hom[-,-]

  Hom[-,_] : Obj → Contravariant C (Setoids ℓ e)
  Hom[-,_] = appʳ Hom[-,-]

  Hom[_,_] : Obj → Obj → Setoid ℓ e
  Hom[ A , B ] = hom-setoid {A} {B}

-- Notation for when the ambient Category must be specified explicitly.
module _ {o ℓ e} (C : Category o ℓ e) where
  open Category C
  open Hom C

  Hom[_][-,-] : Bifunctor (Category.op C) C (Setoids ℓ e)
  Hom[_][-,-] = Hom[-,-]

  Hom[_][_,-] : Obj → Functor C (Setoids ℓ e)
  Hom[_][_,-] B = Hom[ B ,-]

  Hom[_][-,_] : Obj → Contravariant C (Setoids ℓ e)
  Hom[_][-,_] B = Hom[-, B ]

  Hom[_][_,_] : Obj → Obj → Setoid ℓ e
  Hom[_][_,_] A B = hom-setoid {A} {B}
