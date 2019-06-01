{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Hom where

open import Data.Product
open import Function using () renaming (_∘_ to _∙_)

open import Categories.Category
open import Categories.Bifunctor hiding (id)
open import Categories.Sets
import Categories.Square as Square

open import Relation.Binary using (Setoid)

module Hom {o ℓ e} (C : Category o ℓ e) where
  open Category C
  open Square C

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
          F₀′ (A , B) = record
            { Carrier       = A ⇒ B
            ; _≈_           = _≈_
            ; isEquivalence = equiv
            }

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
            (g₂ ∘ f₂) ∘ x ∘ f₁ ∘ g₁ ≈⟨ refl ⟩∘⟨ sym assoc ⟩
            (g₂ ∘ f₂) ∘ (x ∘ f₁) ∘ g₁ ≈⟨ pullʳ (pullˡ (∘-resp-≈ʳ (∘-resp-≈ˡ x≈y))) ⟩
            g₂ ∘ (f₂ ∘ y ∘ f₁) ∘ g₁ ∎

          F-resp-≈′ : ∀ {A B : Σ Obj (λ x → Obj)}
                        {f g : Σ (proj₁ B ⇒ proj₁ A) (λ x → proj₂ A ⇒ proj₂ B)} →
                        Σ (proj₁ f ≈ proj₁ g) (λ x → proj₂ f ≈ proj₂ g) →
                        {x y : proj₁ A ⇒ proj₂ A} →
                        x ≈ y → proj₂ f ∘ x ∘ proj₁ f ≈ proj₂ g ∘ y ∘ proj₁ g
          F-resp-≈′ {f = f₁ , f₂} {g₁ , g₂} (f₁≈g₁ , f₂≈g₂) {x} {y} x≈y = begin
            f₂ ∘ x ∘ f₁ ≈⟨ f₂≈g₂ ⟩∘⟨ x≈y ⟩∘⟨ f₁≈g₁ ⟩
            g₂ ∘ y ∘ g₁ ∎

  open Functor Hom[-,-]
  open Equiv

  Hom[_,-] : Obj → Functor C (Setoids ℓ e)
  Hom[ A ,-] = record
    { F₀           = F₀ ∙ (A ,_)
    ; F₁           = F₁ ∙ (id ,_)
    ; identity     = identity
    ; homomorphism = λ x≈y → trans (∘-resp-≈ʳ (∘-resp-≈ʳ (sym identityˡ))) (homomorphism x≈y)
    ; F-resp-≈     = λ f≈g x≈y → ∘-resp-≈ f≈g (∘-resp-≈ˡ x≈y)
    }

  Hom[-,_] : Obj → Contravariant C (Setoids ℓ e)
  Hom[-, B ] = record
    { F₀           = F₀ ∙ (_, B)
    ; F₁           = F₁ ∙ (_, id)
    ; identity     = identity
    ; homomorphism = λ x≈y → trans (∘-resp-≈ˡ (sym identityˡ)) (homomorphism x≈y)
    ; F-resp-≈     = λ f≈g x≈y → ∘-resp-≈ʳ (∘-resp-≈ x≈y f≈g)
    }

module _ {o ℓ e} where

  Hom[_][-,-] : ∀ (C : Category o ℓ e) → Bifunctor (Category.op C) C (Setoids ℓ e)
  Hom[ C ][-,-] = Hom[-,-]
    where open Hom C
  
  Hom[_][_,-] : ∀ (C : Category o ℓ e) → Category.Obj C → Functor C (Setoids ℓ e)
  Hom[ C ][ B ,-] = Hom[ B ,-]
    where open Hom C
  
  Hom[_][-,_] : ∀ (C : Category o ℓ e) → Category.Obj C → Contravariant C (Setoids ℓ e)
  Hom[ C ][-, B ] = Hom[-, B ]
    where open Hom C
  
