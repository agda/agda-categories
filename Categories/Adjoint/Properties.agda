{-# OPTIONS --without-K --safe #-}

module Categories.Adjoint.Properties where

open import Level
open import Data.Product using (Σ; _,_)

open import Categories.Adjoint
open import Categories.Adjoint.RAPL public
open import Categories.Category
open import Categories.Functor
open import Categories.Functor.Continuous
open import Categories.Functor.Bifunctor
open import Categories.Functor.Bifunctor.Properties
open import Categories.NaturalTransformation

import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level
    C D E J : Category o ℓ e

-- if the left adjoint functor is a partial application of bifunctor, then it uniquely
-- determines a bifunctor compatible with the right adjoint functor.
module _ {C : Category o ℓ e}
         (L : Bifunctor C E D) {R : ∀ (X : Category.Obj E) → Functor D C}
         (LR : ∀ (X : Category.Obj E) → appʳ L X ⊣ R X) where
  private
    module C    = Category C
    module D    = Category D
    module E    = Category E
    module L    = Functor L
    module R X  = Functor (R X)
    module LR X = Adjoint (LR X)
    open C

    F′ : ∀ {A X B Y} f g → R.F₀ A X ⇒ R.F₀ B Y
    F′ {A} {X} {B} {Y} f g = LR.Ladjunct B (LR.counit.η A Y D.∘ L.F₁ (R.F₁ A g , f))
    --  R.F₁ B (LR.counit.η A Y) ∘ R.F₁ B (L.F₁ (R.F₁ A g , f)) ∘ LR.unit.η B (R.F₀ A X)

    commute′ : ∀ {A B X} (f : A E.⇒ B) → LR.counit.η A X D.∘ L.F₁ (F′ f D.id , E.id) D.≈ LR.counit.η B X D.∘ L.F₁ (C.id , f)
    commute′ {A} {B} {X} f = begin
      LR.counit.η A X D.∘ L.F₁ (F′ f D.id , E.id) ≈⟨ LR.RLadjunct≈id A ⟩
      LR.counit.η B X D.∘ L.F₁ (R.F₁ B D.id , f)  ≈⟨ refl ⟩∘⟨ L.F-resp-≈ (R.identity B , E.Equiv.refl) ⟩
      LR.counit.η B X D.∘ L.F₁ (C.id , f)         ∎
      where open D.HomReasoning

    open HomReasoning
    
    decompose₁ : ∀ {A B X Y} {f : A E.⇒ B} {g : X D.⇒ Y} → F′ f g ≈ R.F₁ A g ∘ F′ f D.id
    decompose₁ {A} {B} {X} {Y} {f} {g} = begin
      F′ f g
        ≈⟨ R.F-resp-≈ A (D.∘-resp-≈ʳ [ L ]-decompose₁) ⟩∘⟨refl ⟩
      R.F₁ A (LR.counit.η B Y D.∘ L.F₁ (R.F₁ B g , E.id) D.∘ L.F₁ (C.id , f)) ∘ LR.unit.η A (R.F₀ B X)
        ≈⟨ R.F-resp-≈ A (pullˡ (LR.counit.commute B g)) ⟩∘⟨refl ⟩
      R.F₁ A ((g D.∘ LR.counit.η B X) D.∘ L.F₁ (C.id , f)) ∘ LR.unit.η A (R.F₀ B X)
        ≈˘⟨ R.F-resp-≈ A (pushʳ (D.∘-resp-≈ʳ (L.F-resp-≈ (R.identity B , E.Equiv.refl)))) ⟩∘⟨refl ⟩
      R.F₁ A (g D.∘ LR.counit.η B X D.∘ L.F₁ (R.F₁ B D.id , f)) ∘ LR.unit.η A (R.F₀ B X)
        ≈⟨ R.homomorphism A ⟩∘⟨refl ⟩
      (R.F₁ A g ∘ R.F₁ A (LR.counit.η B X D.∘ L.F₁ (R.F₁ B D.id , f))) ∘ LR.unit.η A (R.F₀ B X)
        ≈⟨ assoc ⟩
      R.F₁ A g ∘ F′ f D.id
        ∎
      where open MR D

    decompose₂ : ∀ {A B X Y} {f : A E.⇒ B} {g : X D.⇒ Y} → F′ f g ≈ F′ f D.id ∘ R.F₁ B g
    decompose₂ {A} {B} {X} {Y} {f} {g} = begin
      F′ f g
        ≈⟨ R.F-resp-≈ A (D.∘-resp-≈ʳ [ L ]-decompose₂) ⟩∘⟨refl ⟩
      R.F₁ A (LR.counit.η B Y D.∘ L.F₁ (C.id , f) D.∘ L.F₁ (R.F₁ B g , E.id)) ∘ LR.unit.η A (R.F₀ B X)
        ≈˘⟨ R.F-resp-≈ A (pushˡ (D.∘-resp-≈ʳ (L.F-resp-≈ (R.identity B , E.Equiv.refl)))) ⟩∘⟨refl ⟩
      R.F₁ A ((LR.counit.η B Y D.∘ L.F₁ (R.F₁ B D.id , f)) D.∘ L.F₁ (R.F₁ B g , E.id)) ∘ LR.unit.η A (R.F₀ B X)
        ≈⟨ R.homomorphism A ⟩∘⟨refl ⟩
      (R.F₁ A (LR.counit.η B Y D.∘ L.F₁ (R.F₁ B D.id , f)) ∘ R.F₁ A (L.F₁ (R.F₁ B g , E.id))) ∘ LR.unit.η A (R.F₀ B X)
        ≈˘⟨ MR.pushʳ C (LR.unit.commute A (R.F₁ B g)) ⟩
      R.F₁ A (LR.counit.η B Y D.∘ L.F₁ (R.F₁ B D.id , f)) ∘ LR.unit.η A (R.F₀ B Y) ∘ R.F₁ B g
        ≈˘⟨ assoc ⟩
      F′ f D.id ∘ R.F₁ B g
        ∎
      where open MR D

    swap : ∀ {A B X Y} {f : A E.⇒ B} {g : X D.⇒ Y} → R.F₁ A g ∘ F′ f D.id ≈ F′ f D.id ∘ R.F₁ B g
    swap = trans (⟺ decompose₁) decompose₂

    commute″ : ∀ {X Y Z A} {f : Y E.⇒ Z} {g : X E.⇒ Y} → F′ (f E.∘ g) (D.id {A}) ≈ F′ g D.id ∘ F′ f D.id
    commute″ {X} {Y} {Z} {A} {f} {g} = begin
      F′ (f E.∘ g) D.id
        ≈⟨ R.F-resp-≈ X (D.∘-resp-≈ʳ (L.F-resp-≈ (R.identity Z , E.Equiv.refl))) ⟩∘⟨refl ⟩
      R.F₁ X (LR.counit.η Z A D.∘ L.F₁ (C.id , f E.∘ g)) ∘ LR.unit.η X (R.F₀ Z A)
        ≈⟨ R.F-resp-≈ X (D.∘-resp-≈ʳ (Functor.homomorphism (appˡ L (R.F₀ Z A)))) ⟩∘⟨refl ⟩
      R.F₁ X (LR.counit.η Z A D.∘ L.F₁ (C.id , f) D.∘ L.F₁ (C.id , g)) ∘ LR.unit.η X (R.F₀ Z A)
        ≈˘⟨ R.F-resp-≈ X (MR.pushˡ D (commute′ f)) ⟩∘⟨refl ⟩
      R.F₁ X ((LR.counit.η Y A D.∘ L.F₁ (F′ f D.id , E.id)) D.∘ L.F₁ (C.id , g)) ∘ LR.unit.η X (R.F₀ Z A)
        ≈˘⟨ R.F-resp-≈ X (MR.pushʳ D [ L ]-commute) ⟩∘⟨refl ⟩
      R.F₁ X (LR.counit.η Y A D.∘ L.F₁ (C.id , g) D.∘ L.F₁ (F′ f D.id , E.id)) ∘ LR.unit.η X (R.F₀ Z A)
        ≈˘⟨ R.F-resp-≈ X D.assoc ⟩∘⟨refl ⟩
      R.F₁ X ((LR.counit.η Y A D.∘ L.F₁ (C.id , g)) D.∘ L.F₁ (F′ f D.id , E.id)) ∘ LR.unit.η X (R.F₀ Z A)
        ≈⟨ R.homomorphism X ⟩∘⟨refl ⟩
      (R.F₁ X (LR.counit.η Y A D.∘ L.F₁ (C.id , g)) ∘ R.F₁ X (L.F₁ (F′ f D.id , E.id))) ∘ LR.unit.η X (R.F₀ Z A)
        ≈˘⟨ MR.pushʳ C (LR.unit.commute X (F′ f D.id)) ⟩
      R.F₁ X (LR.counit.η Y A D.∘ L.F₁ (C.id , g)) ∘ LR.unit.η X (R.F₀ Y A) ∘ F′ f D.id
        ≈˘⟨ R.F-resp-≈ X (D.∘-resp-≈ʳ (L.F-resp-≈ (R.identity Y , E.Equiv.refl))) ⟩∘⟨ refl ⟩∘⟨ refl ⟩
      R.F₁ X (LR.counit.η Y A D.∘ L.F₁ (R.F₁ Y D.id , g)) ∘ LR.unit.η X (R.F₀ Y A) ∘ F′ f D.id
        ≈˘⟨ assoc ⟩
      F′ g D.id ∘ F′ f D.id
        ∎
  
  induced-bifunctorʳ : Bifunctor E.op D C
  induced-bifunctorʳ = record
    { F₀           = λ where
      (e , d) → R.F₀ e d 
    ; F₁           = λ where
      {A , X} {B , Y} (f , g) → F′ f g
    ; identity     = λ where
      {e , d} →
        let open MR D
        in begin
          F′ E.id D.id
            ≈⟨ R.F-resp-≈ e (D.∘-resp-≈ʳ (L.F-resp-≈ (R.identity e , E.Equiv.refl))) ⟩∘⟨ refl ⟩
          R.F₁ e (LR.counit.η e d D.∘ L.F₁ (C.id , E.id)) ∘ LR.unit.η e (R.F₀ e d)
            ≈⟨ R.F-resp-≈ e (elimʳ L.identity) ⟩∘⟨ refl ⟩
          R.F₁ e (LR.counit.η e d) ∘ LR.unit.η e (R.F₀ e d)
            ≈⟨ LR.zag e ⟩
          C.id
            ∎
    ; homomorphism = λ where
      {A , X} {B , Y} {W , Z} {f , h} {g , i} →
        let open MR C
        in begin
          F′ (f E.∘ g) (i D.∘ h)
            ≈⟨ decompose₁ ⟩
          R.F₁ W (i D.∘ h) ∘ F′ (f E.∘ g) D.id
            ≈˘⟨ center⁻¹ (⟺ (R.homomorphism W)) (⟺ commute″) ⟩
          R.F₁ W i ∘ (R.F₁ W h ∘ F′ g D.id) ∘ F′ f D.id
            ≈˘⟨ center (⟺ swap) ⟩
          (R.F₁ W i ∘ F′ g D.id) ∘ R.F₁ B h ∘ F′ f D.id
            ≈˘⟨ decompose₁ ⟩∘⟨ decompose₁ ⟩
          F′ g i ∘ F′ f h
            ∎
    ; F-resp-≈     = λ where
      {A , X} {B , Y} (eq , eq′) →
        ∘-resp-≈ˡ (R.F-resp-≈ B (D.∘-resp-≈ʳ (L.F-resp-≈ (R.F-resp-≈ A eq′ , eq))))
    }

module _ {L : Functor C D} {R : Functor D C} (L⊣R : L ⊣ R) where

  rapl′ : ∀ {o ℓ e} → Continuous o ℓ e R
  rapl′ lim = rapl L⊣R lim , Mor.≅.refl C
