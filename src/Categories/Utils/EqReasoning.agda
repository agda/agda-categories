{-# OPTIONS --without-K --safe #-}

module Categories.Utils.EqReasoning where

open import Level
open import Relation.Binary.PropositionalEquality
open import Data.Product using (Σ; _,_; _×_)

open import Categories.Utils.Product

subst₂-sym-subst₂ : {ℓa ℓb ℓp : Level} {A : Set ℓa} {B : Set ℓb} {a₁ a₂ : A} {b₁ b₂ : B}
                    (R : A → B → Set ℓp) {p : R a₁ b₁} (eq₁ : a₁ ≡ a₂) (eq₂ : b₁ ≡ b₂) →
                    subst₂ R (sym eq₁) (sym eq₂) (subst₂ R eq₁ eq₂ p) ≡ p
subst₂-sym-subst₂ R refl refl = refl

subst₂-subst₂-sym : {ℓa ℓb ℓp : Level} {A : Set ℓa} {B : Set ℓb} {a₁ a₂ : A} {b₁ b₂ : B}
                    (R : A → B → Set ℓp) {p : R a₁ b₁} (eq₁ : a₂ ≡ a₁) (eq₂ : b₂ ≡ b₁) →
                    subst₂ R eq₁ eq₂ (subst₂ R (sym eq₁) (sym eq₂) p) ≡ p
subst₂-subst₂-sym R refl refl = refl

subst₂-subst₂ : {ℓa ℓb ℓp : Level} {A : Set ℓa} {B : Set ℓb} {a₁ a₂ a₃ : A} {b₁ b₂ b₃ : B}
              (R : A → B → Set ℓp) {p : R a₁ b₁}
              (eq-a₁₂ : a₁ ≡ a₂) (eq-a₂₃ : a₂ ≡ a₃)
              (eq-b₁₂ : b₁ ≡ b₂) (eq-b₂₃ : b₂ ≡ b₃) →
              subst₂ R eq-a₂₃ eq-b₂₃ (subst₂ R eq-a₁₂ eq-b₁₂ p) ≡ subst₂ R (trans eq-a₁₂ eq-a₂₃) (trans eq-b₁₂ eq-b₂₃) p
subst₂-subst₂ R refl refl refl refl = refl

subst₂-app : ∀ {a₁ a₂ a₃ a₄ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂} {A₃ : Set a₃} {A₄ : Set a₄}
                  (B₁ : A₁ → A₃ → Set b₁) {B₂ : A₂ → A₄ → Set b₂}
                  {f : A₂ → A₁} {h : A₄ → A₃} {x₁ x₂ : A₂} {x₃ x₄ : A₄} (y : B₂ x₁ x₃)
                  (g : ∀ w z → B₂ w z → B₁ (f w) (h z)) (eq₁ : x₁ ≡ x₂) (eq₂ : x₃ ≡ x₄) →
                  subst₂ B₁ (cong f eq₁) (cong h eq₂) (g x₁ x₃ y) ≡ g x₂ x₄ (subst₂ B₂ eq₁ eq₂ y)
subst₂-app _ _ _ refl refl = refl

subst₂-prod : ∀ {ℓa ℓb ℓr ℓs} {A : Set ℓa} {B : Set ℓb}
      (R : A → A → Set ℓr) (S : B → B → Set ℓs) {a b c d : A} {x y z w : B}
      {f : R a b} {g : S x y}
      (eq₁ : a ≡ c) (eq₂ : b ≡ d) (eq₃ : x ≡ z) (eq₄ : y ≡ w) →
      subst₂ (λ { (p , q) (r , s) → R p r × S q s })
      (sym (cong₂ _,_ (sym eq₁) (sym eq₃)))
      (sym (cong₂ _,_ (sym eq₂) (sym eq₄)))
      (f , g)
      ≡
      (subst₂ R eq₁ eq₂ f , subst₂ S eq₃ eq₄ g)
subst₂-prod R S refl refl refl refl = refl

------------------
-- For reasoning with things from Categories.Utils.Product
subst₂-expand : ∀ {a b ℓ ℓ′ p q} {A : Set a} {B : Set b}
  {P : A → Set p} {Q : B → Set q}
  (_∙_ : A → B → Set ℓ) → (_∘_ : ∀ {x y} → P x → Q y → Set ℓ′) →
  {a₁ a₂ : A} {b₁ b₂ : B} {p₁ p₂ : P a₁} {q₁ q₂ : Q b₁}
  (eq₁ : a₁ ≡ a₂) (eq₂ : p₁ ≡ p₂) (eq₃ : b₁ ≡ b₂) (eq₄ : q₁ ≡ q₂) →
  (F : a₁ ∙ b₁) → (G : p₁ ∘ q₁) →
  subst₂ (_∙_ -< _×_ >- _∘_)
      (cong₂ _,_ eq₁ eq₂)
      (cong₂ _,_ eq₃ eq₄)
      (F , G) ≡ (subst₂ _∙_ eq₁ eq₃ F , subst₂ _∘_ eq₂ eq₄ G)
subst₂-expand T₁ T₂ refl refl refl refl F G = refl
