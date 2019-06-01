{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Categories.Object.Coproduct {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level

open Category 𝒞

open import Categories.Square 𝒞
open import Categories.Morphisms 𝒞
import Categories.Object.Product op as Op×

open HomReasoning

private
  variable
    A B C D : Obj
    f g h : A ⇒ B

-- Borrowed from Dan Doel's definition of coproducts
record Coproduct (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    A+B   : Obj
    i₁    : A ⇒ A+B
    i₂    : B ⇒ A+B
    [_,_] : A ⇒ C → B ⇒ C → A+B ⇒ C

    commute₁  : [ f , g ] ∘ i₁ ≈ f
    commute₂  : [ f , g ] ∘ i₂ ≈ g
    universal : h ∘ i₁ ≈ f → h ∘ i₂ ≈ g → [ f , g ] ≈ h

  g-η : [ f ∘ i₁ , f ∘ i₂ ] ≈ f
  g-η = universal Equiv.refl Equiv.refl

  η : [ i₁ , i₂ ] ≈ id
  η = universal identityˡ identityˡ

  []-cong₂ : ∀ {C} → {f f′ : A ⇒ C} {g g′ : B ⇒ C} → f ≈ f′ → g ≈ g′ → [ f , g ] ≈ [ f′ , g′ ]
  []-cong₂ f≈f′ g≈g′ = universal (trans commute₁ (sym f≈f′)) (trans commute₂ (sym g≈g′))

-- record BinCoproducts : Set (suc o ⊔ ℓ ⊔ e) where
--   field
--     _+_   : (A B : Obj) -> Obj
--     i₁    : A ⇒ (A + B)
--     i₂    : B ⇒ (A + B)
--     [_,_] : A ⇒ C → B ⇒ C → (A + B) ⇒ C

--     commute₁ : ∀ {f : A ⇒ C} {g : B ⇒ C} → [ f , g ] ∘ i₁ ≈ f
--     commute₂ : ∀ {f : A ⇒ C} {g : B ⇒ C} → [ f , g ] ∘ i₂ ≈ g
--     universal : ∀ {f : A ⇒ C} {g : B ⇒ C} {h : (A + B) ⇒ C} →
--                   h ∘ i₁ ≈ f → h ∘ i₂ ≈ g → [ f , g ] ≈ h

coproduct→product : ∀ {A B} → Coproduct A B → Op×.Product A B
coproduct→product A+B = record
  { A×B = A+B.A+B
  ; π₁ = A+B.i₁
  ; π₂ = A+B.i₂
  ; ⟨_,_⟩ = A+B.[_,_]
  ; commute₁ = A+B.commute₁
  ; commute₂ = A+B.commute₂
  ; universal = A+B.universal
  }
  where
  module A+B = Coproduct A+B

product→coproduct : ∀ {A B} → Op×.Product A B → Coproduct A B
product→coproduct A×B = record
  { A+B = A×B.A×B
  ; i₁ = A×B.π₁
  ; i₂ = A×B.π₂
  ; [_,_] = A×B.⟨_,_⟩
  ; commute₁ = A×B.commute₁
  ; commute₂ = A×B.commute₂
  ; universal = A×B.universal
  }
  where
  module A×B = Op×.Product A×B

-- open import Categories.Morphisms

-- Commutative : ∀ {A B} → (p₁ : Coproduct A B) (p₂ : Coproduct B A) → _≅_ C (Coproduct.A+B p₁) (Coproduct.A+B p₂)
-- Commutative p₁ p₂ = opⁱ (Op×.Commutative (coproduct→product p₂) (coproduct→product p₁))

-- Associative : ∀ {X Y Z} (p₁ : Coproduct X Y) (p₂ : Coproduct Y Z) (p₃ : Coproduct X (Coproduct.A+B p₂)) (p₄ : Coproduct (Coproduct.A+B p₁) Z) → _≅_ C (Coproduct.A+B p₃) (Coproduct.A+B p₄)
-- Associative p₁ p₂ p₃ p₄ = reverseⁱ C (opⁱ (Op×.Associative (coproduct→product p₁) (coproduct→product p₂) (coproduct→product p₃) (coproduct→product p₄)))
