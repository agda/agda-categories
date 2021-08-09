{-# OPTIONS --without-K --safe #-}

-- The category of Cats is Monoidal

module Categories.Category.Monoidal.Instance.StrictCats where

open import Level
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; uncurry)
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_; refl; cong₂; sym; module ≡-Reasoning; subst₂; cong)
open import Function using (_$_)
open import Data.Unit using (⊤; tt)

open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Cartesian.Monoidal using (module CartesianMonoidal)
open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.StrictCats
open import Categories.Category.Instance.One using (One)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Product
open import Categories.Category.Product.Properties
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Functor.Construction.Constant
open import Categories.Functor.Equivalence
import Categories.Morphism.HeterogeneousIdentity as HId
import Categories.Morphism.HeterogeneousIdentity.Properties as HIdProps
import Categories.Morphism.Reasoning as MR
open import Categories.Object.Terminal
open import Categories.Utils.Product using (zipWith)
open import Categories.Utils.EqReasoning

-- (Strict) Cats is a (strict) Monoidal Category with Product as Bifunctor
module Product {o ℓ e : Level} where
  private
    C = StrictCats o ℓ e
    open _≡F_

  Cats-has-all : BinaryProducts C
  Cats-has-all = record { product = λ {A} {B} → record
    { A×B = Product A B
    ; π₁ = πˡ
    ; π₂ = πʳ
    ; ⟨_,_⟩ = _※_
    ; project₁ = record { eq₀ = λ _ → ≡.refl ; eq₁ = λ _ → MR.id-comm-sym A }
    ; project₂ = record { eq₀ = λ _ → ≡.refl ; eq₁ = λ _ → MR.id-comm-sym B }
    ; unique = λ {hA} {h} {i} {j} left right →
      let unique-eq₀ X = cong₂ _,_ (≡.sym $ eq₀ left X) (≡.sym $ eq₀ right X)
      in record
      { eq₀ = unique-eq₀
      ; eq₁ = λ {a} {b} f →
          let module A   = Category A
              module B   = Category B
              module C   = Category C
              module A×B = Category (Product A B)
              open A×B.HomReasoning
              open HId
              open HIdProps
              open Functor
              leq a = ≡.sym $ eq₀ left a
              req a = ≡.sym $ eq₀ right a
          in begin
                hid (Product A B) (unique-eq₀ b) A×B.∘ F₁ (i ※ j) f
              ≈˘⟨ A×B.∘-resp-≈ˡ (×-hid A B (leq b) (req b)) ⟩
                (hid A (leq b) A.∘ F₁ i f , hid B (req b) B.∘ F₁ j f)
              ≈⟨ eq₁⁻¹ left f , eq₁⁻¹ right f ⟩
                F₁ (πˡ C.∘ h) f A.∘ hid A (leq a) ,
                F₁ (πʳ C.∘ h) f B.∘ hid B (req a)
              ≈⟨ A×B.∘-resp-≈ʳ (×-hid A B (leq a) (req a)) ⟩
                (F₁ h f) A×B.∘ (hid (Product A B) (unique-eq₀ a))
              ∎
      }
    } }

  private
    unique-One : {l : Level} (x : Lift l ⊤) → lift tt ≡ x
    unique-One (lift tt) = refl

  One-⊤ : Terminal C
  One-⊤ = record
    { ⊤ = One
    ; ⊤-is-terminal = record
      { ! = const (lift tt)
      ; !-unique = λ f → record { eq₀ = λ _ → unique-One _ ; eq₁ = λ _ → lift tt }
      }
    }

  Cats-is : Cartesian C
  Cats-is = record { terminal = One-⊤ ; products = Cats-has-all }

  Cats-Monoidal : Monoidal C
  Cats-Monoidal = CartesianMonoidal.monoidal Cats-is
