{-# OPTIONS --without-K --safe #-}
module Categories.NaturalTransformation.Extranatural where

-- Although there is a notion of Extranatural in Categories.NaturalTransformation.Dinatural,
-- it isn't the most general form, thus the need for this as well.

open import Level
open import Data.Product
open import Relation.Binary using (Rel; IsEquivalence; Setoid)

open import Categories.Category
open import Categories.NaturalTransformation as NT hiding (_∘ʳ_)
open import Categories.Functor
open import Categories.Functor.Construction.Constant
open import Categories.Category.Product
import Categories.Morphism.Reasoning as MR

private
  variable
    o₁ o₂ o₃ o₄ ℓ₁ ℓ₂ ℓ₃ ℓ₄ e₁ e₂ e₃ e₄ : Level

record ExtranaturalTransformation
    {A : Category o₁ ℓ₁ e₁}
    {B : Category o₂ ℓ₂ e₂}
    {C : Category o₃ ℓ₃ e₃}
    {D : Category o₄ ℓ₄ e₄}
    (P : Functor (Product A (Product (Category.op B) B)) D)
    (Q : Functor (Product A (Product (Category.op C) C)) D) : Set (o₁ ⊔ o₂ ⊔ o₃ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ e₄)  where

  private
    module A = Category A
    module B = Category B
    module C = Category C
    module D = Category D
    module P = Functor P
    module Q = Functor Q

  open D hiding (op)
  open Commutation D

  field
    α          : ∀ a b c → D [ P.₀ (a , (b , b)) , Q.₀ (a , (c , c)) ]
    commute    : ∀ {a a′ b b′ c c′} (f : A [ a , a′ ]) (g : B [ b , b′ ])
                  (h : C [ c , c′ ]) →
                [ P.₀ (a , (b′ , b) ) ⇒ Q.₀ (a′ , (c , c′)) ]⟨
                  P.₁ (f , B.id , g)         ⇒⟨ P.₀ (a′ , (b′ , b′)) ⟩
                  α a′ b′ c                  ⇒⟨ Q.₀ (a′ , (c , c)) ⟩
                  Q.₁ (A.id , C.id , h)
                ≈ P.₁ (A.id , g , B.id)      ⇒⟨ P.₀ (a , (b , b)) ⟩
                  α a b c′                   ⇒⟨ Q.₀ (a , (c′ , c′)) ⟩
                  Q.₁ (f , h , C.id)
                ⟩
