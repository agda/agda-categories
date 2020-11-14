{-# OPTIONS --without-K --safe #-}
module Categories.Category.Instance.Rels where

open import Data.Product
open import Function
open import Level
open import Relation.Binary
open import Relation.Binary.Construct.Composition
open import Relation.Binary.PropositionalEquality

open import Categories.Category.Core

-- the category whose objects are sets and whose morphisms are binary relations.
Rels : ∀ o ℓ → Category (suc o) (suc (o ⊔ ℓ)) (o ⊔ ℓ)
Rels o ℓ = record
  { Obj = Set o
  ; _⇒_ = λ A B → REL A B (o ⊔ ℓ)
  ; _≈_ = λ _L_ _R_ → ∀ x y → (x L y → x R y) × (x R y → x L y)
  ; id = λ x y → Lift ℓ (x ≡ y)
  ; _∘_ = λ L R → R ; L
  ; assoc = λ x y →
    (λ { (b , fxb , c , gbc , hcy) → c , (b , fxb , gbc) , hcy }) ,
    (λ { (c , (b , fxb , gbc) , hcy) → b , fxb , c , gbc , hcy })
  ; sym-assoc = λ x y →
    (λ { (c , (b , fxb , gbc) , hcy) → b , fxb , c , gbc , hcy }) ,
    (λ { (b , fxb , c , gbc , hcy) → c , (b , fxb , gbc) , hcy })
  ; identityˡ = λ x y → (λ { (.y , fxy , lift refl) → fxy }) , λ fxy → y , fxy , lift refl
  ; identityʳ = λ x y → (λ { (.x , lift refl , fxy) → fxy }) , λ fxy → x , lift refl , fxy
  ; identity² = λ x y →
    (λ { (_ , lift refl , lift refl) → lift refl }) ,
    (λ { (lift refl) → _ , lift refl , lift refl })
  ; equiv = record
    { refl = λ _ _ → id , id
    ; sym = λ p x y → swap (p x y)
    ; trans = λ p q x y → zip (flip _∘′_) _∘′_ (p x y) (q x y)
    }
  ; ∘-resp-≈ = λ p q x y →
    (λ { (b , gxb , fby) → b , proj₁ (q x b) gxb , proj₁ (p b y) fby }) ,
    (λ { (b , ixb , hby) → b , proj₂ (q x b) ixb , proj₂ (p b y) hby })
  }
