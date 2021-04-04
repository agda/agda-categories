{-# OPTIONS --without-K --safe #-}
module Categories.Category.Instance.Rels where

open import Data.Product
open import Function hiding (_⇔_)
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
  ; _≈_ = λ L R → L ⇔ R
  ; id = λ x y → Lift ℓ (x ≡ y)
  ; _∘_ = λ L R → R ; L
  ; assoc = (λ { (b , fxb , c , gbc , hcy) → c , ((b , (fxb , gbc)) , hcy)})
           , λ { (c , (b , fxb , gbc) , hcy) → b , fxb , c , gbc , hcy}
  ; sym-assoc = (λ { (c , (b , fxb , gbc) , hcy) → b , fxb , c , gbc , hcy})
              , (λ { (b , fxb , c , gbc , hcy) → c , ((b , (fxb , gbc)) , hcy)})
  ; identityˡ = (λ { (b , fxb , lift refl) → fxb}) , λ {_} {y} fxy → y , fxy , lift refl
  ; identityʳ = (λ { (a , lift refl , fxy) → fxy}) , λ {x} {_} fxy → x , lift refl , fxy
  ; identity² = (λ { (_ , lift p , lift q) → lift (trans p q)}) , λ { (lift refl) → _ , lift refl , lift refl }
  ; equiv = record
    { refl = id , id
    ; sym = swap
    ; trans = λ { (p₁ , p₂) (q₁ , q₂) → (q₁ ∘′ p₁) , p₂ ∘′ q₂}
    }
  ; ∘-resp-≈ = λ f⇔h g⇔i →
    (λ { (b , gxb , fky) → b , proj₁ g⇔i gxb , proj₁ f⇔h fky }) ,
     λ { (b , ixb , hby) → b , proj₂ g⇔i ixb , proj₂ f⇔h hby }
  }
