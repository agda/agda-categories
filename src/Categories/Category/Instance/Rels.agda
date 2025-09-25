{-# OPTIONS --safe --without-K #-}

module Categories.Category.Instance.Rels where

open import Categories.Category
open import Data.Product
open import Function.Base
open import Level
open import Relation.Binary
open import Relation.Binary.Construct.Composition

Rels : ∀ o ℓ → Category (suc (o ⊔ ℓ)) (suc (o ⊔ ℓ)) (o ⊔ ℓ)
Rels o ℓ  = record
  { Obj = Setoid o ℓ
  ; _⇒_ = λ A B → Σ[ _R_ ∈ REL (Setoid.Carrier A) (Setoid.Carrier B) (o ⊔ ℓ) ] (_R_ Respectsˡ Setoid._≈_ A × _R_ Respectsʳ Setoid._≈_ B)
  ; _≈_ = λ f g → proj₁ f ⇔ proj₁ g
  ; id = λ {A} → let open Setoid A in record
    { fst = λ x y → Lift o (x ≈ y)
    ; snd = record
      { fst = λ x≈z y≈z → lift (trans (sym x≈z) (lower y≈z))
      ; snd = λ x≈z y≈x → lift (trans (lower y≈x) x≈z)
      }
    }
  ; _∘_ = λ f g → record
    { fst = proj₁ g ; proj₁ f
    ; snd = record
      { fst = λ y≈z y[g;f]x → proj₁ y[g;f]x , proj₁ (proj₂ g) y≈z (proj₁ (proj₂ y[g;f]x)) , proj₂ (proj₂ y[g;f]x)
      ; snd = λ y≈z x[g;f]y → proj₁ x[g;f]y , proj₁ (proj₂ x[g;f]y) , proj₂ (proj₂ f) y≈z (proj₂ (proj₂ x[g;f]y))
      }
    }
  ; assoc = record
    { fst = λ { (b , xfb , c , bgc , chy) → c , (b , xfb , bgc) , chy }
    ; snd = λ { (c , (b , xfb , bgc) , chy) → b , xfb , c , bgc , chy }
    }
  ; sym-assoc = record
    { fst = λ { (c , (b , xfb , bgc) , chy) → b , xfb , c , bgc , chy }
    ; snd = λ { (b , xfb , c , bgc , chy) → c , (b , xfb , bgc) , chy }
    }
  ; identityˡ = λ {A} {B} {f} → record
    { fst = λ af;≈b → proj₂ (proj₂ f) (lower (proj₂ (proj₂ af;≈b))) (proj₁ (proj₂ af;≈b)) 
    ; snd = λ afb → _ , afb , lift (Setoid.refl B)
    }
  ; identityʳ = λ {A} {B} {f} → record
    { fst = λ a≈;fb → proj₁ (proj₂ f) (Setoid.sym A (lower (proj₁ (proj₂ a≈;fb)))) (proj₂ (proj₂ a≈;fb))
    ; snd = λ afb → _ , lift (Setoid.refl A) , afb
    }
  ; identity² = λ {A} → record
    { fst = λ x≈;≈y → lift (Setoid.trans A (lower (proj₁ (proj₂ x≈;≈y))) (lower (proj₂ (proj₂ x≈;≈y))))
    ; snd = λ x≈y → _ , lift (Setoid.refl A) , x≈y
    }
  ; equiv = record
    { refl = id , id
    ; sym = swap
    ; trans = λ { (p₁ , p₂) (q₁ , q₂) → (q₁ ∘′ p₁) , (p₂ ∘′ q₂) }
    }
  ; ∘-resp-≈ = λ f⇔h g⇔i → record
    { fst = λ { (b , xgb , bfy) → b , proj₁ g⇔i xgb , proj₁ f⇔h bfy }
    ; snd = λ { (b , xib , bhy) → b , proj₂ g⇔i xib , proj₂ f⇔h bhy }
    }
  }
