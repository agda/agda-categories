{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Preds where

-- Category of (Agda) predicates, aka (indexed types, families of functions, pointwise equality with implicit value)
-- Note the (explicit) levels in each

open import Function renaming (id to idf) using (_∘_)
open import Level using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl; sym; trans)
open import Relation.Unary using (_⇒_; Pred; IUniversal)

open import Categories.Category using (Category)

Preds : ∀ o → Set o → Category (suc o) o o
Preds o A = record
  { Obj = Pred A o
  ; _⇒_ = λ P Q → ∀[ P ⇒ Q ]
  ; _≈_ = λ {P} f g → (x : A) → (y : P x) → f y ≡ g y
  ; id = idf
  ; _∘_ = λ α β → α ∘ β
  ; assoc = λ _ _ → refl
  ; sym-assoc = λ _ _ → refl
  ; identityˡ = λ _ _ → refl
  ; identityʳ = λ _ _ → refl
  ; identity² = λ _ _ → refl
  ; equiv = record
    { refl = λ _ _ → refl
    ; sym = λ α a x → sym (α a x)
    ; trans = λ α β a x → trans (α a x) (β a x)
    }
  ; ∘-resp-≈ = λ {_} {_} {_} {f} {_} {_} {i} α β a x → trans (cong f (β a x)) (α a (i x))
  }
