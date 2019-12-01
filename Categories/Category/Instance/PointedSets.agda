{-# OPTIONS --without-K --safe #-}
module Categories.Category.Instance.PointedSets where

-- Category of Pointed Sets

open import Level
open import Relation.Binary
open import Function using (_∘′_; _$_) renaming (id to idf)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)
open import Data.Product

open import Categories.Category
open import Categories.Category.Instance.Sets
open import Categories.Functor using (Functor)

PointedSets : ∀ o → Category (suc o) o o
PointedSets o = record
  { Obj       = Σ (Set o) idf
  ; _⇒_       = λ c d → Σ (proj₁ c → proj₁ d) (λ f → f (proj₂ c) ≡ proj₂ d)
  ; _≈_       = λ f g → ∀ x → proj₁ f x ≡ proj₁ g x
  ; id        = idf , refl
  ; _∘_       = λ { (f , f-pres-pt) (g , g-pres-pt) → f ∘′ g , ≡.trans (≡.cong f g-pres-pt) f-pres-pt}
  ; assoc     = λ _ → refl
  ; sym-assoc = λ _ → refl
  ; identityˡ = λ _ → refl
  ; identityʳ = λ _ → refl
  ; identity² = λ _ → refl
  ; equiv     = record { refl = λ _ → refl ; sym = λ pf x → ≡.sym $ pf x ; trans = λ i≡j j≡k x → ≡.trans (i≡j x) (j≡k x) }
  ; ∘-resp-≈  = λ {_} {_} {_} {_} {h} {g} f≡h g≡i x → ≡.trans (f≡h (proj₁ g x)) (≡.cong (proj₁ h) $ g≡i x)
  }

Underlying : {o : Level} → Functor (PointedSets o) (Sets o)
Underlying = record
  { F₀           = proj₁
  ; F₁           = proj₁
  ; identity     = refl
  ; homomorphism = refl
  ; F-resp-≈     = λ f≈g {x} → f≈g x
  }
