{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Instance.Simplex where

open import Level
open import Data.Product
open import Data.Fin.Base using (Fin; _≤_)
open import Data.Nat.Base using (ℕ; z≤n; s≤s)
open import Function renaming (id to idF; _∘_ to _∙_)

open import Relation.Binary using (_=[_]⇒_)
open import Relation.Binary.PropositionalEquality

Δ : Category 0ℓ 0ℓ 0ℓ
Δ = record
  { Obj       = ℕ
  ; _⇒_       = λ m n → Σ (Fin m → Fin n) (λ f → _≤_ =[ f ]⇒ _≤_)
  ; _≈_       = λ { (f , mf) (g , mg) → ∀ x → f x ≡ g x }
  ; id        = idF , idF
  ; _∘_       = λ { (f , mf) (g , mg) → f ∙ g , mf ∙ mg }
  ; assoc     = λ _ → refl
  ; sym-assoc = λ _ → refl
  ; identityˡ = λ _ → refl
  ; identityʳ = λ _ → refl
  ; identity² = λ _ → refl
  ; equiv     = record
    { refl  = λ _ → refl
    ; sym   = λ eq x → sym (eq x)
    ; trans = λ eq₁ eq₂ x → trans (eq₁ x) (eq₂ x)
    }
  ; ∘-resp-≈  = λ {_ _ _ f g h i} eq₁ eq₂ x → trans (cong (λ t → proj₁ f t) (eq₂ x)) (eq₁ (proj₁ i x))
  }

open Category Δ

--------------------------------------------------------------------------------
-- Face + Degeneracy Maps

face-map : ∀ {n} → Fin (ℕ.suc n) → Fin n → Fin (ℕ.suc n)
face-map Fin.zero k = Fin.suc k
face-map (Fin.suc i) Fin.zero = Fin.zero
face-map (Fin.suc i) (Fin.suc k) = Fin.suc (face-map i k)

face-mono : ∀ {n} → (i : Fin (ℕ.suc n)) → _≤_ =[ face-map i ]⇒ _≤_
face-mono Fin.zero {x} {y} le = s≤s le
face-mono (Fin.suc i) {Fin.zero} {y} le = z≤n
face-mono (Fin.suc i) {Fin.suc x} {Fin.suc y} (s≤s le) = s≤s (face-mono i le)

face : ∀ {n} → Fin (ℕ.suc n) → n ⇒ ℕ.suc n
face i = face-map i , face-mono i

degeneracy-map : ∀ {n} → Fin n → Fin (ℕ.suc n) → Fin n
degeneracy-map Fin.zero Fin.zero = Fin.zero
degeneracy-map Fin.zero (Fin.suc Fin.zero) = Fin.zero
degeneracy-map Fin.zero (Fin.suc (Fin.suc k)) = Fin.suc k
degeneracy-map (Fin.suc i) Fin.zero = Fin.zero
degeneracy-map (Fin.suc i) (Fin.suc k) = Fin.suc (degeneracy-map i k)

degeneracy-mono : ∀ {n} → (i : Fin n) → _≤_ =[ degeneracy-map i ]⇒ _≤_
degeneracy-mono Fin.zero {Fin.zero} {y} le = z≤n
degeneracy-mono Fin.zero {Fin.suc (Fin.zero)} {Fin.suc y} le = z≤n
degeneracy-mono Fin.zero {Fin.suc (Fin.suc x)} {Fin.suc (Fin.suc y)} (s≤s le) = le
degeneracy-mono (Fin.suc i) {Fin.zero} {y} le = z≤n
degeneracy-mono (Fin.suc i) {Fin.suc x} {Fin.suc y} (s≤s le) = s≤s (degeneracy-mono i le)

degeneracy : ∀ {n} → Fin n → ℕ.suc n ⇒ n
degeneracy i = degeneracy-map i , degeneracy-mono i
