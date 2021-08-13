{-# OPTIONS --without-K --safe #-}
module Categories.Category.Instance.PartialFunctions where

-- Category of (Agda) Sets, and partial functions (modelled using Maybe).
-- Note that unlike for basic categories, this is named after the morphisms instead of the objects.

open import Data.Maybe using (Maybe; nothing; just; _>>=_; maybe)
open import Level
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as ≡
  using (_≗_; refl)

open import Categories.Category

private
  variable
    o : Level
    A B C D : Set o
    f g h : A → Maybe B

  _∘′_ : (B → Maybe C) → (A → Maybe B) → A → Maybe C
  f ∘′ g = λ a → g a >>= f

  ∘′-assoc : {h : C → Maybe D} {g : B → Maybe C} {f : A → Maybe B} → (h ∘′ g) ∘′ f ≗ h ∘′ (g ∘′ f)
  ∘′-assoc {h = h} {g} {f} a with f a
  ... | nothing = refl
  ... | just b = refl

  idˡ : {A B : Set o} {f : A → Maybe B} → just ∘′ f ≗ f
  idˡ {f = f} a = maybe {B = λ b → (b >>= just) ≡.≡ b} (λ x → refl) refl (f a)

  resp : {A B C : Set o} {f h : B → Maybe C} {g i : A → Maybe B} →
    f ≗ h → g ≗ i → (f ∘′ g) ≗ (h ∘′ i)
  resp {f = f} {h} {g} {i} f≡h g≡i a with g a | i a | g≡i a
  ... | just x | just .x | refl = f≡h x
  ... | just x | nothing | ()
  ... | nothing | just x | ()
  ... | nothing | nothing | _ = refl

PartialFunctions : ∀ o → Category (suc o) o o
PartialFunctions o = record
  { Obj = Set o
  ; _⇒_ = λ a b → a → Maybe b
  ; _≈_ = _≗_
  ; id = just
  ; _∘_ = _∘′_
  ; assoc = λ {_} {_} {_} {_} {f} {g} {h} → ∘′-assoc {h = h} {g} {f}
  ; sym-assoc = λ {_} {_} {_} {_} {f} {g} {h} a → ≡.sym (∘′-assoc {h = h} {g} {f} a)
  ; identityˡ = idˡ
  ; identityʳ = λ _ → refl
  ; identity² = idˡ
  ; equiv = λ {A} {B} → Setoid.isEquivalence (≡._→-setoid_ A (Maybe B))
  ; ∘-resp-≈ = resp
  }
