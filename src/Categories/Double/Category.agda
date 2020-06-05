{-# OPTIONS --without-K --safe #-}
module Categories.Double.Category where

open import Level

open import Relation.Binary using (Rel; REL; IsEquivalence; Setoid)
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Categories.Double.IsCategory

record ||Pair {a r : Level} {Obj : Set a} {X X′ Y Y′ : Obj} (R : Rel Obj r) : Set (a ⊔ r) where
  constructor ||
  field
    fst : R X X′
    snd : R Y Y′

open ||Pair

||∘ : {a r : Level} {Obj : Set a} {X X′ Y Y′ X″ Y″ : Obj} {R : Rel Obj r}
  (_∘₁_ : R X′ X″ → R X X′ → R X X″) (_∘₂_ : R Y′ Y″ → R Y Y′ → R Y Y″) →
  ||Pair R → ||Pair R → ||Pair R
||∘ _∘₁_ _∘₂_ i j = || (fst j ∘₁ fst i) (snd j ∘₂ snd i)

-- Witness for a relation
record Witness {a b r : Level} {A : Set a} {B : Set b} (R : REL A B r) : Set (a ⊔ b ⊔ r) where
  constructor proof
  field
    {XW} : A
    {YW} : B
    wit : R XW YW

open Witness

record Category (ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ ℓ₇ ℓ₈ ℓ₉ : Level)
  : Set (suc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆ ⊔ ℓ₇ ⊔ ℓ₈ ⊔ ℓ₉)) where

  infixr 9 _⇒∘_ _⇓∘_
  infix 4 _≃_

  field
    Obj : Set ℓ₁

    -- horizontal category structure
    ⇒Cat : OverCarrier ℓ₂ ℓ₃ Obj

    -- vertical category structure
    ⇓Cat : OverCarrier ℓ₄ ℓ₅ Obj

  -- give short-names to things
  module ⇒ = OverCarrier ⇒Cat
  module ⇓ = OverCarrier ⇓Cat

  field
    cell : {X X′ Y Y′ : Obj} (f : X ⇒.⇒ X′) (g : Y ⇒.⇒ Y′) (u : X ⇓.⇒ Y) (v : X′ ⇓.⇒ Y′) → Set ℓ₆
    id⇒ : {X Y : Obj} (u : X ⇓.⇒ Y) → cell ⇒.id ⇒.id u u
    _⇒∘_ : {X X′ X″ Y Y′ Y″ : Obj} {f : X ⇒.⇒ X′} {g : Y ⇒.⇒ Y′} {u : X ⇓.⇒ Y} {v : X′ ⇓.⇒ Y′}
      {w : X″ ⇓.⇒ Y″} {f′ : X′ ⇒.⇒ X″} {g′ : Y′ ⇒.⇒ Y″} →
      (α : cell f g u v) → (β : cell f′ g′ v w) → cell (f′ ⇒.∘ f) (g′ ⇒.∘ g) u w
    id⇓ : {X Y : Obj} (u : X ⇒.⇒ Y) → cell u u ⇓.id ⇓.id
    _⇓∘_ : {X X′ Y Y′ Z Z′ : Obj} {f : X ⇒.⇒ X′} {g : Y ⇒.⇒ Y′} {h : Z ⇒.⇒ Z′}
      {u : X ⇓.⇒ Y} {v : X′ ⇓.⇒ Y′} {u′ : Y ⇓.⇒ Z} {v′ : Y′ ⇓.⇒ Z′}
      (α : cell f g u v) → (γ : cell g h u′ v′) → cell f h (u′ ⇓.∘ u) (v′ ⇓.∘ v)

  hArr : Set (ℓ₁ ⊔ ℓ₄)
  hArr = Witness ⇓._⇒_

  hCell : (u v : hArr) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₆)
  hCell = λ u v → Σ (||Pair ⇒._⇒_) (λ {(|| f g) → cell f g (wit u) (wit v)})

  hId : {u : hArr} → hCell u u
  hId {u} = || ⇒.id ⇒.id , id⇒ (wit u)

  _∘ₕ_ : {A B C : hArr} → hCell B C → hCell A B → hCell A C
  _∘ₕ_ = λ {(h₁ , c₁) (h₂ , c₂) → ||∘ ⇒._∘_ ⇒._∘_ h₂ h₁ , c₂ ⇒∘ c₁}

  vArr : Set (ℓ₁ ⊔ ℓ₂)
  vArr = Σ (Obj × Obj) (uncurry ⇒._⇒_)

  vCell : (u v : vArr) → Set (ℓ₁ ⊔ ℓ₄ ⊔ ℓ₆)
  vCell = λ u v → Σ (||Pair ⇓._⇒_) (λ {(|| f g) → cell (proj₂ u) (proj₂ v) f g})

  vId : {u : vArr} → vCell u u
  vId {u} = || ⇓.id ⇓.id , id⇓ (proj₂ u)

  _∘ᵥ_ : {A B C : vArr} → vCell B C → vCell A B → vCell A C
  _∘ᵥ_ = λ {(h₁ , c₁) (h₂ , c₂) → ||∘ ⇓._∘_ ⇓._∘_ h₂ h₁ , c₂ ⇓∘ c₁}

  field
    _≃_ : {X X′ Y Y′ : Obj} {f f′ : X ⇒.⇒ X′} {g g′ : Y ⇒.⇒ Y′} {u u′ : X ⇓.⇒ Y} {v v′ : X′ ⇓.⇒ Y′}
      → REL (cell f g u v) (cell f′ g′ u′ v′) ℓ₉

    -- _≃_ is consistent with the other relations
    consistent : {X X′ Y Y′ : Obj} {f f′ : X ⇒.⇒ X′} {g g′ : Y ⇒.⇒ Y′} {u u′ : X ⇓.⇒ Y} {v v′ : X′ ⇓.⇒ Y′}
     → {α : cell f g u v} {β : cell f′ g′ u′ v′} → α ≃ β →
     f ⇒.≈ f′ × g ⇒.≈ g′ × u ⇓.≈ u′ × v ⇓.≈ v′

  field
    Hor : IsCategory ℓ₇ hArr hCell hId _∘ₕ_
    Ver : IsCategory ℓ₈ vArr vCell vId _∘ᵥ_

    interchange-∘ : {X X′ X″ Y Y′ Y″ Z Z′ Z″ : Obj}
      {f : X ⇒.⇒ X′} {g : Y ⇒.⇒ Y′} {h : Z ⇒.⇒ Z′}
      {f′ : X′ ⇒.⇒ X″} {g′ : Y′ ⇒.⇒ Y″} {h′ : Z′ ⇒.⇒ Z″}
      {u : X ⇓.⇒ Y} {v : X′ ⇓.⇒ Y′} {w : X″ ⇓.⇒ Y″}
      {u′ : Y ⇓.⇒ Z} {v′ : Y′ ⇓.⇒ Z′} {w′ : Y″ ⇓.⇒ Z″}
      (α : cell f g u v) (β : cell f′ g′ v w)
      (γ : cell g h u′ v′) (δ : cell g′ h′ v′ w′) →
      (α ⇒∘ β) ⇓∘ (γ ⇒∘ δ) ≃ ((α ⇓∘ γ) ⇒∘ (β ⇓∘ δ))

    ⇓∘-id : ∀ {X Y Z} {u : X ⇓.⇒ Y} {u′ : Y ⇓.⇒ Z} → id⇒ u ⇓∘ id⇒ u′ ≃ id⇒ (u′ ⇓.∘ u)
    ⇒∘-id : ∀ {X X′ X″} {f : X ⇒.⇒ X′} {f′ : X′ ⇒.⇒ X″} → id⇓ f ⇒∘ id⇓ f′ ≃ id⇓ (f′ ⇒.∘ f)
    idid : ∀ {X} → id⇒ (⇓.id {X}) ≃ id⇓ (⇒.id {X})
