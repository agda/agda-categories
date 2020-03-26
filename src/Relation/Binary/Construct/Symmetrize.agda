{-# OPTIONS --without-K --safe #-}
-- Take a relation that is already reflexive and transitive
-- and make it symmetric.
--   (Borrowed from Categories/Support/ZigZag from copumpkin's Categories library

module Relation.Binary.Construct.Symmetrize where

open import Level
open import Relation.Binary
open import Relation.Binary.Construct.On using () renaming (isEquivalence to on-preserves-equivalence)

data Direction : Set where
  ↘ ↗ : Direction

rotate : Direction → Direction
rotate ↘ = ↗
rotate ↗ = ↘

private
  variable
    c ℓ₁ ℓ₂ : Level
    Carrier : Set c

data ZigZag′ (_∼_ : Rel Carrier ℓ₂) : (x y : Carrier) (begin end : Direction) → Set (levelOfTerm x ⊔ ℓ₂) where
  zig : ∀ {x y z e} (first : x ∼ y) (rest : ZigZag′ _∼_ y z ↗ e) → ZigZag′ _∼_ x z ↘ e
  zag : ∀ {x y z e} (first : y ∼ x) (rest : ZigZag′ _∼_ y z ↘ e) → ZigZag′ _∼_ x z ↗ e
  slish : ∀ {x y} (last : x ∼ y) → ZigZag′ _∼_ x y ↘ ↘
  slash : ∀ {x y} (last : y ∼ x) → ZigZag′ _∼_ x y ↗ ↗

data Alternating′ (_∼_ : Carrier → Carrier → Set ℓ₂) (x y : Carrier) : Set (levelOfTerm x ⊔ ℓ₂) where
  disorient : ∀ {begin end} (zz : ZigZag′ _∼_ x y begin end) → Alternating′ _∼_ x y

module _ (Base : Preorder c ℓ₁ ℓ₂) where

  ZigZag : (x y : Preorder.Carrier Base) (begin end : Direction) → Set (c ⊔ ℓ₂)
  ZigZag = ZigZag′ (Preorder._∼_ Base)

  private
    sym′ : {x y z : Preorder.Carrier Base} {begin middle end : Direction} → ZigZag y z middle end →
           ZigZag y x middle begin → ZigZag z x (rotate end) begin
    sym′ (zig first rest) accum = sym′ rest (zag first accum)
    sym′ (zag first rest) accum = sym′ rest (zig first accum)
    sym′ (slish last) accum     = zag last accum
    sym′ (slash last) accum     = zig last accum

  sym : ∀ {x y begin end} → ZigZag x y begin end → ZigZag y x (rotate end) (rotate begin)
  sym (zig first rest) = sym′ rest (slash first)
  sym (zag first rest) = sym′ rest (slish first)
  sym (slish last)     = slash last
  sym (slash last)     = slish last

  trans : ∀ {x y z begin end begin′ end′} → ZigZag x y begin end → ZigZag y z begin′ end′ → ZigZag x z begin end′
  trans (zig first rest) yz = zig first (trans rest yz)
  trans (zag first rest) yz = zag first (trans rest yz)
  trans (slish last) (zig first rest) = zig (Preorder.trans Base last first) rest
  trans (slish last) (zag first rest) = zig last (zag first rest)
  trans (slish last) (slish only) = slish (Preorder.trans Base last only)
  trans (slish last) (slash only) = zig last (slash only)
  trans (slash last) (zig first rest) = zag last (zig first rest)
  trans (slash last) (zag first rest) = zag (Preorder.trans Base first last) rest
  trans (slash last) (slish only) = zag last (slish only)
  trans (slash last) (slash only) = slash (Preorder.trans Base only last)

  Alternating : (x y : Preorder.Carrier Base) → Set (c ⊔ ℓ₂)
  Alternating = Alternating′ (Preorder._∼_ Base)

  private
    is-equivalence : IsEquivalence Alternating
    is-equivalence = record
      { refl = disorient (slash (Preorder.refl Base))
      ; sym = λ where (disorient zz) → disorient (sym zz)
      ; trans = λ where (disorient ij) (disorient jk) → disorient (trans ij jk)
      }

  setoid : Setoid c (c ⊔ ℓ₂)
  setoid = record
    { Carrier = Preorder.Carrier Base
    ; _≈_ = Alternating
    ; isEquivalence = is-equivalence
    }

  -- the main eliminators for Alternating -- they prove that any equivalence that
  -- respects the base preorder also respects its Alternating completion.
  locally-minimal : ∀ {ℓ′} {_≈_ : Rel (Preorder.Carrier Base) ℓ′} (≈-isEquivalence : IsEquivalence _≈_) →
    (Preorder._∼_ Base ⇒ _≈_) → (Alternating ⇒ _≈_)
  locally-minimal {_} {_≋_} isEq inj (disorient zz) = impl zz
    where
    open IsEquivalence isEq renaming (sym to >sym; trans to _>trans>_)

    impl : {i j : Preorder.Carrier Base} {b e : Direction} → ZigZag i j b e → i ≋ j
    impl (zig first rest) = inj first >trans> impl rest
    impl (zag first rest) = >sym (inj first) >trans> impl rest
    impl (slish last) = inj last
    impl (slash last) = >sym (inj last)

  minimal : ∀ {c′ ℓ′} (Dest : Setoid c′ ℓ′) (f : Preorder.Carrier Base → Setoid.Carrier Dest) →
            (Preorder._∼_ Base =[ f ]⇒ Setoid._≈_ Dest) → (Alternating =[ f ]⇒ Setoid._≈_ Dest)
  minimal Dest f inj = locally-minimal (on-preserves-equivalence f (Setoid.isEquivalence Dest)) inj
