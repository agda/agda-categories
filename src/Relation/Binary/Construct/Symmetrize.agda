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
    A B : Set c

data ZigZag (_∼_ : Rel A ℓ₂) : (x y : A) (begin end : Direction) → Set (levelOfTerm x ⊔ ℓ₂) where
  zig : ∀ {x y z e} (first : x ∼ y) (rest : ZigZag _∼_ y z ↗ e) → ZigZag _∼_ x z ↘ e
  zag : ∀ {x y z e} (first : y ∼ x) (rest : ZigZag _∼_ y z ↘ e) → ZigZag _∼_ x z ↗ e
  slish : ∀ {x y} (last : x ∼ y) → ZigZag _∼_ x y ↘ ↘
  slash : ∀ {x y} (last : y ∼ x) → ZigZag _∼_ x y ↗ ↗

data Alternating (_∼_ : A → A → Set ℓ₂) (x y : A) : Set (levelOfTerm x ⊔ ℓ₂) where
  disorient : ∀ {begin end} (zz : ZigZag _∼_ x y begin end) → Alternating _∼_ x y

module _ {_<_ : Rel A ℓ₁} {_≺_ : Rel B ℓ₂} (f : A → B) (inj : _<_ =[ f ]⇒ _≺_) where

  map-zigzag : ∀ {x y b e} → ZigZag _<_ x y b e → ZigZag _≺_ (f x) (f y) b e
  map-zigzag (zig first z) = zig (inj first) (map-zigzag z)
  map-zigzag (zag first z) = zag (inj first) (map-zigzag z)
  map-zigzag (slish last)  = slish (inj last)
  map-zigzag (slash last)  = slash (inj last)

  map-alt : ∀ {x y} → Alternating _<_ x y → Alternating _≺_ (f x) (f y)
  map-alt (disorient zz) = disorient (map-zigzag zz)

module _ (P : Preorder c ℓ₁ ℓ₂) where
  private
    module P = Preorder P
    open P using (Carrier; _∼_)

  zigZag : (x y : Carrier) (begin end : Direction) → Set (c ⊔ ℓ₂)
  zigZag = ZigZag _∼_

  private
    sym′ : ∀ {x y z} {begin middle end} →
             zigZag y z middle end →
             zigZag y x middle begin →
             zigZag z x (rotate end) begin
    sym′ (zig first rest) accum = sym′ rest (zag first accum)
    sym′ (zag first rest) accum = sym′ rest (zig first accum)
    sym′ (slish last) accum     = zag last accum
    sym′ (slash last) accum     = zig last accum

  sym : ∀ {x y begin end} → zigZag x y begin end → zigZag y x (rotate end) (rotate begin)
  sym (zig first rest) = sym′ rest (slash first)
  sym (zag first rest) = sym′ rest (slish first)
  sym (slish last)     = slash last
  sym (slash last)     = slish last

  trans : ∀ {x y z begin end begin′ end′} → zigZag x y begin end → zigZag y z begin′ end′ → zigZag x z begin end′
  trans (zig first rest) yz           = zig first (trans rest yz)
  trans (zag first rest) yz           = zag first (trans rest yz)
  trans (slish last) (zig first rest) = zig (Preorder.trans P last first) rest
  trans (slish last) (zag first rest) = zig last (zag first rest)
  trans (slish last) (slish only)     = slish (Preorder.trans P last only)
  trans (slish last) (slash only)     = zig last (slash only)
  trans (slash last) (zig first rest) = zag last (zig first rest)
  trans (slash last) (zag first rest) = zag (Preorder.trans P first last) rest
  trans (slash last) (slish only)     = zag last (slish only)
  trans (slash last) (slash only)     = slash (Preorder.trans P only last)

  alternating : (x y : Carrier) → Set (c ⊔ ℓ₂)
  alternating = Alternating _∼_

  isEquivalence : IsEquivalence alternating
  isEquivalence = record
    { refl  = disorient (slash (Preorder.refl P))
    ; sym   = λ where (disorient zz) → disorient (sym zz)
    ; trans = λ where (disorient ij) (disorient jk) → disorient (trans ij jk)
    }

  setoid : Setoid c (c ⊔ ℓ₂)
  setoid = record
    { Carrier       = Carrier
    ; _≈_           = alternating
    ; isEquivalence = isEquivalence
    }

  -- the main eliminators for alternating -- they prove that any equivalence that
  -- respects the base preorder also respects its alternating completion.
  locally-minimal : ∀ {ℓ′} {_≈_ : Rel Carrier ℓ′} (≈-isEquivalence : IsEquivalence _≈_) →
                      _∼_ ⇒ _≈_ → alternating ⇒ _≈_
  locally-minimal {_} {_≋_} isEq inj (disorient zz) = impl zz
    where
    open IsEquivalence isEq renaming (sym to >sym; trans to _>trans>_)

    impl : {i j : Preorder.Carrier P} {b e : Direction} → zigZag i j b e → i ≋ j
    impl (zig first rest) = inj first >trans> impl rest
    impl (zag first rest) = >sym (inj first) >trans> impl rest
    impl (slish last)     = inj last
    impl (slash last)     = >sym (inj last)

  minimal : ∀ {c′ ℓ′} (Dest : Setoid c′ ℓ′) (f : Carrier → Setoid.Carrier Dest) →
            (_∼_ =[ f ]⇒ Setoid._≈_ Dest) → (alternating =[ f ]⇒ Setoid._≈_ Dest)
  minimal Dest f inj = locally-minimal (on-preserves-equivalence f (Setoid.isEquivalence Dest)) inj
