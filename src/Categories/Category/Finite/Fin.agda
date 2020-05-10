{-# OPTIONS --without-K --safe #-}

module Categories.Category.Finite.Fin where

open import Level
open import Data.Nat.Base using (ℕ)
open import Data.Vec.Base as Vec using (Vec)
open import Data.List.Base
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Axiom.UniquenessOfIdentityProofs
open import Relation.Binary using (Rel ; Decidable)
open import Relation.Binary.PropositionalEquality as ≡
open import Function.Base using (flip)

open import Categories.Category

record Arrow (n : ℕ) (∣_⇒_∣ : Fin n → Fin n → ℕ) : Set where
  field
    dom : Fin n
    cod : Fin n
    arr : Fin ∣ dom ⇒ cod ∣

-- a hasShape of a finite catgegory
--
-- Classically, a finite category has a finite number of objects and a finite number
-- of morphisms. However, in this library, we cannot conveniently count the number of
-- objects and morphisms, because morphisms are identified up to the underlying
-- equivalence and objects have no general notion of identity. As a result, the
-- classical definition fails.
--
-- Nevetheless, if we know precisely what the objects and morphisms are, then we might
-- be able to count them. As a result, finite categories are just adjoint equivalent
-- to some category with a finite hasShape. Motivated by this idea, we can consider a
-- category with both objects and morphisms represented by Fin. We know Fin has
-- decidable equality and consequently also UIP. This allows us to operate
-- classically. We additionally require categorical axioms and thus ensure all shapes
-- form categories.
record HasFinCatShape (n : ℕ) (∣_⇒_∣ : Fin n → Fin n → ℕ) : Set where
  infix  4 _⇒_
  infixr 9 _∘_

  _⇒_ : Rel (Fin n) 0ℓ
  a ⇒ b = Fin ∣ a ⇒ b ∣

  field
    id  : ∀ {a} → a ⇒ a
    _∘_ : ∀ {a b c} → b ⇒ c → a ⇒ b → a ⇒ c

  field
    assoc     : ∀ {a b c d} {f : a ⇒ b} {g : b ⇒ c} {h : c ⇒ d} → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
    sym-assoc : ∀ {a b c d} {f : a ⇒ b} {g : b ⇒ c} {h : c ⇒ d} → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
    identityˡ : ∀ {a b} {f : a ⇒ b} → id ∘ f ≡ f
    identityʳ : ∀ {a b} {f : a ⇒ b} → f ∘ id ≡ f
    identity² : ∀ {a} → id {a} ∘ id ≡ id
    ∘-resp-≈  : ∀ {a b c} {f h : b ⇒ c} {g i : a ⇒ b} → f ≡ h → g ≡ i → f ∘ g ≡ h ∘ i

  objects : List (Fin n)
  objects = allFin n

  wrap-arr : ∀ {d c} (f : Fin ∣ d ⇒ c ∣) → Arrow n ∣_⇒_∣
  wrap-arr f = record { arr = f }

  morphisms : List (Arrow n ∣_⇒_∣)
  morphisms = concatMap (λ d → concatMap (λ c → tabulate (wrap-arr {d} {c})) objects) objects

  Obj-≟ : Decidable {A = Fin n} _≡_
  Obj-≟ = _≟_

  objects-vec : Vec (Fin n) n
  objects-vec = Vec.allFin n

  ⇒-≟ : ∀ {a b} → Decidable {A = a ⇒ b} _≡_
  ⇒-≟ = _≟_

  Obj-UIP : UIP (Fin n)
  Obj-UIP = Decidable⇒UIP.≡-irrelevant Obj-≟

  ⇒-UIP : ∀ {a b} → UIP (a ⇒ b)
  ⇒-UIP = Decidable⇒UIP.≡-irrelevant ⇒-≟

record FinCatShape : Set where
  infix 9 ∣_⇒_∣

  field
    size     : ℕ
    ∣_⇒_∣    : Fin size → Fin size → ℕ
    hasShape : HasFinCatShape size ∣_⇒_∣

  open HasFinCatShape hasShape public

  op : FinCatShape
  op = record
    { size     = size
    ; ∣_⇒_∣    = flip ∣_⇒_∣
    ; hasShape = record
      { id        = id
      ; _∘_       = flip _∘_
      ; assoc     = sym-assoc
      ; sym-assoc = assoc
      ; identityˡ = identityʳ
      ; identityʳ = identityˡ
      ; identity² = identity²
      ; ∘-resp-≈  = flip ∘-resp-≈
      }
    }

private
  shape-involutive : (shape : FinCatShape) → shape ≡ FinCatShape.op (FinCatShape.op shape)
  shape-involutive _ = refl

  record FinCatShape′ : Set where
    field
      size     : ℕ
      ∣_⇒_∣    : Fin size → Fin size → ℕ

    _⇒_ : Rel (Fin size) 0ℓ
    a ⇒ b = Fin ∣ a ⇒ b ∣

    field
      id  : ∀ {a} → a ⇒ a
      _∘_ : ∀ {a b c} → b ⇒ c → a ⇒ b → a ⇒ c

    field
      assoc     : ∀ {a b c d} {f : a ⇒ b} {g : b ⇒ c} {h : c ⇒ d} → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
      identityˡ : ∀ {a b} {f : a ⇒ b} → id ∘ f ≡ f
      identityʳ : ∀ {a b} {f : a ⇒ b} → f ∘ id ≡ f

shapeHelper : FinCatShape′ → FinCatShape
shapeHelper s = record
  { size     = size
  ; ∣_⇒_∣    = ∣_⇒_∣
  ; hasShape = record
    { id        = id
    ; _∘_       = _∘_
    ; assoc     = assoc
    ; sym-assoc = sym assoc
    ; identityˡ = identityˡ
    ; identityʳ = identityʳ
    ; identity² = identityˡ
    ; ∘-resp-≈  = cong₂ _∘_
    }
  }
  where open FinCatShape′ s

FinCategory : FinCatShape → Category 0ℓ 0ℓ 0ℓ
FinCategory s = record
  { Obj       = Fin size
  ; _⇒_       = _⇒_
  ; _≈_       = _≡_
  ; id        = id
  ; _∘_       = _∘_
  ; assoc     = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv     = ≡.isEquivalence
  ; ∘-resp-≈  = ∘-resp-≈
  }
  where open FinCatShape s

private
  opposite-functorial : (shape : FinCatShape) →
                        FinCategory (FinCatShape.op shape) ≡ Category.op (FinCategory shape)
  opposite-functorial _ = refl
