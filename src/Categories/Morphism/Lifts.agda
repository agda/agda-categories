{-# OPTIONS --without-K --safe #-}

open import Categories.Category
import Categories.Morphism.Reasoning

-- Lifting Properties
module Categories.Morphism.Lifts {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level

open Category 𝒞
open Definitions 𝒞
open Categories.Morphism.Reasoning 𝒞 using (pullˡ)

-- A pair of morphisms has the lifting property if every commutative
-- square admits a diagonal filler. We say that 'i' has the left lifting
-- property with respect to 'p', and that 'p' has the right lifting property
-- with respect to 'i'.
--
-- Graphically, the situation is as follows:
--
--      f
--   A ────> X
--   │     ^ │
--   │  ∃ ╱  │
-- i │   ╱   │ p
--   │  ╱    │
--   V ╱     V
--   B ────> Y
--      g
--
-- Note that the filler is /not/ required to be unique.
--
-- For ease of use, we define lifts in two steps:
-- * 'Filler' describes the data required to fill a /particular/ commutative square.
-- * 'Lifts' then quantifies over all commutative squares.

record Filler {A B X Y} {i : A ⇒ B} {f : A ⇒ X} {g : B ⇒ Y} {p : X ⇒ Y}
              (comm : CommutativeSquare i f g p) : Set (ℓ ⊔ e) where
  field
    filler : B ⇒ X
    fill-commˡ : filler ∘ i ≈ f
    fill-commʳ : p ∘ filler ≈ g

Lifts : ∀ {A B X Y} → (i : A ⇒ B) → (p : X ⇒ Y) → Set (ℓ ⊔ e)
Lifts i p = ∀ {f g} → (comm : CommutativeSquare i f g p) → Filler comm
-- The diagonal in a square. The record does not require the square to commute
-- but rather deduces this from the existence of the diagonal.
-- The reason is that if the record is parametrized by a morphism equality,
-- then record types differ if there are multiple (unequal) proofs of
-- morphism equality. Then, properties like FactorizationSystem.diag-unique₂
-- would become more complicated. Thus, Diagonal does not use
-- above Filler record, which is parametric in a morphism equality.
record Diagonal {A B C D} (i : A ⇒ B) (f : A ⇒ C)
                (g : B ⇒ D) (p : C ⇒ D) : Set (ℓ ⊔ e) where
  field
    --      i
    --   A ────> B
    --   │     / │
    --   │  d ╱  │
    -- f │   ╱   │ g
    --   │  ╱    │
    --   V V     V
    --    C ───> D
    --      m
    d : B ⇒ C
    commˡ : d ∘ i ≈ f
    commʳ : p ∘ d ≈ g

  comm : CommutativeSquare i f g p
  comm = begin
    g ∘ i      ≈⟨ pullˡ commʳ ⟨
    p ∘ d ∘ i  ≈⟨ refl⟩∘⟨ commˡ ⟩
    p ∘ f      ∎
    where open HomReasoning

  toFiller : Filler comm
  toFiller = Filler.constructor d commˡ commʳ

Filler⇒Diagonal : ∀ {A B X Y} {i : A ⇒ B} {f : A ⇒ X} {g : B ⇒ Y} {p : X ⇒ Y}
                  {comm : CommutativeSquare i f g p}
                  → Filler comm
                  → Diagonal i f g p
Filler⇒Diagonal f = record { d = filler ; commˡ = fill-commˡ ; commʳ = fill-commʳ }
  where open Filler f

record UniqueDiagonal {A B X Y} (i : A ⇒ B) (f : A ⇒ X)
                      (g : B ⇒ Y) (p : X ⇒ Y) : Set (ℓ ⊔ e) where
  field
    diagonal : Diagonal i f g p
  open Diagonal diagonal public
  field
    unique : ∀ (v : Diagonal i f g p) → d ≈ Diagonal.d v

  unique₂ : ∀ (v w : Diagonal i f g p) → Diagonal.d v ≈ Diagonal.d w
  unique₂ v w = begin
    Diagonal.d v  ≈⟨ unique v ⟨
    d             ≈⟨ unique w ⟩
    Diagonal.d w  ∎
    where open HomReasoning



--------------------------------------------------------------------------------
-- Lifings of Morphism Classes

-- Shorthand for denoting a class of morphisms.
MorphismClass : (p : Level) → Set (o ⊔ ℓ ⊔ suc p)
MorphismClass p = ∀ {X Y} → X ⇒ Y → Set p

≈-closed : {p : Level} → (M : MorphismClass p) → Set (o ⊔ ℓ ⊔ e ⊔ p)
≈-closed M = ∀ {X Y} → {f g : X ⇒ Y} → f ≈ g → M f → M g

-- Bundled structure for members of a morphism class
record MorphismClassMember {p : Level} (M : MorphismClass p) (A B : Obj) : Set (p ⊔ ℓ) where
  field
    mor : A ⇒ B
    in-class : M mor

-- A morphism 'i' is called "projective" with respect to some morphism class 'J'
-- if it has the left-lifting property against every element of 'J'.
Projective : ∀ {j} {A B} → MorphismClass j → (i : A ⇒ B) → Set (o ⊔ ℓ ⊔ e ⊔ j)
Projective J i = ∀ {X Y} → (f : X ⇒ Y) → J f → Lifts i f

-- Dually, a morphism 'i' is called "injective" with repsect to a morphism class 'J'
-- if it has the right-lifting property against every element of 'J'.
Injective : ∀ {j} {A B} → MorphismClass j → (i : A ⇒ B) → Set (o ⊔ ℓ ⊔ e ⊔ j)
Injective J i = ∀ {X Y} → (f : X ⇒ Y) → J f → Lifts f i

-- The class of J-Projective morphisms.
Proj : ∀ {j} (J : MorphismClass j) → MorphismClass (o ⊔ ℓ ⊔ e ⊔ j)
Proj J = Projective J

-- The class of J-Injective morphisms.
Inj : ∀ {j} (J : MorphismClass j) → MorphismClass (o ⊔ ℓ ⊔ e ⊔ j)
Inj J = Injective J
