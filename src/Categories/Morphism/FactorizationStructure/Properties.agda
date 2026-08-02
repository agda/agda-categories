{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Morphism.Lifts using (MorphismClass)
open import Relation.Unary using (_∈_)

open import Categories.Morphism.FactorizationStructure.Core using (FactorizationStructure)

-- Consider an ℰ,ℳ-factorization system on a category 𝒞:
module Categories.Morphism.FactorizationStructure.Properties
       {o ℓ eq} {𝒞 : Category o ℓ eq}
       {ℓℰ ℓℳ} {ℰ : MorphismClass 𝒞 ℓℰ} {ℳ : MorphismClass 𝒞 ℓℳ}
       (ℰ,ℳ-structured : FactorizationStructure 𝒞 ℰ ℳ)
       where

open import Level

open import Categories.Morphism.Reasoning 𝒞
open import Categories.Morphism.Properties 𝒞 using (id-is-iso)
open Category 𝒞
open Definitions 𝒞
open import Categories.Morphism.Lifts 𝒞 hiding (MorphismClass)
open import Categories.Morphism {o} {ℓ} {eq} 𝒞 using (IsIso)
open import Categories.Morphism.FactorizationStructure.Core 𝒞 ℰ ℳ hiding (FactorizationStructure)
open FactorizationStructure ℰ,ℳ-structured
open MorphismClassMember using (mor)

private
  variable
    A B C D : Obj

open HomReasoning

-- In the trivial commuting square, the identity is always a diagonal:
id-Diagonal : ∀ (g : A ⇒ B) (f : B ⇒ C) → Diagonal g g f f
id-Diagonal g f = record { d = id ; commˡ = identityˡ ; commʳ = identityʳ }

module Lemma-ℰ∩SplitMono (e : A ↠ B) (m : B ↣ C) {f : A ⇒ C} (diag : Diagonal (mor e) id (mor m) f) where
  open Diagonal diag
  -- This module captures a lemma that one almost never needs when working
  -- with factorization systems, but it is used in all the other proofs
  -- of the basic factorization system properties:
  --
  -- Lemmas from section 14 of
  -- Lemma 14.5 of
  -- "Abstract and Concrete Categories - The Joy of Cats"
  -- by Adámek, Herrlich, Strecker, 2004:
  --        e
  --     A ──>> B
  --     │    ╱ V
  --  id │  d╱  │ m
  --     │  ╱   │
  --     V └    V
  --     A ───> C
  --        f
  -- we have that (1) e is an isomorphism and (2) f is in ℳ.
  then-e-IsIso : IsIso (mor e)
  then-e-IsIso = record
    { inv = d
    ; iso = record
      { isoˡ = commˡ
      ; isoʳ = d-unique₂ e m e∘d (id-Diagonal (mor e) (mor m))
      }
    }
    where
      -- we consider two diagonals id and e ∘ d in
      -- the trivial square m ∘ e ≈ m ∘ e:
      open HomReasoning
      e∘d : Diagonal (mor e) (mor e) (mor m) (mor m)
      e∘d = record
        { d = mor e ∘ d
        ; commˡ = cancelʳ commˡ
        ; commʳ = begin
            mor m ∘ (mor e ∘ d)  ≈⟨ extendʳ comm ⟩
            f ∘ (id ∘ d)         ≈⟨ refl⟩∘⟨ identityˡ ⟩
            f ∘ d                ≈⟨ commʳ ⟩
            mor m                ∎
        }

  then-f∈ℳ : f ∈ ℳ
  then-f∈ℳ = ℳ-resp-≈ m∘e≈f (ℳ∘Iso m then-e-IsIso)
    where
      m∘e≈f : mor m ∘ mor e ≈ f
      m∘e≈f = comm ○ identityʳ

module Lemma-ℳ∩SplitEpi (e : A ↠ B) (m : B ↣ C) {f : A ⇒ C} (diag : Diagonal f (mor e) id (mor m)) where
  open Diagonal diag
  -- The dual version of Lemma-ℰ∩SplitMono; we prove it explicitly to avoid dependencies
  -- to Categories.Morphism.FactorizationStructure.Properties. In
  --        f
  --     A ───> C
  --     │    ╱ │
  --   e │  d╱  │ id
  --     V  ╱   │
  --     V └    V
  --     A >──> C
  --        m
  -- we have (1) m is an isomorphism and (2) f ∈ ℰ
  then-m-IsIso : IsIso (mor m)
  then-m-IsIso = record
    { inv = d
    ; iso = record
      { isoˡ = d-unique₂ e m d∘m (id-Diagonal (mor e) (mor m))
      ; isoʳ = commʳ
      }
    }
    where
      -- we consider two diagonals id and e ∘ d in
      -- the trivial square m ∘ e ≈ m ∘ e:
      open HomReasoning
      d∘m : Diagonal (mor e) (mor e) (mor m) (mor m)
      d∘m = record
        { d = d ∘ mor m
        ; commˡ = begin
            (d ∘ mor m) ∘ mor e ≈⟨ extendˡ comm ⟨
            (d ∘ id) ∘ f        ≈⟨ identityʳ ⟩∘⟨refl ⟩
            d ∘ f               ≈⟨ commˡ ⟩
            mor e ∎
        ; commʳ = cancelˡ commʳ
        }
  then-f∈ℰ : f ∈ ℰ
  then-f∈ℰ = ℰ-resp-≈ m∘e≈f (Iso∘ℰ then-m-IsIso e)
    where
      m∘e≈f : mor m ∘ mor e ≈ f
      m∘e≈f = ⟺ comm ○ identityˡ


-- --------------------------------------------------
-- ℰ and ℳ determine each other via (non-unique) diagonalization
-- where one of the vertical arrows is identity
-- --------------------------------------------------
ℰ-orthogonal⊆ℳ : ∀ (f : A ⇒ B)
                   → (∀ {D} (e : A ↠ D) → Lifts (mor e) f)
                   → f ∈ ℳ
ℰ-orthogonal⊆ℳ f f-lifts = Lemma-ℰ∩SplitMono.then-f∈ℳ e m (Filler⇒Diagonal d)
  where
    -- take the ℰ,ℳ-factorization
    open Factorization (factor f)
    -- and apply the lifting property to the ℰ-part:
    comm : CommutativeSquare (mor e) id (mor m) f
    comm = m∘e≈h ○ (⟺ identityʳ)
    d : Filler comm
    d = f-lifts e comm

ℳ-orthogonal⊆ℰ : ∀ (f : A ⇒ B)
                   → (∀ {C} (m : C ↣ B) → Lifts f (mor m))
                   → f ∈ ℰ
ℳ-orthogonal⊆ℰ f f-lifts = Lemma-ℳ∩SplitEpi.then-f∈ℰ e m (Filler⇒Diagonal d)
  where
    -- take the ℰ,ℳ-factorization
    open Factorization (factor f)
    -- and apply the lifting property to the ℰ-part:
    comm : CommutativeSquare f (mor e) id (mor m)
    comm = identityˡ ○ ⟺ m∘e≈h
    d : Filler comm
    d = f-lifts m comm

-- -----------------------------------------
-- Morphism Class Inclusions
-- -----------------------------------------
ℰ∩ℳ⊆Iso : ∀ {h : A ⇒ B} → ℰ h → ℳ h → IsIso h
ℰ∩ℳ⊆Iso {A} {B} {h} h∈ℰ h∈ℳ = record
  { inv = d
  ; iso = record
    { isoˡ = commˡ
    ; isoʳ = commʳ
    } }
  where
    -- consider the diagonal for the trivial commutative square:
    open UniqueDiagonal (diagonalization (mor∈class h∈ℰ) (mor∈class h∈ℳ) (begin
          id ∘ h   ≈⟨ identityˡ ⟩
          h        ≈⟨ identityʳ ⟨
          h ∘ id   ∎))

Iso⊆ℳ : IsIso ⊆ ℳ
Iso⊆ℳ {f = h} h⁻¹ = Lemma-ℰ∩SplitMono.then-f∈ℳ e m (record
  { d = h⁻¹ .inv ∘ mor m
  ; commˡ = begin
          (h⁻¹ .inv ∘ mor m) ∘ mor e    ≈⟨ pullʳ m∘e≈h ⟩
          h⁻¹ .inv ∘ h                  ≈⟨  h⁻¹ .isoˡ ⟩
          id                            ∎
  ; commʳ = cancelˡ (h⁻¹ .isoʳ)
  })
  where
    -- consider a factorization of h into e and m
    open Factorization (factor h)
    open IsIso
    open HomReasoning

Iso⊆ℰ : IsIso ⊆ ℰ
Iso⊆ℰ {f = h} h⁻¹ = Lemma-ℳ∩SplitEpi.then-f∈ℰ e m (record
  { d = mor e ∘ h⁻¹ .inv
  ; commˡ = cancelʳ (h⁻¹ .isoˡ)
  ; commʳ = begin
          mor m ∘ mor e ∘ h⁻¹ .inv  ≈⟨ pullˡ m∘e≈h ⟩
          h ∘ h⁻¹ .inv              ≈⟨ h⁻¹ .isoʳ ⟩
          id                        ∎
  })
  where
    -- consider a factorization of h into e and m
    open Factorization (factor h)
    open IsIso
    open HomReasoning

ℳ∘ℳ⊆ℳ : (g : B ↣ C) → (f : A ↣ B) → (mor g ∘ mor f) ∈ ℳ
ℳ∘ℳ⊆ℳ g f = Lemma-ℰ∩SplitMono.then-f∈ℳ e m d₂′
  where
    -- take the factorization m ∘ e = g ∘ f
    open Factorization (factor (mor g ∘ mor f))
    -- and then construct two diagonals:
    --        e
    --     A ────────>> Im
    --     V         ⟋╱ V
    --   id│    d₂⟋  ╱  │ m
    --     │   ⟋    ╱d₁ │
    --     V └     └    V
    --     A >──> B >─> C
    --        f      g
    open UniqueDiagonal
    open HomReasoning
    d₁ : UniqueDiagonal (mor e) (mor f) (mor m) (mor g)
    d₁ = diagonalization e g m∘e≈h
    d₂ : UniqueDiagonal (mor e) id (d₁ .d) (mor f)
    d₂ = diagonalization e f (begin
      d₁ .d ∘ mor e   ≈⟨ d₁ .commˡ ⟩
      mor f           ≈⟨ identityʳ ⟨
      mor f ∘ id      ∎)
    -- so d₂ is also a diagonal for the big square
    d₂′ : Diagonal (mor e) id (mor m) (mor g ∘ mor f)
    d₂′ = record
       { d = d₂ .d
       ; commˡ = d₂ .commˡ
       ; commʳ = glueTrianglesˡ (d₁ .commʳ) (d₂ .commʳ)
       }

ℰ∘ℰ⊆ℰ : (g : B ↠ C) → (f : A ↠ B) → (mor g ∘ mor f) ∈ ℰ
ℰ∘ℰ⊆ℰ g f = Lemma-ℳ∩SplitEpi.then-f∈ℰ e m d₂′
  where
    -- take the factorization m ∘ e = g ∘ f
    open Factorization (factor (mor g ∘ mor f))
    -- and then construct two diagonals:
    --        f      g
    --     A ──>> B ─>> C
    --     │     ╱    ⟋ │
    --    e│  d₁╱  ⟋ d₂ │ id
    --     V   ╱ ⟋      │
    --     V └  └       V
    --    Im >────────> B
    --           m
    open UniqueDiagonal
    open HomReasoning
    d₁ : UniqueDiagonal (mor f) (mor e) (mor g) (mor m)
    d₁ = diagonalization f m (⟺ m∘e≈h)
    d₂ : UniqueDiagonal (mor g) (d₁ .d) id (mor m)
    d₂ = diagonalization g m (begin
      id ∘ mor g     ≈⟨ identityˡ ⟩
      mor g          ≈⟨ d₁ .commʳ ⟨
      mor m ∘ d₁ .d  ∎)
    d₂′ : Diagonal (mor g ∘ mor f) (mor e) id (mor m)
    d₂′ = record
      { d = d₂ .d
      ; commˡ = glueTrianglesʳ (d₂ .commˡ) (d₁ .commˡ)
      ; commʳ = d₂ .commʳ
      }


