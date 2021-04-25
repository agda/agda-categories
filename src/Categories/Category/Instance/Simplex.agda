{-# OPTIONS --without-K --safe #-}


-- The Simplex category Δ
module Categories.Category.Instance.Simplex where

open import Level using (0ℓ)
open import Data.Product
open import Data.Fin.Base using (Fin; zero; suc; _≤_; _<_; inject₁)
open import Data.Nat.Base using (ℕ; zero; suc; z≤n; s≤s)
open import Function renaming (id to idF; _∘_ to _∙_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Categories.Category.Core using (Category)

--------------------------------------------------------------------------------
-- The Simplex Category
--
-- Classically, the category Δ is defined as follows:
--   * Objects are Natural Numbers
--   * Morphisms 'm ⇒ n' are order-preserving maps 'Fin m → Fin n'
--
-- We _can_ define this version of Δ, but it is generally /not/ the version we want.
-- Most of the time we work with Δ, we only care about 2 classes of maps:
--   * Face maps 'δᵢ : n ⇒ (1 + n)' whose image omits 'i'
--   * Boundary maps 'σᵢ : (1 + n) ⇒ n' such that 'σᵢ i = σᵢ (i + 1) = i'
-- It turns out that all of the maps of Δ can be decomposed into compositions
-- of these 2 classes of maps[1], so most texts will define Functors out of Δ
-- based solely how they act on these morphisms.
--
-- Therefore, we want our definition of Δ to put these morphisms front and center,
-- by encoding our homs as follows:

infix 4 _Δ⇒_
infixr 9 _⊚_

data _Δ⇒_ : ℕ → ℕ → Set where
  ε  : ∀ {n} → n Δ⇒ n
  δ  : ∀ {n} → (i : Fin (suc n)) → n Δ⇒ (suc n)
  σ  : ∀ {n} → (j : Fin n) → (suc n) Δ⇒ n
  _⊚_ : ∀ {l m n} → m Δ⇒ n → l Δ⇒ m → l Δ⇒ n

-- However, this raises some tricky questions about equality of morphisms. It is tempting
-- to use the Simplical Identities[2]:
--   * δᵢ ∘ δⱼ = δⱼ₊₁ ∘ δᵢ if i ≤ j
--   * σⱼ ∘ σᵢ = σᵢ ∘ σⱼ₊₁ if i ≤ j
--   * σⱼ ∘ δᵢ = δᵢ ∘ σⱼ₋₁ if i < j
--   * σⱼ ∘ δᵢ = id        if i = j or i = j + 1
--   * σⱼ ∘ δᵢ = δᵢ₋₁ ∘ σⱼ if j + 1 < i
--
-- However, we can do better than this. Instead, we appeal to the denotational
-- semantics of our formal chains of morphisms. In this case we interpret
-- our morphisms as maps between finite ordinals:

face : ∀ {n} → Fin (ℕ.suc n) → Fin n → Fin (ℕ.suc n)
face Fin.zero    k           = Fin.suc k
face (Fin.suc i) Fin.zero    = Fin.zero
face (Fin.suc i) (Fin.suc k) = Fin.suc (face i k)

degen : ∀ {n} → Fin n → Fin (ℕ.suc n) → Fin n
degen Fin.zero    Fin.zero    = Fin.zero
degen Fin.zero    (Fin.suc k) = k
degen (Fin.suc i) Fin.zero    = Fin.zero
degen (Fin.suc i) (Fin.suc k) = Fin.suc (degen i k)

⟦_⟧ : ∀ {m n} → m Δ⇒ n → (Fin m → Fin n)
⟦ ε ⟧ x = x
⟦ δ i ⟧ x = face i x
⟦ σ j ⟧ x = degen j x
⟦ f ⊚ g ⟧ x = ⟦ f ⟧ (⟦ g ⟧ x)

-- Now, we can define equality of morphisms by appealing to our semantics!
infix  4 _≗_

-- We wrap this in a record so that we don't compute away what the original morphsims were.
record _≗_ {m n} (f g : m Δ⇒ n) : Set where
  constructor Δ-eq
  field
    Δ-pointwise : ∀ {x} → ⟦ f ⟧ x ≡ ⟦ g ⟧ x

open _≗_ public

-- Now, we get the same benefits of being able to do induction on our input
-- arguments when trying to prove equalities, as well as being able to define functors
-- out of Δ via their action on face/degeneracy maps.

Δ : Category 0ℓ 0ℓ 0ℓ
Δ = record
  { Obj = ℕ
  ; _⇒_ = _Δ⇒_
  ; _≈_ = _≗_
  ; id = ε
  ; _∘_ = _⊚_
  ; assoc = Δ-eq refl
  ; sym-assoc = Δ-eq refl
  ; identityˡ = Δ-eq refl
  ; identityʳ = Δ-eq refl
  ; identity² = Δ-eq refl
  ; equiv = record
    { refl = Δ-eq refl
    ; sym = λ eq → Δ-eq (sym (Δ-pointwise eq))
    ; trans = λ eq₁ eq₂ → Δ-eq (trans (Δ-pointwise eq₁) (Δ-pointwise eq₂))
    }
  ; ∘-resp-≈ = λ {_ _ _ f g h i} eq₁ eq₂ → Δ-eq (trans (cong ⟦ f ⟧ (Δ-pointwise eq₂)) (Δ-pointwise eq₁))
  }


-- For completeness, here are the aforementioned simplical identities. These may seem /slightly/
-- different than the ones presented before, but it's just re-indexing to avoid having to use 'pred'.
open Category Δ

-- δᵢ ∘ δⱼ = δⱼ₊₁ ∘ δᵢ if i ≤ j
face-comm : ∀ {n} {i j : Fin (suc n)}  → i ≤ j → δ (inject₁ i) ∘ δ j ≈ δ (suc j) ∘ δ i
face-comm {_} {zero}  {j}     z≤n      = Δ-eq refl
face-comm {_} {suc i} {suc j} (s≤s le) = Δ-eq (λ { {zero} → refl ; {suc x} → cong suc (Δ-pointwise (face-comm le)) })

-- σⱼ ∘ σᵢ = σᵢ ∘ σⱼ₊₁ if i ≤ j
degen-comm : ∀ {n} {i j : Fin n} → i ≤ j → σ j ∘ σ (inject₁ i) ≈ σ i ∘ σ (suc j)
degen-comm {_} {zero}  {zero}  z≤n      = Δ-eq λ { {zero} → refl ; {suc x} → refl }
degen-comm {_} {zero}  {suc j} z≤n      = Δ-eq λ { {zero} → refl ; {suc x} → refl }
degen-comm {_} {suc i} {suc j} (s≤s le) = Δ-eq (λ { {zero} → refl ; {suc x} → cong suc (Δ-pointwise (degen-comm le)) })

-- σⱼ ∘ δᵢ = δᵢ ∘ σⱼ₋₁ if i < j
degen-face-comm : ∀ {n} {i : Fin (suc n)} {j : Fin n} → i < suc j → σ (suc j) ∘ δ (inject₁ i) ≈ δ i ∘ σ j
degen-face-comm {_} {zero}  {j}     (s≤s le) = Δ-eq refl
degen-face-comm {_} {suc i} {suc j} (s≤s le) = Δ-eq (λ { {zero} → refl ; {suc x} → cong suc (Δ-pointwise (degen-face-comm le)) })

-- σⱼ ∘ δᵢ = id        if i = j
degen-face-id : ∀ {n} {i j : Fin n} → i ≡ j → σ j ∘ δ (inject₁ i) ≈ id
degen-face-id {_} {zero}  {zero}  refl = Δ-eq refl
degen-face-id {_} {suc i} {suc i} refl = Δ-eq (λ { {zero} → refl ; {suc x} → cong suc (Δ-pointwise (degen-face-id {i = i} refl)) })

-- σⱼ ∘ δᵢ = id        if i = j + 1
degen-face-suc-id : ∀ {n} {i : Fin (suc n)} {j : Fin n} → i ≡ suc j → σ j ∘ δ i ≈ id
degen-face-suc-id {_} {suc zero}    {zero}  refl = Δ-eq λ { {zero} → refl ; {suc x} → refl }
degen-face-suc-id {_} {suc (suc i)} {suc i} refl = Δ-eq λ { {zero} → refl ; {suc x} → cong suc (Δ-pointwise (degen-face-suc-id {i = suc i} refl)) }

-- σⱼ ∘ δᵢ = δᵢ₋₁ ∘ σⱼ if j + 1 < i
degen-face-suc-comm : ∀ {n} {i : Fin (suc n)} {j : Fin n} → suc j < i → σ (inject₁ j) ∘ δ (suc i) ≈ δ i ∘ σ j
degen-face-suc-comm {_} {suc (suc i)} {zero}  (s≤s (s≤s z≤n)) = Δ-eq (λ { {zero} → refl ; {suc x} → refl })
degen-face-suc-comm {_} {suc (suc i)} {suc j} (s≤s le)        = Δ-eq (λ { {zero} → refl ; {suc x} → cong suc (Δ-pointwise (degen-face-suc-comm le)) })

-- Further Work:
-- If we had a means of decomposing any monotone map 'Fin n ⇒ Fin m' into a series of face/boundary
-- maps, we would be able to compute normal forms in Δ by using normalization by evaluation. This is
-- very promising, as it would let us define a reflection tactic to automatically perform
-- proofs about chains of morphisms in Δ.

-- Footnotes:
-- 1. For a proof of this, see Categories for The Working Mathematician VII.5
-- 2. See https://ncatlab.org/nlab/show/simplex+category
