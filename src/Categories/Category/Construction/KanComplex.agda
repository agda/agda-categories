{-# OPTIONS --without-K --safe #-}


open import Level

-- Kan Complexes
--
-- These are technically "Algebraic" Kan Complexes, as they come with a choice of fillers
-- However, this notion is far easier than the more geometric flavor,
-- as we can sidestep questions about choice.

module Categories.Category.Construction.KanComplex (o ℓ : Level) where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; inject₁)

open import Categories.Category using (Category)

open import Categories.Category.Instance.SimplicialSet using (SimplicialSet)
open import Categories.Category.Instance.SimplicialSet.Properties o ℓ using (ΔSet; Δ[_]; Λ[_,_]; Λ-inj)

open Category (SimplicialSet o ℓ)

-- A Kan complex is a simplicial set where every k-horn has a filler.
record IsKanComplex (X : ΔSet) : Set (o ⊔ ℓ) where
  field
    filler      : ∀ {n} {k} → Λ[ n , k ] ⇒ X → Δ[ n ] ⇒ X
    filler-cong : ∀ {n} {k} → {f g : Λ[ n , k ] ⇒ X} → f ≈ g → filler {n} f ≈ filler g
    is-filler   : ∀ {n} {k} → (f : Λ[ n , k ] ⇒ X) → filler f ∘ Λ-inj k ≈ f

-- 'inner k' will embed 'k : Fin n' into the "inner" portion of 'Fin (n + 2)'
-- Visually, it looks a little something like:
-- 
--   * * *
--   | | | 
--   v v v
-- * * * * *
-- 
-- Note that this is set up in such a way that we can normalize
-- as far as possible without pattern matching on 'i' in proofs.
inner : ∀ {n} → Fin n → Fin (ℕ.suc (ℕ.suc n))
inner i = Fin.suc (inject₁ i)

-- A Weak Kan complex is similar to a Kan Complex, but where only "inner horns" have fillers.
--
-- The indexing here is tricky, but it lets us avoid extra proof conditions that the horn is an inner horn.
-- The basic idea is that if we want an n-dimensional inner horn, then we only want to allow the faces {1,2,3...n-1}
-- to be missing. We could do this by requiring proofs that the missing face is greater than 0 and less than n, but
-- this makes working with the definition _extremely_ difficult.
--
-- To avoid this, we only allow an missing face index that ranges from 0 to n-2, and then embed that index
-- into the full range of face indexes via 'inner'. This does require us to shift our indexes around a bit.
-- To make this indexing more obvious, we use the suggestively named variable 'n-2'.
record IsWeakKanComplex (X : ΔSet) : Set (o ⊔ ℓ) where
  field
    filler      : ∀ {n-2} {k : Fin n-2} → Λ[ ℕ.suc (ℕ.suc n-2) , inner k ] ⇒ X → Δ[ ℕ.suc (ℕ.suc n-2) ] ⇒ X
    filler-cong : ∀ {n-2} {k : Fin n-2} → {f g : Λ[ ℕ.suc (ℕ.suc n-2) , inner k ] ⇒ X} → f ≈ g → filler f ≈ filler g
    is-filler   : ∀ {n-2} {k : Fin n-2} → (f : Λ[ ℕ.suc (ℕ.suc n-2) , inner k ] ⇒ X) → filler f ∘ Λ-inj (inner k) ≈ f

KanComplex⇒WeakKanComplex : ∀ {X} → IsKanComplex X → IsWeakKanComplex X
KanComplex⇒WeakKanComplex complex = record { IsKanComplex complex }
