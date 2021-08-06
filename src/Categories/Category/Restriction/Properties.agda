{-# OPTIONS --without-K --safe #-}

-- Some properties of Restriction Categories

-- The first few lemmas are from Cocket & Lack, Lemma 2.1
module Categories.Category.Restriction.Properties where

open import Level using (Level; _⊔_)

open import Categories.Category.Core using (Category)
open import Categories.Category.Restriction using (Restriction)
open import Categories.Morphism using (Mono)
open import Categories.Morphism.Idempotent using (Idempotent)

private
  variable
    o ℓ e : Level
    𝒞 : Category o ℓ e

module _ (R : Restriction 𝒞) where
  open Category 𝒞
  open Restriction R
  open HomReasoning

  private
    variable
      A B C : Obj
      f : A ⇒ B
      g : B ⇒ C

  ↓f-idempotent : (A ⇒ B) → Idempotent 𝒞 A
  ↓f-idempotent f = record { idem = f ↓ ; idempotent = ⟺ ↓-denestʳ ○ ↓-cong pidʳ }

  -- a special version of ↓ being a partial left identity
  ↓-pidˡ-gf : f ↓ ∘ (g ∘ f) ↓ ≈ (g ∘ f) ↓
  ↓-pidˡ-gf {f = f} {g = g} = begin
    f ↓ ∘ (g ∘ f) ↓   ≈⟨ ↓-comm ⟩
    (g ∘ f) ↓ ∘ f ↓   ≈˘⟨ ↓-denestʳ ⟩
    ((g ∘ f) ∘ f ↓) ↓ ≈⟨ ↓-cong assoc ⟩
    (g ∘ (f ∘ f ↓)) ↓ ≈⟨ ↓-cong (∘-resp-≈ʳ pidʳ) ⟩
    (g ∘ f) ↓ ∎

  -- left denesting looks different in its conclusion
  ↓-denestˡ : (g ↓ ∘ f) ↓ ≈ (g ∘ f) ↓
  ↓-denestˡ {g = g} {f = f} = begin
    (g ↓ ∘ f) ↓       ≈⟨ ↓-cong ↓-skew-comm ⟩
    (f ∘ (g ∘ f) ↓) ↓ ≈⟨ ↓-denestʳ ⟩
    f ↓ ∘ (g ∘ f) ↓   ≈⟨ ↓-pidˡ-gf ⟩
    (g ∘ f) ↓         ∎

  ↓-idempotent : f ↓ ↓ ≈ f ↓
  ↓-idempotent {f = f} = begin
    f ↓ ↓        ≈˘⟨ ↓-cong identityʳ ⟩
    (f ↓ ∘ id) ↓ ≈⟨ ↓-denestˡ ⟩
    (f ∘ id) ↓   ≈⟨ ↓-cong identityʳ ⟩
    f ↓ ∎

  ↓↓denest : (g ↓ ∘ f ↓) ↓ ≈ g ↓ ∘ f ↓
  ↓↓denest {g = g} {f = f} = begin
    (g ↓ ∘ f ↓) ↓ ≈⟨ ↓-denestʳ ⟩
    g ↓ ↓ ∘ f ↓   ≈⟨ (↓-idempotent ⟩∘⟨refl) ⟩
    g ↓ ∘ f ↓ ∎

  Mono⇒f≈id : Mono 𝒞 f → f ↓ ≈ id
  Mono⇒f≈id {f = f} mono = mono (f ↓) id (pidʳ ○ ⟺ identityʳ)

  -- if the domain of g is at least that of f, then the restriction coincides
  ↓⊃⇒≈ : f ∘ g ↓ ≈ f → f ↓ ≈ f ↓ ∘ g ↓
  ↓⊃⇒≈ {f = f} {g = g} fg↓≈f = ⟺ (↓-cong fg↓≈f) ○ ↓-denestʳ
