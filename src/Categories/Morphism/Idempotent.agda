{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core

-- Idempotents and Split Idempotents
module Categories.Morphism.Idempotent {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level

open import Categories.Morphism.Reasoning 𝒞

open Category 𝒞
open HomReasoning

record Idempotent (A : Obj) : Set (ℓ ⊔ e) where
  field
    idem       : A ⇒ A
    idempotent : idem ∘ idem ≈ idem

record IsSplitIdempotent {A : Obj} (i : A ⇒ A) : Set (o ⊔ ℓ ⊔ e) where
  field
    {R}      : Obj
    retract  : A ⇒ R
    section  : R ⇒ A
    retracts : retract ∘ section ≈ id 
    splits   : section ∘ retract ≈ i

  retract-absorb : retract ∘ i ≈ retract
  retract-absorb = begin
    retract ∘ i                 ≈˘⟨ refl⟩∘⟨ splits ⟩
    retract ∘ section ∘ retract ≈⟨ cancelˡ retracts ⟩
    retract                     ∎

  section-absorb : i ∘ section ≈ section
  section-absorb = begin
    i ∘ section                   ≈˘⟨ splits ⟩∘⟨refl ⟩
    (section ∘ retract) ∘ section ≈⟨ cancelʳ retracts ⟩
    section                       ∎

record SplitIdempotent (A : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    idem : A ⇒ A
    isSplitIdempotent : IsSplitIdempotent idem

  open IsSplitIdempotent isSplitIdempotent public
