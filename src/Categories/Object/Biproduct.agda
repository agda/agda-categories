{-# OPTIONS --without-K --safe #-}

open import Categories.Category

-- Biproducts, a-la Karvonen.
--
-- This definition has advantages over more traditional ones,
-- namely that that we don't require either enrichment in CMon/Ab, or Zero Objects.
--
-- See https://arxiv.org/abs/1801.06488
module Categories.Object.Biproduct {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level

open Category 𝒞

private
  variable
    A B C D : Obj
    f g h : A ⇒ B

record Biproduct (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    A⊕B : Obj

    -- Product Structure
    π₁    : A⊕B ⇒ A
    π₂    : A⊕B ⇒ B
    ⟨_,_⟩ : C ⇒ A → C ⇒ B → C ⇒ A⊕B

    project₁  : π₁ ∘ ⟨ f , g ⟩ ≈ f
    project₂  : π₂ ∘ ⟨ f , g ⟩ ≈ g
    ⟨⟩-unique : π₁ ∘ h ≈ f → π₂ ∘ h ≈ g → ⟨ f , g ⟩ ≈ h

    -- Coproduct Structure
    i₁    : A ⇒ A⊕B
    i₂    : B ⇒ A⊕B
    [_,_] : A ⇒ C → B ⇒ C → A⊕B ⇒ C

    inject₁   : [ f , g ] ∘ i₁ ≈ f
    inject₂   : [ f , g ] ∘ i₂ ≈ g
    []-unique : h ∘ i₁ ≈ f → h ∘ i₂ ≈ g → [ f , g ] ≈ h

    -- Coherence
    π₁∘i₁≈id : π₁ ∘ i₁ ≈ id
    π₂∘i₂≈id : π₂ ∘ i₂ ≈ id
    permute  : i₁ ∘ π₁ ∘ i₂ ∘ π₂ ≈ i₂ ∘ π₂ ∘ i₁ ∘ π₁
