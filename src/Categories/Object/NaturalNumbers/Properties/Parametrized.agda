{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category.Core
open import Categories.Object.Terminal using (Terminal)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.BinaryCoproducts using (BinaryCoproducts)
open import Categories.Category.CartesianClosed using (CartesianClosed)

-- In CCCs every NNO is a PNNO

module Categories.Object.NaturalNumbers.Properties.Parametrized {o ℓ e} (𝒞 : Category o ℓ e) (𝒞-CartesianClosed : CartesianClosed 𝒞) (𝒞-Coproducts : BinaryCoproducts 𝒞) where

open Category 𝒞
open CartesianClosed 𝒞-CartesianClosed using (cartesian; λg; eval′; β′; λ-inj; λ-cong; η-exp′; λ-unique′; subst)
open Cartesian cartesian renaming (unique′ to bp-unique′)

open import Categories.Object.NaturalNumbers 𝒞 terminal using (NNO)
open import Categories.Object.NaturalNumbers.Parametrized 𝒞 cartesian using (ParametrizedNNO)
open import Categories.Morphism 𝒞
open import Categories.Morphism.Reasoning 𝒞

open HomReasoning
open Equiv

NNO×CCC⇒PNNO : NNO → ParametrizedNNO
NNO×CCC⇒PNNO nno = record
  { N = N
  ; isParametrizedNNO = record
    { z = z
    ; s = s
    ; universal = λ {A} {X} f g → (eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ×₁ id)) ∘ swap
    ; commute₁ = commute₁'
    ; commute₂ = commute₂'
    ; unique = unique'
    }
  }
  where
  open NNO nno renaming (unique to nno-unique)

  commute₁' : ∀ {A X} {f : A ⇒ X} {g : X ⇒ X} → f ≈ ((eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ×₁ id)) ∘ swap) ∘ ⟨ id , z ∘ ! ⟩
  commute₁' {A} {X} {f} {g} = begin
    f                                                                                    ≈⟨ introʳ project₂ ⟩
    f ∘ π₂ ∘ ⟨ ! , id ⟩                                                                  ≈⟨ pullˡ (⟺ β′) ⟩
    (eval′ ∘ (λg (f ∘ π₂) ×₁ id)) ∘ ⟨ ! , id ⟩                                           ≈⟨ pullʳ ×₁∘⟨⟩ ⟩
    eval′ ∘ ⟨ λg (f ∘ π₂) ∘ ! , id ∘ id ⟩                                                ≈⟨ refl⟩∘⟨ ⟨⟩-congʳ (∘-resp-≈ˡ z-commute) ⟩
    eval′ ∘ ⟨ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ∘ z) ∘ ! , id ∘ id ⟩             ≈⟨ refl⟩∘⟨ (⟨⟩-congʳ assoc ○ ⟺ ×₁∘⟨⟩) ⟩
    eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ×₁ id) ∘ ⟨ z ∘ ! , id ⟩            ≈⟨ sym-assoc ○ pushʳ (⟺ swap∘⟨⟩) ⟩
    ((eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ×₁ id)) ∘ swap) ∘ ⟨ id , z ∘ ! ⟩ ∎

  commute₂' : ∀ {A X} {f : A ⇒ X} {g : X ⇒ X}
    → g ∘ ((eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ×₁ id)) ∘ swap) ≈ ((eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ×₁ id)) ∘ swap) ∘ (id ×₁ s)
  commute₂' {A} {X} {f} {g} = begin
    g ∘ (eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ×₁ id)) ∘ swap                        ≈⟨ pullˡ (pullˡ (⟺ β′)) ⟩
    ((eval′ ∘ (λg (g ∘ eval′) ×₁ id)) ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ×₁ id)) ∘ swap ≈⟨ (pullʳ ×₁∘×₁) ⟩∘⟨refl ⟩
    (eval′ ∘ (λg (g ∘ eval′) ∘  universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ×₁ id ∘ id)) ∘ swap     ≈⟨ (refl⟩∘⟨ (×₁-cong₂ s-commute refl)) ⟩∘⟨refl ⟩
    (eval′ ∘ (universal (λg (f ∘ π₂))  (λg (g ∘ eval′)) ∘ s ×₁ id ∘ id)) ∘ swap                  ≈⟨ (refl⟩∘⟨ (⟺ ×₁∘×₁)) ⟩∘⟨refl ⟩
    (eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ×₁ id) ∘ (s ×₁ id)) ∘ swap                ≈⟨ pullʳ (pullʳ (⟺ swap∘×₁)) ⟩
    eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ×₁ id) ∘ swap ∘ (id ×₁ s)                  ≈⟨ sym-assoc ○ sym-assoc ⟩
    ((eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ×₁ id)) ∘ swap) ∘ (id ×₁ s)              ∎

  unique' : ∀ {A X} {f : A ⇒ X} {g : X ⇒ X} {u : A × N ⇒ X}
    → f ≈ u ∘ ⟨ id , z ∘ ! ⟩ → g ∘ u ≈ u ∘ (id ×₁ s) → u ≈ (eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ×₁ id)) ∘ swap
  unique' {A} {X} {f} {g} {u} eqᶻ eqˢ = swap-epi _ _ (λ-inj (begin
    λg (u ∘ swap)                                                                   ≈⟨ nno-unique (⟺ z-commutes) s-commutes ⟩
    universal (λg (f ∘ π₂)) (λg (g ∘ eval′))                                        ≈˘⟨ η-exp′ ⟩
    λg (eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ×₁ id))                   ≈˘⟨ λ-cong (cancelʳ swap∘swap) ⟩
    λg (((eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ×₁ id)) ∘ swap) ∘ swap) ∎))
    where
    z-commutes : λg (u ∘ swap) ∘ z ≈ λg (f ∘ π₂)
    z-commutes = λ-unique′ (begin
      eval′ ∘ (λg (u ∘ swap) ∘ z ×₁ id)         ≈˘⟨ refl⟩∘⟨ (×₁∘×₁ ○ ×₁-cong₂ refl identity²) ⟩
      eval′ ∘ (λg (u ∘ swap) ×₁ id) ∘ (z ×₁ id) ≈⟨ extendʳ β′ ⟩
      u ∘ swap ∘ (z ×₁ id)                      ≈⟨ refl⟩∘⟨ swap∘×₁ ⟩
      u ∘ (id ×₁ z) ∘ swap                      ≈⟨ refl⟩∘⟨ (bp-unique′ π₁-commutes π₂-commutes) ⟩
      u ∘ ⟨ id , z ∘ ! ⟩ ∘ π₂                   ≈⟨ pullˡ (⟺ eqᶻ) ⟩
      f ∘ π₂                                    ∎)
      where
      π₁-commutes : π₁ ∘ (id ×₁ z) ∘ swap ≈ π₁ ∘ ⟨ id , z ∘ ! ⟩ ∘ π₂
      π₁-commutes = begin
        π₁ ∘ (id ×₁ z) ∘ swap    ≈⟨ extendʳ project₁ ○ identityˡ ⟩
        π₁ ∘ swap                ≈⟨ project₁ ⟩
        π₂                       ≈˘⟨ cancelˡ project₁ ⟩
        π₁ ∘ ⟨ id , z ∘ ! ⟩ ∘ π₂ ∎
      π₂-commutes : π₂ ∘ (id ×₁ z) ∘ swap ≈ π₂ ∘ ⟨ id , z ∘ ! ⟩ ∘ π₂
      π₂-commutes = begin
        π₂ ∘ (id ×₁ z) ∘ swap    ≈⟨ extendʳ project₂ ⟩
        z ∘ π₂ ∘ swap            ≈⟨ refl⟩∘⟨ project₂ ⟩
        z ∘ π₁                   ≈⟨ refl⟩∘⟨ !-unique₂ ⟩
        z ∘ ! ∘ π₂               ≈˘⟨ extendʳ project₂ ⟩
        π₂ ∘ ⟨ id , z ∘ ! ⟩ ∘ π₂ ∎
    s-commutes : λg (g ∘ eval′) ∘ λg (u ∘ swap) ≈ λg (u ∘ swap) ∘ s
    s-commutes = begin
      λg (g ∘ eval′) ∘ λg (u ∘ swap)           ≈⟨ subst ⟩
      λg ((g ∘ eval′) ∘ (λg (u ∘ swap) ×₁ id)) ≈⟨ λ-cong (pullʳ β′ ○ pullˡ eqˢ) ⟩
      λg ((u ∘ (id ×₁ s)) ∘ swap)              ≈⟨ λ-cong (pullʳ (⟺ swap∘×₁) ○ sym-assoc) ⟩
      λg ((u ∘ swap) ∘ (s ×₁ id))              ≈˘⟨ subst ⟩
      λg (u ∘ swap) ∘ s                        ∎
