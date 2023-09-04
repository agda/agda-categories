{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core
open import Categories.Object.Terminal using (Terminal)
open import Categories.Category.CartesianClosed.Bundle using (CartesianClosedCategory)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.Cocartesian using (BinaryCoproducts)
open import Categories.Category.CartesianClosed using (CartesianClosed)

-- In CCCs NNOs and PNNOs coincide

module Categories.Object.NaturalNumbers.Properties.Parametrized {o ℓ e} (CCC : CartesianClosedCategory o ℓ e) (𝒞-Coproducts : BinaryCoproducts (CartesianClosedCategory.U CCC)) where

open import Level

open CartesianClosedCategory CCC renaming (U to 𝒞)
open CartesianClosed cartesianClosed using (cartesian; λg; eval′; β′; λ-inj; λ-cong; η-exp′; λ-unique′; subst)
open Cartesian cartesian using (terminal; products)
open BinaryProducts products renaming (unique′ to bp-unique′)

open import Categories.Object.NaturalNumbers 𝒞 terminal using (NNO)
open import Categories.Object.NaturalNumbers.Parametrized cartesianCategory using (ParametrizedNNO)
open import Categories.Morphism 𝒞
open import Categories.Morphism.Reasoning 𝒞

open HomReasoning
open Equiv

open Terminal terminal

NNO×CCC⇒PNNO : NNO → ParametrizedNNO
NNO×CCC⇒PNNO nno = record 
  { N = N 
  ; isParametrizedNNO = record
    { z = z
    ; s = s
    ; universal = λ {A} {X} f g → (eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ⁂ id)) ∘ swap
    ; commute₁ = λ {A} {X} {f} {g} → begin 
      f                                                                                   ≈⟨ introʳ project₂ ⟩
      f ∘ π₂ ∘ ⟨ ! , id ⟩                                                                 ≈⟨ pullˡ (⟺ β′) ⟩
      (eval′ ∘ (λg (f ∘ π₂) ⁂ id)) ∘ ⟨ ! , id ⟩                                           ≈⟨ pullʳ ⁂∘⟨⟩ ⟩
      eval′ ∘ ⟨ λg (f ∘ π₂) ∘ ! , id ∘ id ⟩                                               ≈⟨ refl⟩∘⟨ ⟨⟩-congʳ (∘-resp-≈ˡ z-commute) ⟩
      eval′ ∘ ⟨ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ∘ z) ∘ ! , id ∘ id ⟩            ≈⟨ refl⟩∘⟨ (⟨⟩-congʳ assoc ○ ⟺ ⁂∘⟨⟩) ⟩
      eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ⁂ id) ∘ ⟨ z ∘ ! , id ⟩            ≈⟨ sym-assoc ○ pushʳ (⟺ swap∘⟨⟩) ⟩
      ((eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ⁂ id)) ∘ swap) ∘ ⟨ id , z ∘ ! ⟩ ∎
    ; commute₂ = λ {A} {X} {f} {g} → begin
      g ∘ (eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ⁂ id)) ∘ swap                       ≈⟨ pullˡ (pullˡ (⟺ β′)) ⟩
      ((eval′ ∘ (λg (g ∘ eval′) ⁂ id)) ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ⁂ id)) ∘ swap ≈⟨ (pullʳ ⁂∘⁂) ⟩∘⟨refl ⟩
      (eval′ ∘ (λg (g ∘ eval′) ∘  universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ⁂ id ∘ id)) ∘ swap    ≈⟨ (refl⟩∘⟨ (⁂-cong₂ s-commute refl)) ⟩∘⟨refl ⟩
      (eval′ ∘ (universal (λg (f ∘ π₂))  (λg (g ∘ eval′)) ∘ s ⁂ id ∘ id)) ∘ swap                 ≈⟨ (refl⟩∘⟨ (⟺ ⁂∘⁂)) ⟩∘⟨refl ⟩
      (eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ⁂ id) ∘ (s ⁂ id)) ∘ swap                ≈⟨ pullʳ (pullʳ (⟺ swap∘⁂)) ⟩
      eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ⁂ id) ∘ swap ∘ (id ⁂ s)                  ≈⟨ sym-assoc ○ sym-assoc ⟩
      ((eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ⁂ id)) ∘ swap) ∘ (id ⁂ s)              ∎
    ; unique = λ {A} {X} {f} {g} {u} eqᶻ eqˢ → ∘swap-inj (λ-inj 
      (begin 
        λg (u ∘ swap)                                                                  ≈⟨ nno-unique 
          (⟺ (λ-unique′ 
            (begin 
              eval′ ∘ (λg (u ∘ swap) ∘ z ⁂ id)        ≈⟨ refl⟩∘⟨ ⟺ (⁂∘⁂ ○ ⁂-cong₂ refl identity²) ⟩ 
              eval′ ∘ (λg (u ∘ swap) ⁂ id) ∘ (z ⁂ id) ≈⟨ pullˡ β′ ⟩
              (u ∘ swap) ∘ (z ⁂ id)                   ≈⟨ pullʳ swap∘⁂ ⟩
              u ∘ (id ⁂ z) ∘ swap                     ≈⟨ pushʳ (bp-unique′ 
                                                          ( pullˡ project₁ 
                                                          ○ pullʳ project₁ 
                                                          ○ ⟺ (pullˡ project₁)) 
                                                          ( pullˡ project₂ 
                                                          ○ pullʳ project₂ 
                                                          ○ ⟺ (pullʳ !-unique₂) 
                                                          ○ ⟺ (pullˡ project₂))) ⟩
              (u ∘ ⟨ id , z ∘ ! ⟩) ∘ π₂               ≈⟨ ⟺ (∘-resp-≈ˡ eqᶻ) ⟩
              f ∘ π₂                                  ∎))) 
          (begin 
            λg (g ∘ eval′) ∘ λg (u ∘ swap)          ≈⟨ subst ⟩ 
            λg ((g ∘ eval′) ∘ (λg (u ∘ swap) ⁂ id)) ≈⟨ λ-cong (pullʳ β′ ○ pullˡ eqˢ) ⟩
            λg ((u ∘ (id ⁂ s)) ∘ swap)              ≈⟨ λ-cong (pullʳ (⟺ swap∘⁂) ○ sym-assoc) ⟩
            λg ((u ∘ swap) ∘ (s ⁂ id))              ≈˘⟨ subst ⟩
            λg (u ∘ swap) ∘ s ∎) ⟩ 
        universal (λg (f ∘ π₂)) (λg (g ∘ eval′))                                       ≈˘⟨ η-exp′ ⟩
        λg (eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ⁂ id))                   ≈˘⟨ λ-cong (cancelʳ swap∘swap) ⟩
        λg (((eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ⁂ id)) ∘ swap) ∘ swap) ∎))
    } 
  }
  where
    open NNO nno renaming (unique to nno-unique)
