{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core
open import Categories.Object.Terminal using (Terminal)
open import Categories.Category.Cartesian.Bundle using (CartesianCategory)
open import Categories.Category.BinaryProducts using (BinaryProducts)

-- Parametrized natural numbers object as described here https://ncatlab.org/nlab/show/natural+numbers+object#withparams

module Categories.Object.NaturalNumber.Parametrized {o ℓ e} (CC : CartesianCategory o ℓ e) where

open import Level
open CartesianCategory CC renaming (U to 𝒞)
open BinaryProducts products hiding (η; unique)

open import Categories.Object.NaturalNumber 𝒞 terminal using (IsNaturalNumber; NaturalNumber) renaming (up-to-iso to nno-up-to-iso)
open import Categories.Morphism 𝒞 using (_≅_)
open import Categories.Morphism.Reasoning 𝒞

open HomReasoning
open Equiv
open Terminal terminal using (⊤; !; !-unique₂)


private
  variable
    A B C D X Y Z : Obj
    h i j : A ⇒ B

record IsParametrizedNaturalNumber (N : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    z : ⊤ ⇒ N
    s : N ⇒ N
    universal : ∀ {A X} → A ⇒ X → X ⇒ X → A × N ⇒ X
    commute₁ : ∀ {A X} {f : A ⇒ X} {g : X ⇒ X} → f ≈ universal f g ∘ ⟨ id , z ∘ ! ⟩
    commute₂ : ∀ {A X} {f : A ⇒ X} {g : X ⇒ X} → g ∘ (universal f g) ≈ (universal f g) ∘ (id ⁂ s)
    unique : ∀ {A X} {f : A ⇒ X} {g : X ⇒ X} {u : A × N ⇒ X} → f ≈ u ∘ ⟨ id , z ∘ ! ⟩ → g ∘ u ≈ u ∘ (id ⁂ s) → u ≈ universal f g

  η : universal {A = ⊤} ⟨ id , z ∘ ! ⟩ (id ⁂ s) ≈ id
  η = ⟺ (unique (⟺ identityˡ) id-comm)
  
  universal-cong : ∀ {A} → {f f′ : ⊤ ⇒ A} → {g g′ : A ⇒ A} → f ≈ f′ → g ≈ g′ → universal f g ≈ universal f′ g′
  universal-cong f≈f′ g≈g′ = unique (⟺ f≈f′ ○  commute₁) (∘-resp-≈ˡ (⟺ g≈g′) ○ commute₂)

  isNaturalNumber : IsNaturalNumber N
  isNaturalNumber = record
    { z = z
    ; s = s
    ; universal = λ {A} q f → universal q f ∘ ⟨ ! , id ⟩
    ; z-commute = λ {A} {q} {f} → begin 
      q                                  ≈⟨ commute₁ ⟩ 
      universal q f ∘ ⟨ id , z ∘ ! ⟩     ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ !-unique₂ (⟺ z∘! ○ ⟺ identityˡ) ⟩
      universal q f ∘ ⟨ ! ∘ z , id ∘ z ⟩ ≈˘⟨ pullʳ ⟨⟩∘ ⟩
      (universal q f ∘ ⟨ ! , id ⟩) ∘ z   ∎
    ; s-commute = λ {A} {q} {f} → begin 
      f ∘ universal q f ∘ ⟨ ! , id ⟩          ≈⟨ pullˡ commute₂ ⟩ 
      (universal q f ∘ (id ⁂ s)) ∘ ⟨ ! , id ⟩ ≈⟨ pullʳ ⁂∘⟨⟩ ⟩
      universal q f ∘ ⟨ id ∘ ! , s ∘ id ⟩     ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ !-unique₂ id-comm ⟩
      universal q f ∘ ⟨ ! ∘ s , id ∘ s ⟩      ≈˘⟨ pullʳ ⟨⟩∘ ⟩
      (universal q f ∘ ⟨ ! , id ⟩) ∘ s        ∎
    ; unique = λ {A} {q} {f} {u} eqᶻ eqˢ → begin 
      u                          ≈⟨ introʳ project₂ ○ sym-assoc ⟩ 
      (u ∘ π₂) ∘ ⟨ ! , id ⟩      ≈⟨ unique (eqᶻ ○ (pushʳ (z∘! ○ (⟺ project₂)))) 
                                           (pullˡ eqˢ ○ ⟺ (pullʳ project₂ ○ sym-assoc)) 
                                  ⟩∘⟨refl ⟩
      universal q f ∘ ⟨ ! , id ⟩ ∎
    }
    where
      z∘! : z ≈ z ∘ !
      z∘! = ⟺ identityʳ ○ ∘-resp-≈ʳ !-unique₂

record ParametrizedNaturalNumber : Set (o ⊔ ℓ ⊔ e) where
  field
    N : Obj
    isParametrizedNaturalNumber : IsParametrizedNaturalNumber N

  open IsParametrizedNaturalNumber isParametrizedNaturalNumber public

-- every PNNO is also a NNO (the other direction only holds in CCCs)
PNNO⇒NNO : ParametrizedNaturalNumber → NaturalNumber
PNNO⇒NNO pnno = record { N = ParametrizedNaturalNumber.N pnno ; isNaturalNumber = ParametrizedNaturalNumber.isNaturalNumber pnno }

up-to-iso : ∀ (N N′ : ParametrizedNaturalNumber) → ParametrizedNaturalNumber.N N ≅ ParametrizedNaturalNumber.N N′
up-to-iso N N′ = nno-up-to-iso (PNNO⇒NNO N) (PNNO⇒NNO N′)