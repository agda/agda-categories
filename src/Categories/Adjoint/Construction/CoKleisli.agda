{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Comonad

-- Verbatim dual of Categories.Adjoint.Construction.Kleisli
module Categories.Adjoint.Construction.CoKleisli {o ℓ e} {C : Category o ℓ e} (M : Comonad C) where

open import Categories.Category.Construction.CoKleisli
open import Categories.Adjoint
open import Categories.Functor
open import Categories.Functor.Properties
open import Categories.NaturalTransformation.Core
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_)
open import Categories.Morphism.Reasoning C

private
  module C = Category C
  module M = Comonad M
  open M.F
  open C
  open HomReasoning
  open Equiv

Forgetful : Functor (CoKleisli M) C
Forgetful =
 record
  { F₀           = λ X → F₀ X
  ; F₁           = λ f → F₁ f ∘ M.δ.η _
  ; identity     = Comonad.identityˡ M
  ; homomorphism = λ {X Y Z} {f g} → begin
    (F₁ (g ∘ F₁ f ∘ M.δ.η X)) ∘ M.δ.η X           ≈⟨ homomorphism ⟩∘⟨refl ⟩
    (F₁ g ∘ F₁ (F₁ f ∘ M.δ.η X)) ∘ M.δ.η X        ≈⟨ (refl⟩∘⟨ homomorphism) ⟩∘⟨refl ⟩
    (F₁ g ∘ F₁ (F₁ f) ∘ F₁ (M.δ.η X)) ∘ M.δ.η X   ≈⟨ assoc ⟩
    F₁ g ∘ ((F₁ (F₁ f) ∘ F₁ (M.δ.η X)) ∘ M.δ.η X) ≈⟨ refl⟩∘⟨ assoc ⟩
    F₁ g ∘ (F₁ (F₁ f) ∘ F₁ (M.δ.η X) ∘ M.δ.η X)   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym M.assoc ⟩
    F₁ g ∘ (F₁ (F₁ f) ∘ M.δ.η (F₀ X) ∘ M.δ.η X)   ≈⟨ refl⟩∘⟨ sym assoc ⟩
    F₁ g ∘ ((F₁ (F₁ f) ∘ M.δ.η (F₀ X)) ∘ M.δ.η X) ≈⟨ refl⟩∘⟨ sym (M.δ.commute f) ⟩∘⟨refl ⟩
    F₁ g ∘ ((M.δ.η Y ∘ F₁ f) ∘ M.δ.η X)           ≈⟨ refl⟩∘⟨ assoc ⟩
    F₁ g ∘ (M.δ.η Y ∘ F₁ f ∘ M.δ.η X)             ≈⟨ sym assoc ⟩
    (F₁ g ∘ M.δ.η Y) ∘ F₁ f ∘ M.δ.η X             ∎
  ; F-resp-≈     = λ eq → ∘-resp-≈ˡ (F-resp-≈ eq)
  }

Cofree : Functor C (CoKleisli M)
Cofree =
 record
  { F₀ = λ X → X
  ; F₁ = λ f → f ∘ M.ε.η _
  ; identity = λ {A} → identityˡ
  ; homomorphism = λ {X Y Z} {f g} → begin
    (g ∘ f) ∘ M.ε.η X                                 ≈⟨ assoc ⟩
    g ∘ f ∘ M.ε.η X                                   ≈⟨ refl⟩∘⟨ sym (M.ε.commute f) ⟩
    g ∘ M.ε.η Y ∘ F₁ f                                ≈⟨ sym assoc ⟩
    (g ∘ M.ε.η Y) ∘ F₁ f                              ≈⟨ refl⟩∘⟨ sym identityʳ ⟩
    (g ∘ M.ε.η Y) ∘ (F₁ f ∘ C.id)                     ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym (Comonad.identityˡ M) ⟩
    (g ∘ M.ε.η Y) ∘ (F₁ f ∘ F₁ (M.ε.η X) ∘ M.δ.η X)   ≈⟨ refl⟩∘⟨ sym assoc ⟩
    (g ∘ M.ε.η Y) ∘ ((F₁ f ∘ F₁ (M.ε.η X)) ∘ M.δ.η X) ≈⟨ refl⟩∘⟨ sym homomorphism ⟩∘⟨refl ⟩
    (g ∘ M.ε.η Y) ∘ (F₁ (f ∘ M.ε.η X) ∘ M.δ.η X)      ∎
  ; F-resp-≈ = λ x → ∘-resp-≈ˡ x
  }

FF≃F : Forgetful ∘F Cofree ≃ M.F
FF≃F =
 record
  { F⇒G = ntHelper record
    { η = λ X → F₁ C.id
    ; commute = λ {X Y} f → begin
     F₁ C.id ∘ F₁ (f ∘ M.ε.η X) ∘ M.δ.η X        ≈⟨ refl⟩∘⟨ homomorphism ⟩∘⟨refl ⟩
     F₁ C.id ∘ (F₁ f ∘ F₁ (M.ε.η X)) ∘ M.δ.η X   ≈⟨ refl⟩∘⟨ assoc ⟩
     F₁ C.id ∘ (F₁ f ∘ (F₁ (M.ε.η X) ∘ M.δ.η X)) ≈⟨ sym assoc ⟩
     (F₁ C.id ∘ F₁ f) ∘ (F₁ (M.ε.η X) ∘ M.δ.η X) ≈⟨ identity ⟩∘⟨refl ⟩∘⟨refl ⟩
     (C.id ∘ F₁ f) ∘ (F₁ (M.ε.η X) ∘ M.δ.η X)    ≈⟨ identityˡ ⟩∘⟨refl ⟩
     F₁ f ∘ (F₁ (M.ε.η X) ∘ M.δ.η X)             ≈⟨ refl⟩∘⟨ Comonad.identityˡ M ⟩
     F₁ f ∘ C.id                                 ≈⟨ refl⟩∘⟨ sym identity ⟩
     F₁ f ∘ F₁ C.id                              ∎
    }
  ; F⇐G = ntHelper record
    { η = λ X → F₁ C.id
    ; commute = λ {X Y} f → begin
      F₁ C.id ∘ F₁ f                              ≈⟨ [ M.F ]-resp-square id-comm-sym ⟩
      F₁ f ∘ F₁ C.id                              ≈⟨ sym identityʳ ⟩∘⟨refl ⟩
      (F₁ f ∘ C.id) ∘ F₁ C.id                     ≈⟨ (refl⟩∘⟨ sym (Comonad.identityˡ M)) ⟩∘⟨refl ⟩
      (F₁ f ∘ F₁ (M.ε.η X) ∘ M.δ.η X) ∘ F₁ C.id   ≈⟨ sym assoc ⟩∘⟨refl ⟩
      ((F₁ f ∘ F₁ (M.ε.η X)) ∘ M.δ.η X) ∘ F₁ C.id ≈⟨ sym homomorphism ⟩∘⟨refl ⟩∘⟨refl ⟩
      (F₁ (f ∘ M.ε.η X) ∘ M.δ.η X) ∘ F₁ C.id      ∎
    }
  ; iso = λ X → record
    { isoˡ = elimʳ identity ○ identity
    ; isoʳ = elimʳ identity ○ identity
    }
  }

Forgetful⊣Cofree : Forgetful ⊣ Cofree
Forgetful⊣Cofree =
 record
  { unit = ntHelper record { η = λ X → F₁ C.id ; commute = {!   !} }
  ; counit = ntHelper record { η = M.ε.η ; commute = {!   !} }
  ; zig = λ {A} → {!   !}
  ; zag = λ {B} → {!   !}
  }

{-
record
  { unit   = ntHelper record
    { η       = M.η.η
    ; commute = λ {X Y} f → begin
      M.η.η Y ∘ f                               ≈⟨ M.η.commute f ⟩
      F₁ f ∘ M.η.η X                            ≈˘⟨ cancelˡ M.identityˡ ⟩∘⟨refl ⟩
      (M.μ.η Y ∘ F₁ (M.η.η Y) ∘ F₁ f) ∘ M.η.η X ≈˘⟨ ∘-resp-≈ʳ homomorphism ⟩∘⟨refl ⟩
      (M.μ.η Y ∘ F₁ (M.η.η Y ∘ f)) ∘ M.η.η X    ∎
    }
  ; counit = ntHelper record
    { η       = λ X → F₁ C.id
    ; commute = λ {X Y} f → begin
      (M.μ.η Y ∘ F₁ (F₁ C.id)) ∘ M.η.η (F₀ Y) ∘ M.μ.η Y ∘ F₁ f
        ≈⟨ elimʳ (F-resp-≈ identity ○ identity) ⟩∘⟨refl ⟩
      M.μ.η Y ∘ M.η.η (F₀ Y) ∘ M.μ.η Y ∘ F₁ f
        ≈⟨ cancelˡ M.identityʳ ⟩
      M.μ.η Y ∘ F₁ f
        ≈⟨ introʳ identity ⟩
      (M.μ.η Y ∘ F₁ f) ∘ F₁ C.id
        ∎
    }
  ; zig    = λ {A} → begin
    (M.μ.η A ∘ F₁ (F₁ C.id)) ∘ M.η.η (F₀ A) ∘ M.η.η A ≈⟨ elimʳ (F-resp-≈ identity ○ identity) ⟩∘⟨refl ⟩
    M.μ.η A ∘ M.η.η (F₀ A) ∘ M.η.η A                  ≈⟨ cancelˡ M.identityʳ ⟩
    M.η.η A                                           ∎
  ; zag    = λ {B} → begin
    (M.μ.η B ∘ F₁ (F₁ C.id)) ∘ M.η.η (F₀ B)           ≈⟨ elimʳ (F-resp-≈ identity ○ identity) ⟩∘⟨refl ⟩
    M.μ.η B ∘ M.η.η (F₀ B)                            ≈⟨ M.identityʳ ⟩
    C.id                                              ∎
  }
-}