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
  ; homomorphism = λ {X Y Z} {f g} → hom-proof {X} {Y} {Z} {f} {g}
  ; F-resp-≈     = λ eq → ∘-resp-≈ˡ (F-resp-≈ eq)
  }
  where
  hom-proof :
   {X Y Z : Obj} {f : F₀ X ⇒ Y} {g : F₀ Y ⇒ Z} →
   (F₁ (g ∘ F₁ f ∘ M.δ.η X)) ∘ M.δ.η X ≈ (F₁ g ∘ M.δ.η Y) ∘ F₁ f ∘ M.δ.η X
  hom-proof {X} {Y} {Z} {f} {g} = begin
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

Cofree : Functor C (CoKleisli M)
Cofree =
 record
  { F₀ = λ X → X
  ; F₁ = λ f → f ∘ M.ε.η _
  ; identity = λ {A} → identityˡ
  ; homomorphism = λ {X Y Z} {f g} → hom-proof {X} {Y} {Z} {f} {g}
  ; F-resp-≈ = λ x → ∘-resp-≈ˡ x
  }
  where
  hom-proof :
   {X Y Z : Obj} {f : X ⇒ Y} {g : Y ⇒ Z} →
   (g ∘ f) ∘ M.ε.η X ≈ (g ∘ M.ε.η Y) ∘ (F₁ (f ∘ M.ε.η X) ∘ M.δ.η X)
  hom-proof {X} {Y} {Z} {f} {g} = begin
   (g ∘ f) ∘ M.ε.η X                                 ≈⟨ assoc ⟩
   g ∘ f ∘ M.ε.η X                                   ≈⟨ refl⟩∘⟨ sym (M.ε.commute f) ⟩
   g ∘ M.ε.η Y ∘ F₁ f                                ≈⟨ sym assoc ⟩
   (g ∘ M.ε.η Y) ∘ F₁ f                              ≈⟨ refl⟩∘⟨ sym identityʳ ⟩
   (g ∘ M.ε.η Y) ∘ (F₁ f ∘ C.id)                     ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym (Comonad.identityˡ M) ⟩
   (g ∘ M.ε.η Y) ∘ (F₁ f ∘ F₁ (M.ε.η X) ∘ M.δ.η X)   ≈⟨ refl⟩∘⟨ sym assoc ⟩
   (g ∘ M.ε.η Y) ∘ ((F₁ f ∘ F₁ (M.ε.η X)) ∘ M.δ.η X) ≈⟨ refl⟩∘⟨ sym homomorphism ⟩∘⟨refl ⟩
   (g ∘ M.ε.η Y) ∘ (F₁ (f ∘ M.ε.η X) ∘ M.δ.η X)      ∎

FF≃F : Forgetful ∘F Cofree ≃ M.F
FF≃F =
 record
  { F⇒G = ntHelper record
    { η = λ X → F₁ C.id
    ; commute = λ {X Y} f → to-commute {X} {Y} f
    }
  ; F⇐G = ntHelper record
    { η = λ X → F₁ C.id
    ; commute = λ {X Y} f → from-commute {X} {Y} f
    }
  ; iso = λ X → record
    { isoˡ = elimʳ identity ○ identity
    ; isoʳ = elimʳ identity ○ identity
    }
  }
  where
  to-commute : {X Y : Obj} → (f : X ⇒ Y) → F₁ C.id ∘ F₁ (f ∘ M.ε.η X) ∘ M.δ.η X ≈ F₁ f ∘ F₁ C.id
  to-commute {X} {Y} f = begin
   F₁ C.id ∘ F₁ (f ∘ M.ε.η X) ∘ M.δ.η X        ≈⟨ refl⟩∘⟨ homomorphism ⟩∘⟨refl ⟩
   F₁ C.id ∘ (F₁ f ∘ F₁ (M.ε.η X)) ∘ M.δ.η X   ≈⟨ refl⟩∘⟨ assoc ⟩
   F₁ C.id ∘ (F₁ f ∘ (F₁ (M.ε.η X) ∘ M.δ.η X)) ≈⟨ sym assoc ⟩
   (F₁ C.id ∘ F₁ f) ∘ (F₁ (M.ε.η X) ∘ M.δ.η X) ≈⟨ identity ⟩∘⟨refl ⟩∘⟨refl ⟩
   (C.id ∘ F₁ f) ∘ (F₁ (M.ε.η X) ∘ M.δ.η X)    ≈⟨ identityˡ ⟩∘⟨refl ⟩
   F₁ f ∘ (F₁ (M.ε.η X) ∘ M.δ.η X)             ≈⟨ refl⟩∘⟨ Comonad.identityˡ M ⟩
   F₁ f ∘ C.id                                 ≈⟨ refl⟩∘⟨ sym identity ⟩
   F₁ f ∘ F₁ C.id                              ∎
  from-commute : {X Y : Obj} → (f : X ⇒ Y) → F₁ C.id ∘ F₁ f ≈ (F₁ (f ∘ M.ε.η X) ∘ M.δ.η X) ∘ F₁ C.id
  from-commute {X} {Y} f = begin
      F₁ C.id ∘ F₁ f                              ≈⟨ [ M.F ]-resp-square id-comm-sym ⟩
      F₁ f ∘ F₁ C.id                              ≈⟨ sym identityʳ ⟩∘⟨refl ⟩
      (F₁ f ∘ C.id) ∘ F₁ C.id                     ≈⟨ (refl⟩∘⟨ sym (Comonad.identityˡ M)) ⟩∘⟨refl ⟩
      (F₁ f ∘ F₁ (M.ε.η X) ∘ M.δ.η X) ∘ F₁ C.id   ≈⟨ sym assoc ⟩∘⟨refl ⟩
      ((F₁ f ∘ F₁ (M.ε.η X)) ∘ M.δ.η X) ∘ F₁ C.id ≈⟨ sym homomorphism ⟩∘⟨refl ⟩∘⟨refl ⟩
      (F₁ (f ∘ M.ε.η X) ∘ M.δ.η X) ∘ F₁ C.id      ∎

Forgetful⊣Cofree : Forgetful ⊣ Cofree
Forgetful⊣Cofree =
 record
  { unit = ntHelper record
    { η = λ X → F₁ C.id
    ; commute = λ {X Y} f → unit-commute {X} {Y} f
    }
  ; counit = ntHelper record
    { η = M.ε.η
    ; commute = λ {X Y} f → counit-commute {X} {Y} f
    }
  ; zig = λ {A} → zig-proof {A}
  ; zag = λ {B} → zag-proof {B}
  }
  where
  unit-commute : ∀ {X Y : Obj} →
   (f : F₀ X ⇒ Y) →
   F₁ C.id ∘ F₁ f ∘ M.δ.η X ≈ ((F₁ f ∘ M.δ.η X) ∘ M.ε.η (F₀ X)) ∘ F₁ (F₁ C.id) ∘ M.δ.η X
  unit-commute {X} {Y} f = begin
   F₁ C.id ∘ F₁ f ∘ M.δ.η X                                   ≈⟨ sym assoc ⟩
   (F₁ C.id ∘ F₁ f) ∘ M.δ.η X                                 ≈⟨ sym homomorphism ⟩∘⟨refl ⟩
   (F₁ (C.id ∘ f)) ∘ M.δ.η X                                  ≈⟨ F-resp-≈ identityˡ ⟩∘⟨refl ⟩  F₁ f ∘  M.δ.η X ≈⟨ sym identityʳ ⟩
   (F₁ f ∘ M.δ.η X) ∘ C.id                                    ≈⟨ sym (refl⟩∘⟨ Comonad.identityʳ M) ⟩
   (F₁ f ∘ M.δ.η X) ∘ (M.ε.η (F₀ X) ∘ M.δ.η X)                ≈⟨ sym assoc ⟩
   ((F₁ f ∘ M.δ.η X) ∘ M.ε.η (F₀ X)) ∘ M.δ.η X                ≈⟨ refl⟩∘⟨ sym identityˡ ⟩
   ((F₁ f ∘ M.δ.η X) ∘ M.ε.η (F₀ X)) ∘ C.id ∘ M.δ.η X         ≈⟨ refl⟩∘⟨ sym identity ⟩∘⟨refl ⟩
   ((F₁ f ∘ M.δ.η X) ∘ M.ε.η (F₀ X)) ∘ F₁ C.id ∘ M.δ.η X      ≈⟨ refl⟩∘⟨ sym (F-resp-≈ identity)  ⟩∘⟨refl ⟩
   ((F₁ f ∘ M.δ.η X) ∘ M.ε.η (F₀ X)) ∘ F₁ (F₁ C.id) ∘ M.δ.η X ∎
  counit-commute : ∀ {X Y : Obj} →
   (f : X ⇒ Y) →
   M.ε.η Y ∘ (F₁ (f ∘ M.ε.η X) ∘ M.δ.η X) ≈ f ∘ M.ε.η X
  counit-commute {X} {Y} f = begin
   M.ε.η Y ∘ (F₁ (f ∘ M.ε.η X) ∘ M.δ.η X)      ≈⟨ refl⟩∘⟨ homomorphism ⟩∘⟨refl ⟩
   M.ε.η Y ∘ ((F₁ f ∘ F₁ (M.ε.η X)) ∘ M.δ.η X) ≈⟨ refl⟩∘⟨ assoc ⟩
   M.ε.η Y ∘ (F₁ f ∘ F₁ (M.ε.η X) ∘ M.δ.η X)   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ Comonad.identityˡ M ⟩
   M.ε.η Y ∘ (F₁ f ∘ C.id)                     ≈⟨ sym assoc ⟩
   (M.ε.η Y ∘ F₁ f) ∘ C.id                     ≈⟨ identityʳ ⟩
   M.ε.η Y ∘ F₁ f                              ≈⟨ M.ε.commute f ⟩
   f ∘ M.ε.η X ∎
  zig-proof : {A : Obj} → M.ε.η (F₀ A) ∘ F₁ (F₁ C.id) ∘ M.δ.η _ ≈ C.id
  zig-proof {A} = begin
   M.ε.η (F₀ A) ∘ F₁ (F₁ C.id) ∘ M.δ.η _ ≈⟨ refl⟩∘⟨ F-resp-≈ identity ⟩∘⟨refl ⟩
   M.ε.η (F₀ A) ∘ F₁ C.id ∘ M.δ.η _      ≈⟨ refl⟩∘⟨ identity ⟩∘⟨refl ⟩
   M.ε.η (F₀ A) ∘ C.id ∘ M.δ.η _         ≈⟨ refl⟩∘⟨ identityˡ ⟩
   M.ε.η (F₀ A) ∘ M.δ.η _                ≈⟨ Comonad.identityʳ M ⟩
   C.id                                  ∎
  zag-proof : {B : Obj} → (M.ε.η B ∘ M.ε.η (F₀ B)) ∘ (F₁ (F₁ C.id) ∘ M.δ.η _) ≈ M.ε.η B
  zag-proof {B} = begin
    (M.ε.η B ∘ M.ε.η (F₀ B)) ∘ (F₁ (F₁ C.id) ∘ M.δ.η _) ≈⟨ assoc ⟩
    M.ε.η B ∘ (M.ε.η (F₀ B) ∘ (F₁ (F₁ C.id) ∘ M.δ.η _)) ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ F-resp-≈ identity ⟩∘⟨refl) ⟩
    M.ε.η B ∘ (M.ε.η (F₀ B) ∘ (F₁ C.id ∘ M.δ.η _))      ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ identity ⟩∘⟨refl) ⟩
    M.ε.η B ∘ (M.ε.η (F₀ B) ∘ (C.id ∘ M.δ.η _))         ≈⟨ refl⟩∘⟨ refl⟩∘⟨ identityˡ ⟩
    M.ε.η B ∘ (M.ε.η (F₀ B) ∘ M.δ.η _)                  ≈⟨ refl⟩∘⟨ Comonad.identityʳ M ⟩
    M.ε.η B ∘ C.id                                      ≈⟨ identityʳ ⟩
    M.ε.η B                                             ∎