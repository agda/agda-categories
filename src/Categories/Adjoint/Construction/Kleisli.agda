{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category
open import Categories.Monad

module Categories.Adjoint.Construction.Kleisli {o ℓ e} {C : Category o ℓ e} (M : Monad C) where

open import Categories.Category.Construction.Kleisli
open import Categories.Adjoint
open import Categories.Functor
open import Categories.Morphism
open import Categories.Functor.Properties
open import Categories.NaturalTransformation.Core
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_)
open import Categories.Morphism.Reasoning C
open import Categories.Tactic.Category

private
  module C = Category C
  module M = Monad M
  open M.F
  open C
  open HomReasoning
  open Equiv

Forgetful : Functor (Kleisli M) C
Forgetful = record
  { F₀           = λ X → F₀ X
  ; F₁           = λ f → M.μ.η _ ∘ F₁ f
  ; identity     = M.identityˡ
  ; homomorphism = λ {X Y Z} {f g} → begin
    M.μ.η Z ∘ F₁ ((M.μ.η Z ∘ F₁ g) ∘ f)         ≈⟨ refl⟩∘⟨ homomorphism ⟩
    M.μ.η Z ∘ F₁ (M.μ.η Z ∘ F₁ g) ∘ F₁ f        ≈⟨ refl⟩∘⟨ homomorphism ⟩∘⟨refl ⟩
    M.μ.η Z ∘ (F₁ (M.μ.η Z) ∘ F₁ (F₁ g)) ∘ F₁ f ≈⟨ pull-first M.assoc ⟩
    (M.μ.η Z ∘ M.μ.η (F₀ Z)) ∘ F₁ (F₁ g) ∘ F₁ f ≈⟨ center (M.μ.commute g) ⟩
    M.μ.η Z ∘ (F₁ g ∘ M.μ.η Y) ∘ F₁ f           ≈⟨ pull-first refl ⟩
    (M.μ.η Z ∘ F₁ g) ∘ M.μ.η Y ∘ F₁ f           ∎
  ; F-resp-≈     = λ eq → ∘-resp-≈ʳ (F-resp-≈ eq)
  }

Free : Functor C (Kleisli M)
Free = record
  { F₀           = λ X → X
  ; F₁           = λ f → M.η.η _ ∘ f
  ; identity     = identityʳ
  ; homomorphism = λ {X Y Z} {f g} → begin
    M.η.η Z ∘ g ∘ f                                 ≈⟨ sym-assoc ○ ⟺ identityˡ ⟩
    C.id ∘ (M.η.η Z ∘ g) ∘ f                        ≈˘⟨ pull-first M.identityˡ ⟩
    M.μ.η Z ∘ (F₁ (M.η.η Z) ∘ M.η.η Z ∘ g) ∘ f      ≈⟨ refl⟩∘⟨ pushʳ (M.η.commute g) ⟩∘⟨refl ⟩
    M.μ.η Z ∘ ((F₁ (M.η.η Z) ∘ F₁ g) ∘ M.η.η Y) ∘ f ≈˘⟨ center (∘-resp-≈ˡ homomorphism) ⟩
    (M.μ.η Z ∘ F₁ (M.η.η Z ∘ g)) ∘ M.η.η Y ∘ f      ∎
  ; F-resp-≈     = ∘-resp-≈ʳ
  }

FF≃F : Forgetful ∘F Free ≃ M.F
FF≃F = record
  { F⇒G = ntHelper record
    { η       = λ X → F₁ C.id
    ; commute = λ {X Y} f → begin
      F₁ C.id ∘ M.μ.η Y ∘ F₁ (M.η.η Y ∘ f)      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ homomorphism ⟩
      F₁ C.id ∘ M.μ.η Y ∘ F₁ (M.η.η Y) ∘ F₁ f   ≈⟨ refl⟩∘⟨ cancelˡ M.identityˡ ⟩
      F₁ C.id ∘ F₁ f                            ≈⟨ [ M.F ]-resp-square id-comm-sym ⟩
      F₁ f ∘ F₁ C.id                            ∎
    }
  ; F⇐G = ntHelper record
    { η       = λ X → F₁ C.id
    ; commute = λ {X Y} f → begin
      F₁ C.id ∘ F₁ f                            ≈⟨ [ M.F ]-resp-square id-comm-sym ⟩
      F₁ f ∘ F₁ C.id                            ≈˘⟨ cancelˡ M.identityˡ ⟩∘⟨refl ⟩
      (M.μ.η Y ∘ F₁ (M.η.η Y) ∘ F₁ f) ∘ F₁ C.id ≈˘⟨ ∘-resp-≈ʳ homomorphism ⟩∘⟨refl ⟩
      (M.μ.η Y ∘ F₁ (M.η.η Y ∘ f)) ∘ F₁ C.id    ∎
    }
  ; iso = λ X → record
    { isoˡ = elimˡ identity ○ identity
    ; isoʳ = elimˡ identity ○ identity
    }
  }

Free⊣Forgetful : Free ⊣ Forgetful
Free⊣Forgetful = record
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

module KleisliExtension where

  κ : {A B : Obj} → (f : A ⇒ F₀ B) → F₀ A ⇒ F₀ B
  κ {A} {B} f = M.μ.η B ∘ F₁ f

  f-iso⇒Klf-iso : ∀ {A B : Obj} → (f : A ⇒ F₀ B) → (g : B ⇒ F₀ A) → Iso (Kleisli M) g f → Iso C (κ f) (κ g)
  f-iso⇒Klf-iso {A} {B} f g (record { isoˡ = isoˡ ; isoʳ = isoʳ }) = record
    { isoˡ = begin
       (M.μ.η A ∘ F₁ g) ∘ M.μ.η B ∘ F₁ f           ≈⟨ center (sym (M.μ.commute g)) ⟩
       M.μ.η A ∘ (M.μ.η (F₀ A) ∘ F₁ (F₁ g)) ∘ F₁ f ≈⟨ assoc²'' ○ pushˡ (Monad.sym-assoc M) ⟩
       M.μ.η A ∘ F₁ (M.μ.η A) ∘ F₁ (F₁ g) ∘ F₁ f   ≈⟨ refl⟩∘⟨ sym trihom ⟩
       M.μ.η A ∘ F₁ (M.μ.η A ∘ F₁ g ∘ f)           ≈⟨ refl⟩∘⟨ F-resp-≈ (sym assoc) ⟩
       M.μ.η A ∘ F₁ ((M.μ.η A ∘ F₁ g) ∘ f)         ≈⟨ refl⟩∘⟨ F-resp-≈ isoʳ ○ Monad.identityˡ M ⟩
       C.id                                        ∎
    ; isoʳ = begin
       (M.μ.η B ∘ F₁ f) ∘ M.μ.η A ∘ F₁ g           ≈⟨ center (sym (M.μ.commute f)) ⟩
       M.μ.η B ∘ (M.μ.η (F₀ B) ∘ F₁ (F₁ f)) ∘ F₁ g ≈⟨ assoc²'' ○ pushˡ (Monad.sym-assoc M) ⟩
       M.μ.η B ∘ F₁ (M.μ.η B) ∘ F₁ (F₁ f) ∘ F₁ g   ≈⟨ refl⟩∘⟨ sym trihom ⟩
       M.μ.η B ∘ F₁ (M.μ.η B ∘ F₁ f ∘ g)           ≈⟨ refl⟩∘⟨ F-resp-≈ (sym assoc) ⟩
       M.μ.η B ∘ F₁ ((M.μ.η B ∘ F₁ f) ∘ g)         ≈⟨ refl⟩∘⟨ F-resp-≈ isoˡ ○ Monad.identityˡ M ⟩
       C.id                                        ∎
    }
    where
    trihom : {X Y Z W : Obj} {f : X ⇒ Y} {g : Y ⇒ Z} {h : Z ⇒ W} → F₁ (h ∘ g ∘ f) ≈ F₁ h ∘ F₁ g ∘ F₁ f
    trihom {X} {Y} {Z} {W} {f} {g} {h} = begin
      F₁ (h ∘ g ∘ f)     ≈⟨ homomorphism ⟩
      F₁ h ∘ F₁ (g ∘ f)  ≈⟨ refl⟩∘⟨ homomorphism ⟩
      F₁ h ∘ F₁ g ∘ F₁ f ∎

  Klf-iso⇒f-iso : ∀ {A B : Obj} → (f : A ⇒ F₀ B) → (g : B ⇒ F₀ A) → Iso C (κ f) (κ g) → Iso (Kleisli M) g f
  Klf-iso⇒f-iso {A} {B} f g record { isoˡ = isoˡ ; isoʳ = isoʳ } = record
    { isoˡ = begin
      (M.μ.η B ∘ F₁ f) ∘ g                              ≈⟨ introʳ (Monad.identityʳ M) ⟩∘⟨refl ⟩
      ((M.μ.η B ∘ F₁ f) ∘ (M.μ.η A ∘ M.η.η (F₀ A))) ∘ g ≈⟨ solve C ⟩
      M.μ.η B ∘ F₁ f ∘ (M.μ.η A) ∘ (M.η.η (F₀ A) ∘ g)   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ M.η.commute g ⟩
      M.μ.η B ∘ F₁ f ∘ M.μ.η A ∘ (F₁ g ∘ M.η.η B)       ≈⟨ solve C ⟩
      ((M.μ.η B ∘ F₁ f) ∘ M.μ.η A ∘ F₁ g) ∘ M.η.η B     ≈⟨ elimˡ isoʳ ⟩
      M.η.η B                                           ∎
    ; isoʳ = begin
      (M.μ.η A ∘ F₁ g) ∘ f                              ≈⟨ introʳ (Monad.identityʳ M) ⟩∘⟨refl ⟩
      ((M.μ.η A ∘ F₁ g) ∘ (M.μ.η B ∘ M.η.η (F₀ B))) ∘ f ≈⟨ solve C ⟩
      M.μ.η A ∘ F₁ g ∘ (M.μ.η B) ∘ (M.η.η (F₀ B) ∘ f)   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ M.η.commute f ⟩
      M.μ.η A ∘ F₁ g ∘ M.μ.η B ∘ (F₁ f ∘ M.η.η A)       ≈⟨ solve C ⟩
      ((M.μ.η A ∘ F₁ g) ∘ M.μ.η B ∘ F₁ f) ∘ M.η.η A     ≈⟨ elimˡ isoˡ ⟩
      M.η.η A                                           ∎
    }

  kl-ext-compat : ∀ {A B X : Obj} → (f : A ⇒ F₀ B) → (g : B ⇒ F₀ X) → κ ((κ g) ∘ f) ≈ κ g ∘ κ f
  kl-ext-compat {A} {B} {X} f g = begin
    M.μ.η X ∘ F₁ ((M.μ.η X ∘ F₁ g) ∘ f)         ≈⟨ refl⟩∘⟨ F-resp-≈ assoc ○ refl⟩∘⟨ trihom ⟩
    M.μ.η X ∘ (F₁ (M.μ.η X) ∘ F₁ (F₁ g) ∘ F₁ f) ≈⟨ solve C ⟩
    (M.μ.η X ∘ F₁ (M.μ.η X)) ∘ F₁ (F₁ g) ∘ F₁ f ≈⟨ Monad.assoc M ⟩∘⟨refl ⟩
    (M.μ.η X ∘ M.μ.η (F₀ X)) ∘ F₁ (F₁ g) ∘ F₁ f ≈⟨ center (M.μ.commute g) ⟩
    M.μ.η X ∘ (F₁ g ∘ M.μ.η B) ∘ F₁ f           ≈⟨ solve C ⟩
    (M.μ.η X ∘ F₁ g) ∘ M.μ.η B ∘ F₁ f           ∎
    where
    trihom : {X Y Z W : Obj} {f : X ⇒ Y} {g : Y ⇒ Z} {h : Z ⇒ W} → F₁ (h ∘ g ∘ f) ≈ F₁ h ∘ F₁ g ∘ F₁ f
    trihom {X} {Y} {Z} {W} {f} {g} {h} = begin
      F₁ (h ∘ g ∘ f)     ≈⟨ homomorphism ⟩
      F₁ h ∘ F₁ (g ∘ f)  ≈⟨ refl⟩∘⟨ homomorphism ⟩
      F₁ h ∘ F₁ g ∘ F₁ f ∎
