{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Monad using (Monad)

module Categories.Adjoint.Construction.Kleisli {o ℓ e} {C : Category o ℓ e} (M : Monad C) where

open import Categories.Category.Construction.Kleisli using (Kleisli)
open import Categories.Adjoint using (_⊣_)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Morphism using (Iso)
open import Categories.Functor.Properties using ([_]-resp-square)
open import Categories.NaturalTransformation.Core using (ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_)
open import Categories.Morphism.Reasoning C

private
  module C = Category C
  module M = Monad M
  open M.F
  open M using (module μ; module η)
  open C using (Obj; _⇒_; _∘_; _≈_; ∘-resp-≈ʳ; ∘-resp-≈ˡ; assoc; sym-assoc; identityˡ)
  open C.HomReasoning
  open C.Equiv

Forgetful : Functor (Kleisli M) C
Forgetful = record
  { F₀           = λ X → F₀ X
  ; F₁           = λ f → μ.η _ ∘ F₁ f
  ; identity     = M.identityˡ
  ; homomorphism = λ {X Y Z} {f g} → begin
    μ.η Z ∘ F₁ ((μ.η Z ∘ F₁ g) ∘ f)         ≈⟨ refl⟩∘⟨ homomorphism ⟩
    μ.η Z ∘ F₁ (μ.η Z ∘ F₁ g) ∘ F₁ f        ≈⟨ refl⟩∘⟨ homomorphism ⟩∘⟨refl ⟩
    μ.η Z ∘ (F₁ (μ.η Z) ∘ F₁ (F₁ g)) ∘ F₁ f ≈⟨ pull-first M.assoc ⟩
    (μ.η Z ∘ μ.η (F₀ Z)) ∘ F₁ (F₁ g) ∘ F₁ f ≈⟨ center (μ.commute g) ⟩
    μ.η Z ∘ (F₁ g ∘ μ.η Y) ∘ F₁ f           ≈⟨ pull-first refl ⟩
    (μ.η Z ∘ F₁ g) ∘ μ.η Y ∘ F₁ f           ∎
  ; F-resp-≈     = λ eq → ∘-resp-≈ʳ (F-resp-≈ eq)
  }

Free : Functor C (Kleisli M)
Free = record
  { F₀           = λ X → X
  ; F₁           = λ f → η.η _ ∘ f
  ; identity     = C.identityʳ
  ; homomorphism = λ {X Y Z} {f g} → begin
    η.η Z ∘ g ∘ f                             ≈⟨ sym-assoc ○ ⟺ identityˡ ⟩
    C.id ∘ (η.η Z ∘ g) ∘ f                    ≈˘⟨ pull-first M.identityˡ ⟩
    μ.η Z ∘ (F₁ (η.η Z) ∘ η.η Z ∘ g) ∘ f      ≈⟨ refl⟩∘⟨ pushʳ (η.commute g) ⟩∘⟨refl ⟩
    μ.η Z ∘ ((F₁ (η.η Z) ∘ F₁ g) ∘ η.η Y) ∘ f ≈˘⟨ center (∘-resp-≈ˡ homomorphism) ⟩
    (μ.η Z ∘ F₁ (η.η Z ∘ g)) ∘ η.η Y ∘ f      ∎
  ; F-resp-≈     = ∘-resp-≈ʳ
  }

FF≃F : Forgetful ∘F Free ≃ M.F
FF≃F = record
  { F⇒G = ntHelper record
    { η       = λ X → F₁ C.id
    ; commute = λ {X Y} f → begin
      F₁ C.id ∘ μ.η Y ∘ F₁ (η.η Y ∘ f)      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ homomorphism ⟩
      F₁ C.id ∘ μ.η Y ∘ F₁ (η.η Y) ∘ F₁ f   ≈⟨ refl⟩∘⟨ cancelˡ M.identityˡ ⟩
      F₁ C.id ∘ F₁ f                        ≈⟨ [ M.F ]-resp-square id-comm-sym ⟩
      F₁ f ∘ F₁ C.id                        ∎
    }
  ; F⇐G = ntHelper record
    { η       = λ X → F₁ C.id
    ; commute = λ {X Y} f → begin
      F₁ C.id ∘ F₁ f                         ≈⟨ [ M.F ]-resp-square id-comm-sym ⟩
      F₁ f ∘ F₁ C.id                         ≈˘⟨ cancelˡ M.identityˡ ⟩∘⟨refl ⟩
      (μ.η Y ∘ F₁ (η.η Y) ∘ F₁ f) ∘ F₁ C.id  ≈˘⟨ ∘-resp-≈ʳ homomorphism ⟩∘⟨refl ⟩
      (μ.η Y ∘ F₁ (η.η Y ∘ f)) ∘ F₁ C.id     ∎
    }
  ; iso = λ X → record
    { isoˡ = elimˡ identity ○ identity
    ; isoʳ = elimˡ identity ○ identity
    }
  }

Free⊣Forgetful : Free ⊣ Forgetful
Free⊣Forgetful = record
  { unit   = ntHelper record
    { η       = η.η
    ; commute = λ {X Y} f → begin
      η.η Y ∘ f                            ≈⟨ η.commute f ⟩
      F₁ f ∘ η.η X                         ≈˘⟨ cancelˡ M.identityˡ ⟩∘⟨refl ⟩
      (μ.η Y ∘ F₁ (η.η Y) ∘ F₁ f) ∘ η.η X  ≈˘⟨ ∘-resp-≈ʳ homomorphism ⟩∘⟨refl ⟩
      (μ.η Y ∘ F₁ (η.η Y ∘ f)) ∘ η.η X     ∎
    }
  ; counit = ntHelper record
    { η       = λ X → F₁ C.id
    ; commute = λ {X Y} f → begin
      (μ.η Y ∘ F₁ (F₁ C.id)) ∘ η.η (F₀ Y) ∘ μ.η Y ∘ F₁ f  ≈⟨ elimʳ (F-resp-≈ identity ○ identity) ⟩∘⟨refl ⟩
      μ.η Y ∘ η.η (F₀ Y) ∘ μ.η Y ∘ F₁ f                   ≈⟨ cancelˡ M.identityʳ ⟩
      μ.η Y ∘ F₁ f                                        ≈⟨ introʳ identity ⟩
      (μ.η Y ∘ F₁ f) ∘ F₁ C.id                            ∎
    }
  ; zig    = λ {A} → begin
    (μ.η A ∘ F₁ (F₁ C.id)) ∘ η.η (F₀ A) ∘ η.η A  ≈⟨ elimʳ (F-resp-≈ identity ○ identity) ⟩∘⟨refl ⟩
    μ.η A ∘ η.η (F₀ A) ∘ η.η A                   ≈⟨ cancelˡ M.identityʳ ⟩
    η.η A                                        ∎
  ; zag    = λ {B} → begin
    (μ.η B ∘ F₁ (F₁ C.id)) ∘ η.η (F₀ B)  ≈⟨ elimʳ (F-resp-≈ identity ○ identity) ⟩∘⟨refl ⟩
    μ.η B ∘ η.η (F₀ B)                   ≈⟨ M.identityʳ ⟩
    C.id                                 ∎
  }

module KleisliExtension where

  κ : {A B : Obj} → (f : A ⇒ F₀ B) → F₀ A ⇒ F₀ B
  κ {_} {B} f = μ.η B ∘ F₁ f

  f-iso⇒Klf-iso : ∀ {A B : Obj} → (f : A ⇒ F₀ B) → (g : B ⇒ F₀ A) → Iso (Kleisli M) g f → Iso C (κ f) (κ g)
  f-iso⇒Klf-iso {A} {B} f g (record { isoˡ = isoˡ ; isoʳ = isoʳ }) = record
    { isoˡ = begin
       (μ.η A ∘ F₁ g) ∘ μ.η B ∘ F₁ f           ≈⟨ center (sym (μ.commute g)) ⟩
       μ.η A ∘ (μ.η (F₀ A) ∘ F₁ (F₁ g)) ∘ F₁ f ≈⟨ assoc²δγ ○ pushˡ M.sym-assoc ⟩
       μ.η A ∘ F₁ (μ.η A) ∘ F₁ (F₁ g) ∘ F₁ f   ≈⟨ refl⟩∘⟨ sym trihom ⟩
       μ.η A ∘ F₁ (μ.η A ∘ F₁ g ∘ f)           ≈⟨ refl⟩∘⟨ F-resp-≈ sym-assoc ⟩
       μ.η A ∘ F₁ ((μ.η A ∘ F₁ g) ∘ f)         ≈⟨ refl⟩∘⟨ F-resp-≈ isoʳ ○ M.identityˡ ⟩
       C.id                                        ∎
    ; isoʳ = begin
       (μ.η B ∘ F₁ f) ∘ μ.η A ∘ F₁ g           ≈⟨ center (sym (μ.commute f)) ⟩
       μ.η B ∘ (μ.η (F₀ B) ∘ F₁ (F₁ f)) ∘ F₁ g ≈⟨ assoc²δγ ○ pushˡ M.sym-assoc ⟩
       μ.η B ∘ F₁ (μ.η B) ∘ F₁ (F₁ f) ∘ F₁ g   ≈⟨ refl⟩∘⟨ sym trihom ⟩
       μ.η B ∘ F₁ (μ.η B ∘ F₁ f ∘ g)           ≈⟨ refl⟩∘⟨ F-resp-≈ sym-assoc ⟩
       μ.η B ∘ F₁ ((μ.η B ∘ F₁ f) ∘ g)         ≈⟨ refl⟩∘⟨ F-resp-≈ isoˡ ○ M.identityˡ ⟩
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
      (μ.η B ∘ F₁ f) ∘ g                          ≈⟨ introʳ M.identityʳ ⟩∘⟨refl ⟩
      ((μ.η B ∘ F₁ f) ∘ (μ.η A ∘ η.η (F₀ A))) ∘ g ≈⟨ assoc ⟩∘⟨refl ○ assoc ○ refl⟩∘⟨ assoc ○ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
      μ.η B ∘ F₁ f ∘ (μ.η A) ∘ (η.η (F₀ A) ∘ g)   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ η.commute g ⟩
      μ.η B ∘ F₁ f ∘ μ.η A ∘ (F₁ g ∘ η.η B)       ≈˘⟨ assoc ⟩∘⟨refl ○ assoc ○ refl⟩∘⟨ assoc ○ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
      ((μ.η B ∘ F₁ f) ∘ μ.η A ∘ F₁ g) ∘ η.η B     ≈⟨ elimˡ isoʳ ⟩
      η.η B                                           ∎
    ; isoʳ = begin
      (μ.η A ∘ F₁ g) ∘ f                          ≈⟨ introʳ M.identityʳ ⟩∘⟨refl ⟩
      ((μ.η A ∘ F₁ g) ∘ (μ.η B ∘ η.η (F₀ B))) ∘ f ≈⟨ assoc ⟩∘⟨refl ○ assoc ○ refl⟩∘⟨ assoc ○ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
      μ.η A ∘ F₁ g ∘ (μ.η B) ∘ (η.η (F₀ B) ∘ f)   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ η.commute f ⟩
      μ.η A ∘ F₁ g ∘ μ.η B ∘ (F₁ f ∘ η.η A)       ≈˘⟨ assoc ⟩∘⟨refl ○ assoc ○ refl⟩∘⟨ assoc ○ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
      ((μ.η A ∘ F₁ g) ∘ μ.η B ∘ F₁ f) ∘ η.η A     ≈⟨ elimˡ isoˡ ⟩
      η.η A                                       ∎
    }

  kl-ext-compat : ∀ {A B X : Obj} → (f : A ⇒ F₀ B) → (g : B ⇒ F₀ X) → κ ((κ g) ∘ f) ≈ κ g ∘ κ f
  kl-ext-compat {A} {B} {X} f g = begin
    μ.η X ∘ F₁ ((μ.η X ∘ F₁ g) ∘ f)         ≈⟨ refl⟩∘⟨ F-resp-≈ assoc ○ refl⟩∘⟨ trihom ⟩
    μ.η X ∘ (F₁ (μ.η X) ∘ F₁ (F₁ g) ∘ F₁ f) ≈⟨ sym-assoc ⟩
    (μ.η X ∘ F₁ (μ.η X)) ∘ F₁ (F₁ g) ∘ F₁ f ≈⟨ M.assoc ⟩∘⟨refl ⟩
    (μ.η X ∘ μ.η (F₀ X)) ∘ F₁ (F₁ g) ∘ F₁ f ≈⟨ center (μ.commute g) ⟩
    μ.η X ∘ (F₁ g ∘ μ.η B) ∘ F₁ f           ≈⟨ sym-assoc ○ (sym-assoc ⟩∘⟨refl) ○ assoc ⟩
    (μ.η X ∘ F₁ g) ∘ μ.η B ∘ F₁ f           ∎
    where
    trihom : {X Y Z W : Obj} {f : X ⇒ Y} {g : Y ⇒ Z} {h : Z ⇒ W} → F₁ (h ∘ g ∘ f) ≈ F₁ h ∘ F₁ g ∘ F₁ f
    trihom {X} {Y} {Z} {W} {f} {g} {h} = begin
      F₁ (h ∘ g ∘ f)     ≈⟨ homomorphism ⟩
      F₁ h ∘ F₁ (g ∘ f)  ≈⟨ refl⟩∘⟨ homomorphism ⟩
      F₁ h ∘ F₁ g ∘ F₁ f ∎
