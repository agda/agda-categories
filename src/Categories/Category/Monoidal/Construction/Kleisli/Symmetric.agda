{-# OPTIONS --without-K --safe #-}
module Categories.Category.Monoidal.Construction.Kleisli.Symmetric where

open import Level
open import Data.Product using (_,_)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Bifunctor using (flip-bifunctor)
open import Categories.Monad using (Monad)
open import Categories.Monad.Commutative using (CommutativeMonad)
open import Categories.Monad.Commutative.Properties using (module CommutativeProperties)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)
open import Categories.NaturalTransformation using (ntHelper)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Braided using (Braided)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.Construction.Kleisli using (module TripleNotation)
open import Categories.Category.Monoidal.Construction.Kleisli using (Kleisli-Monoidal; ⊗')

import Categories.Morphism.Reasoning as MR
import Categories.Monad.Strong.Properties as StrongProps
import Categories.Category.Monoidal.Symmetric.Properties as SymmProps
import Categories.Category.Monoidal.Utilities as MonoidalUtils

private
  variable
    o ℓ e : Level

-- The Kleisli category of a commutative monad (where 𝒞 is symmetric) is symmetric.

module _ {𝒞 : Category o ℓ e} {monoidal : Monoidal 𝒞} (symmetric : Symmetric monoidal) (CM : CommutativeMonad (Symmetric.braided symmetric)) where
  open Category 𝒞
  open MR 𝒞
  open HomReasoning
  open Equiv

  open CommutativeMonad CM hiding (identityˡ)
  open Monad M using (μ)
  open TripleNotation M

  open StrongProps.Left strength using (left-right-braiding-comm; right-left-braiding-comm)
  open StrongProps.Left.Shorthands strength
  open StrongProps.Right.Shorthands rightStrength
  open MonoidalUtils.Shorthands monoidal using (α⇒; α⇐)

  open Symmetric symmetric renaming (commutative to B-commutative)
  open SymmProps symmetric
  open CommutativeProperties braided CM

  private
    B : ∀ {X Y} → X ⊗₀ Y ⇒ Y ⊗₀ X
    B {X} {Y} = braiding.⇒.η (X , Y)

  braiding' : NaturalIsomorphism (⊗' symmetric CM) (flip-bifunctor (⊗' symmetric CM))
  braiding' = record
    { F⇒G = ntHelper (record { η = λ _ → η ∘ B ; commute = λ (f , g) → swapping f g })
    ; F⇐G = ntHelper (record { η = λ _ → η ∘ B ; commute = λ (f , g) → swapping g f })
    ; iso = λ _ → record { isoˡ = pullˡ *-identityʳ ○ cancelʳ B-commutative ; isoʳ = pullˡ *-identityʳ ○ cancelʳ B-commutative }
    }
    where
    swapping : ∀ {X Y U V} (f : X ⇒ M.F.₀ Y) (g : U ⇒ M.F.₀ V) → (η ∘ B) * ∘ ψ ∘ (f ⊗₁ g) ≈ (ψ ∘ (g ⊗₁ f)) * ∘ η ∘ B
    swapping f g = begin
      (η ∘ B) * ∘ ψ ∘ (f ⊗₁ g)
        ≈⟨ *⇒F₁ ⟩∘⟨refl ⟩
      M.F.₁ B ∘ ψ ∘ (f ⊗₁ g)
        ≈⟨ refl⟩∘⟨ commutes ⟩∘⟨refl ⟩
      M.F.₁ B ∘ (σ * ∘ τ) ∘ (f ⊗₁ g)
        ≈⟨ extendʳ (pullˡ F₁∘*) ⟩
      (M.F.₁ B ∘ σ) * ∘ τ ∘ (f ⊗₁ g)
        ≈⟨ *-resp-≈ (∘-resp-≈ˡ (M.F.F-resp-≈ (sym braiding-selfInverse)) ○ left-right-braiding-comm braided ○ ∘-resp-≈ʳ braiding-selfInverse) ⟩∘⟨refl ⟩
      (τ ∘ B) * ∘ τ ∘ (f ⊗₁ g)
        ≈˘⟨ pullˡ (pullˡ *∘F₁) ○ assoc ⟩
      τ * ∘ (M.F.₁ B ∘ τ) ∘ (f ⊗₁ g)
        ≈˘⟨ extendʳ (pullʳ (sym (right-left-braiding-comm braided))) ⟩
      ψ ∘ B ∘ (f ⊗₁ g)
        ≈⟨ refl⟩∘⟨ braiding.⇒.commute _ ⟩
      ψ ∘ (g ⊗₁ f) ∘ B
        ≈˘⟨ extendʳ *-identityʳ ⟩
      (ψ ∘ (g ⊗₁ f)) * ∘ η ∘ B
        ∎

  Kleisli-Braided : Braided (Kleisli-Monoidal symmetric CM)
  Kleisli-Braided = record
    { braiding = braiding'
    ; hexagon₁ = hexagon₁'
    ; hexagon₂ = hexagon₂'
    }
    where
    hexagon₁' : ∀ {X Y Z : Obj} → (ψ {X} {Y ⊗₀ Z} ∘ (η ⊗₁ (η ∘ B))) * ∘ (η ∘ α⇒) * ∘ (ψ ∘ ((η ∘ B) ⊗₁ η)) ≈ (η ∘ α⇒) * ∘ (η ∘ B) * ∘ (η ∘ α⇒)
    hexagon₁' = begin
      (ψ ∘ (η ⊗₁ (η ∘ B))) * ∘ (η ∘ α⇒) * ∘ (ψ ∘ ((η ∘ B) ⊗₁ η))
        ≈⟨ pullˡ *-sym-assoc ⟩
      ((ψ ∘ (η ⊗₁ (η ∘ B))) * ∘ (η ∘ α⇒)) * ∘ (ψ ∘ ((η ∘ B) ⊗₁ η))
        ≈⟨ ((*-resp-≈ (pullˡ *-identityʳ)) ⟩∘⟨refl) ⟩
      ((ψ ∘ (η ⊗₁ (η ∘ B))) ∘ α⇒) * ∘ (ψ ∘ ((η ∘ B) ⊗₁ η))
        ≈˘⟨ *-resp-≈ (∘-resp-≈ˡ (∘-resp-≈ʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identityʳ , refl)))) ⟩∘⟨ ∘-resp-≈ʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (refl , identityʳ)) ⟩
      ((ψ ∘ (η ⊗₁ η) ∘ (id ⊗₁ B)) ∘ α⇒) * ∘ (ψ ∘ (η ⊗₁ η) ∘ (B ⊗₁ id))
        ≈⟨ *-resp-≈ (∘-resp-≈ˡ (pullˡ ψ-η)) ⟩∘⟨ pullˡ ψ-η ⟩
      ((η ∘ (id ⊗₁ B)) ∘ α⇒) * ∘ (η ∘ (B ⊗₁ id))
        ≈⟨ pullˡ *-identityʳ ⟩
      ((η ∘ (id ⊗₁ B)) ∘ α⇒) ∘ (B ⊗₁ id)
        ≈⟨ (assoc ○ pullʳ hexagon₁ ○ (sym-assoc ○ sym-assoc)) ⟩
      ((η ∘ α⇒) ∘ B) ∘ α⇒
        ≈˘⟨ pullˡ (pullˡ *-identityʳ) ⟩
      (η ∘ α⇒) * ∘ (η ∘ B) ∘ α⇒
        ≈˘⟨ refl⟩∘⟨ (pullˡ *-identityʳ) ⟩
      (η ∘ α⇒) * ∘ (η ∘ B) * ∘ (η ∘ α⇒)
        ∎
    hexagon₂' : ∀ {X Y Z : Obj} → ((ψ {X ⊗₀ Y} {Z} ∘ ((η ∘ B) ⊗₁ η)) * ∘ (η ∘ α⇐)) * ∘ (ψ ∘ (η ⊗₁ (η ∘ B))) ≈ ((η ∘ α⇐) * ∘ (η ∘ B)) * ∘ (η ∘ α⇐)
    hexagon₂' = begin
      ((ψ ∘ ((η ∘ B) ⊗₁ η)) * ∘ (η ∘ α⇐)) * ∘ (ψ ∘ (η ⊗₁ (η ∘ B)))
        ≈⟨ ((*-resp-≈ (pullˡ *-identityʳ)) ⟩∘⟨refl) ⟩
      ((ψ ∘ ((η ∘ B) ⊗₁ η)) ∘ α⇐) * ∘ (ψ ∘ (η ⊗₁ (η ∘ B)))
        ≈˘⟨ *-resp-≈ (∘-resp-≈ˡ (∘-resp-≈ʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (refl , identityʳ)))) ⟩∘⟨ ∘-resp-≈ʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identityʳ , refl)) ⟩
      ((ψ ∘ (η ⊗₁ η) ∘ (B ⊗₁ id)) ∘ α⇐) * ∘ (ψ ∘ (η ⊗₁ η) ∘ (id ⊗₁ B))
        ≈⟨ *-resp-≈ (∘-resp-≈ˡ (pullˡ ψ-η)) ⟩∘⟨ pullˡ ψ-η ⟩
      ((η ∘ (B ⊗₁ id)) ∘ α⇐) * ∘ (η ∘ (id ⊗₁ B))
        ≈⟨ pullˡ *-identityʳ ⟩
      ((η ∘ (B ⊗₁ id)) ∘ α⇐) ∘ (id ⊗₁ B)
        ≈⟨ (assoc ○ pullʳ (sym-assoc ○ hexagon₂) ○ (sym-assoc ○ ∘-resp-≈ˡ sym-assoc)) ⟩
      ((η ∘ α⇐) ∘ B) ∘ α⇐
        ≈˘⟨ pullˡ (pullˡ *-identityʳ) ⟩
      (η ∘ α⇐) * ∘ (η ∘ B) ∘ α⇐
        ≈˘⟨ refl⟩∘⟨ (pullˡ *-identityʳ) ⟩
      (η ∘ α⇐) * ∘ (η ∘ B) * ∘ (η ∘ α⇐)
        ≈˘⟨ *-assoc ⟩∘⟨refl ○ assoc ⟩
      ((η ∘ α⇐) * ∘ (η ∘ B)) * ∘ (η ∘ α⇐)
        ∎

  Kleisli-Symmetric : Symmetric (Kleisli-Monoidal symmetric CM)
  Kleisli-Symmetric = record 
    { braided = Kleisli-Braided
    ; commutative = λ {X} {Y} → pullˡ *-identityʳ ○ cancelʳ B-commutative
    }
