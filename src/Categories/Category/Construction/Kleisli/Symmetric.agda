{-# OPTIONS --without-K --allow-unsolved-metas #-}
module Categories.Category.Construction.Kleisli.Symmetric where

open import Level

open import Categories.Category
open import Categories.Monad hiding (id)
open import Categories.Monad.Strong
open import Categories.Monad.Strong.Properties
open import Categories.Monad.Commutative
open import Categories.Category.Construction.Kleisli
open import Categories.Category.Cartesian
open import Categories.Category.Cartesian.SymmetricMonoidal
open import Categories.Category.Cartesian.Monoidal
open import Categories.Category.BinaryProducts
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Symmetric
open import Categories.Object.Terminal
open import Categories.NaturalTransformation.Core using (ntHelper)
open import Categories.Category.Construction.Kleisli.Monoidal

open import Data.Product using (_,_)

import Categories.Morphism.Reasoning as MR

import Categories.Monad.Strong.Properties as StrongProps

private
  variable
    o ℓ e : Level

module _ {𝒞 : Category o ℓ e} (cartesian : Cartesian 𝒞) (CM : CommutativeMonad (Symmetric.braided (symmetric 𝒞 cartesian))) where
  open Category 𝒞
  open MR 𝒞
  open HomReasoning
  open Equiv
  open Cartesian cartesian
  open Terminal terminal
  open BinaryProducts products hiding (η)

  open CommutativeMonad CM hiding (identityˡ)
  open Monad M using (μ)
  open TripleNotation M

  open StrongProps.Left strength using (left-right-braiding-comm; right-left-braiding-comm)
  open StrongProps.Left.Shorthands strength
  open StrongProps.Right.Shorthands rightStrength

  open CartesianMonoidal cartesian using (monoidal)
  open Monoidal monoidal
  open Symmetric (symmetric 𝒞 cartesian) using (braided; hexagon₁; hexagon₂)

  Kleisli-Symmetric : Symmetric (Kleisli-Monoidal cartesian CM)
  Kleisli-Symmetric = record 
    { braided = record 
      { braiding = record 
        { F⇒G = record { η = λ _ → η ∘ swap ; commute = λ (f , g) → swapping f g ; sym-commute = λ (f , g) → sym (swapping f g) }
        ; F⇐G = record { η = λ _ → η ∘ swap ; commute = λ (f , g) → swapping g f ; sym-commute = λ (f , g) → sym (swapping g f) }
        ; iso = λ _ → record { isoˡ = pullˡ *-identityʳ ○ cancelʳ swap∘swap ; isoʳ = pullˡ *-identityʳ ○ cancelʳ swap∘swap } 
        } 
      ; hexagon₁ = λ {X} {Y} {Z} → begin 
        (ψ ∘ (η ⁂ η ∘ swap)) * ∘ (η ∘ associator.from) * ∘ (ψ ∘ (η ∘ swap ⁂ η))         ≈⟨ pullˡ *-sym-assoc ⟩ 
        ((ψ ∘ (η ⁂ η ∘ swap)) * ∘ (η ∘ associator.from)) * ∘ (ψ ∘ (η ∘ swap ⁂ η))       ≈⟨ ((*-resp-≈ (pullˡ *-identityʳ)) ⟩∘⟨refl) ⟩ 
        ((ψ ∘ (η ⁂ η ∘ swap)) ∘ associator.from) * ∘ (ψ ∘ (η ∘ swap ⁂ η))               ≈˘⟨ *-resp-≈ (∘-resp-≈ˡ (∘-resp-≈ʳ (⁂∘⁂ ○ ⁂-cong₂ identityʳ refl))) ⟩∘⟨ ∘-resp-≈ʳ (⁂∘⁂ ○ ⁂-cong₂ refl identityʳ) ⟩ 
        ((ψ ∘ (η ⁂ η) ∘ (id ⁂ swap)) ∘ associator.from) * ∘ (ψ ∘ (η ⁂ η) ∘ (swap ⁂ id)) ≈⟨ *-resp-≈ (∘-resp-≈ˡ (pullˡ ψ-η)) ⟩∘⟨ pullˡ ψ-η ⟩ 
        ((η ∘ (id ⁂ swap)) ∘ associator.from) * ∘ (η ∘ (swap ⁂ id))                     ≈⟨ pullˡ *-identityʳ ⟩ 
        ((η ∘ (id ⁂ swap)) ∘ associator.from) ∘ (swap ⁂ id)                             ≈⟨ (assoc ○ pullʳ hexagon₁ ○ (sym-assoc ○ sym-assoc)) ⟩ 
        ((η ∘ associator.from) ∘ swap) ∘ associator.from                                ≈˘⟨ pullˡ (pullˡ *-identityʳ) ⟩ 
        (η ∘ associator.from) * ∘ (η ∘ swap) ∘ associator.from                          ≈˘⟨ refl⟩∘⟨ (pullˡ *-identityʳ) ⟩ 
        (η ∘ associator.from) * ∘ (η ∘ swap) * ∘ (η ∘ associator.from)                  ∎ 
      ; hexagon₂ = λ {X} {Y} {Z} → begin 
        ((ψ ∘ (η ∘ swap ⁂ η)) * ∘ (η ∘ associator.to)) * ∘ (ψ ∘ (η ⁂ (η ∘ swap)))     ≈⟨ ((*-resp-≈ (pullˡ *-identityʳ)) ⟩∘⟨refl) ⟩ 
        ((ψ ∘ (η ∘ swap ⁂ η)) ∘ associator.to) * ∘ (ψ ∘ (η ⁂ η ∘ swap))               ≈˘⟨ *-resp-≈ (∘-resp-≈ˡ (∘-resp-≈ʳ (⁂∘⁂ ○ ⁂-cong₂ refl identityʳ))) ⟩∘⟨ ∘-resp-≈ʳ (⁂∘⁂ ○ ⁂-cong₂ identityʳ refl) ⟩ 
        ((ψ ∘ (η ⁂ η) ∘ (swap ⁂ id)) ∘ associator.to) * ∘ (ψ ∘ (η ⁂ η) ∘ (id ⁂ swap)) ≈⟨ *-resp-≈ (∘-resp-≈ˡ (pullˡ ψ-η)) ⟩∘⟨ pullˡ ψ-η ⟩ 
        ((η ∘ (swap ⁂ id)) ∘ associator.to) * ∘ (η ∘ (id ⁂ swap))                     ≈⟨ pullˡ *-identityʳ ⟩ 
        ((η ∘ (swap ⁂ id)) ∘ associator.to) ∘ (id ⁂ swap)                             ≈⟨ (assoc ○ pullʳ (sym-assoc ○ hexagon₂) ○ (sym-assoc ○ ∘-resp-≈ˡ sym-assoc)) ⟩
        ((η ∘ associator.to) ∘ swap) ∘ associator.to                                  ≈˘⟨ pullˡ (pullˡ *-identityʳ) ⟩ 
        (η ∘ associator.to) * ∘ (η ∘ swap) ∘ associator.to                            ≈˘⟨ refl⟩∘⟨ (pullˡ *-identityʳ) ⟩ 
        (η ∘ associator.to) * ∘ (η ∘ swap) * ∘ (η ∘ associator.to)                    ≈˘⟨ *-assoc ⟩∘⟨refl ○ assoc ⟩ 
        ((η ∘ associator.to) * ∘ (η ∘ swap)) * ∘ (η ∘ associator.to)                  ∎ 
      } 
    ; commutative = λ {X} {Y} → pullˡ *-identityʳ ○ cancelʳ swap∘swap 
    }
    where
    swapping : ∀ {X Y A B} (f : X ⇒ M.F.₀ Y) (g : A ⇒ M.F.₀ B) → (η ∘ swap) * ∘ ψ ∘ (f ⁂ g) ≈ (ψ ∘ (g ⁂ f)) * ∘ η ∘ swap
    swapping f g = begin 
      (η ∘ swap) * ∘ ψ ∘ (f ⁂ g)       ≈⟨ *⇒F₁ ⟩∘⟨refl ⟩ 
      M.F.₁ swap ∘ ψ ∘ (f ⁂ g)         ≈⟨ refl⟩∘⟨ commutes ⟩∘⟨refl ⟩ 
      M.F.₁ swap ∘ (σ * ∘ τ) ∘ (f ⁂ g) ≈⟨ extendʳ (pullˡ F₁∘*) ⟩
      (M.F.₁ swap ∘ σ) * ∘ τ ∘ (f ⁂ g) ≈⟨ ((*-resp-≈ (left-right-braiding-comm braided)) ⟩∘⟨refl) ⟩
      (τ ∘ swap) * ∘ τ ∘ (f ⁂ g)       ≈˘⟨ pullˡ (pullˡ *∘F₁) ○ assoc ⟩
      τ * ∘ (M.F.₁ swap ∘ τ) ∘ (f ⁂ g) ≈˘⟨ extendʳ (pullʳ (sym (right-left-braiding-comm braided))) ⟩
      ψ ∘ swap ∘ (f ⁂ g)               ≈⟨ refl⟩∘⟨ swap∘⁂ ⟩ 
      ψ ∘ (g ⁂ f) ∘ swap               ≈˘⟨ extendʳ *-identityʳ ⟩ 
      (ψ ∘ (g ⁂ f)) * ∘ η ∘ swap       ∎

