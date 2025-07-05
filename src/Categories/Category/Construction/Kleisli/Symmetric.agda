{-# OPTIONS --without-K --safe #-}
module Categories.Category.Construction.Kleisli.Symmetric where

open import Level
open import Data.Product using (_,_)

open import Categories.Category.Core using (Category)
open import Categories.Monad using (Monad)
open import Categories.Monad.Commutative using (CommutativeMonad)
open import Categories.Monad.Commutative.Properties using (module CommutativeProperties)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.Construction.Kleisli
open import Categories.Category.Construction.Kleisli.Monoidal using (Kleisli-Monoidal)

import Categories.Morphism.Reasoning as MR
import Categories.Monad.Strong.Properties as StrongProps
import Categories.Category.Monoidal.Symmetric.Properties as SymmProps

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

  open Symmetric symmetric renaming (commutative to B-commutative)
  open SymmProps symmetric
  open CommutativeProperties braided CM

  private
    B : ∀ {X Y} → X ⊗₀ Y ⇒ Y ⊗₀ X
    B {X} {Y} = braiding.⇒.η (X , Y)

  Kleisli-Symmetric : Symmetric (Kleisli-Monoidal symmetric CM)
  Kleisli-Symmetric = record 
    { braided = record 
      { braiding = record 
        { F⇒G = record { η = λ _ → η ∘ B ; commute = λ (f , g) → swapping f g ; sym-commute = λ (f , g) → sym (swapping f g) }
        ; F⇐G = record { η = λ _ → η ∘ B ; commute = λ (f , g) → swapping g f ; sym-commute = λ (f , g) → sym (swapping g f) }
        ; iso = λ _ → record { isoˡ = pullˡ *-identityʳ ○ cancelʳ B-commutative ; isoʳ = pullˡ *-identityʳ ○ cancelʳ B-commutative } 
        } 
      ; hexagon₁ = hexagon₁'
      ; hexagon₂ = hexagon₂'
      } 
    ; commutative = λ {X} {Y} → pullˡ *-identityʳ ○ cancelʳ B-commutative 
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
    hexagon₁' : ∀ {X Y Z : Obj} → (ψ {X} {Y ⊗₀ Z} ∘ (η ⊗₁ (η ∘ B))) * ∘ (η ∘ associator.from) * ∘ (ψ ∘ ((η ∘ B) ⊗₁ η)) ≈ (η ∘ associator.from) * ∘ (η ∘ B) * ∘ (η ∘ associator.from)
    hexagon₁' = begin 
      (ψ ∘ (η ⊗₁ (η ∘ B))) * ∘ (η ∘ associator.from) * ∘ (ψ ∘ ((η ∘ B) ⊗₁ η))       
        ≈⟨ pullˡ *-sym-assoc ⟩ 
      ((ψ ∘ (η ⊗₁ (η ∘ B))) * ∘ (η ∘ associator.from)) * ∘ (ψ ∘ ((η ∘ B) ⊗₁ η))     
        ≈⟨ ((*-resp-≈ (pullˡ *-identityʳ)) ⟩∘⟨refl) ⟩ 
      ((ψ ∘ (η ⊗₁ (η ∘ B))) ∘ associator.from) * ∘ (ψ ∘ ((η ∘ B) ⊗₁ η))             
        ≈˘⟨ *-resp-≈ (∘-resp-≈ˡ (∘-resp-≈ʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identityʳ , refl)))) ⟩∘⟨ ∘-resp-≈ʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (refl , identityʳ)) ⟩ 
      ((ψ ∘ (η ⊗₁ η) ∘ (id ⊗₁ B)) ∘ associator.from) * ∘ (ψ ∘ (η ⊗₁ η) ∘ (B ⊗₁ id)) 
        ≈⟨ *-resp-≈ (∘-resp-≈ˡ (pullˡ ψ-η)) ⟩∘⟨ pullˡ ψ-η ⟩ 
      ((η ∘ (id ⊗₁ B)) ∘ associator.from) * ∘ (η ∘ (B ⊗₁ id))                       
        ≈⟨ pullˡ *-identityʳ ⟩ 
      ((η ∘ (id ⊗₁ B)) ∘ associator.from) ∘ (B ⊗₁ id)                               
        ≈⟨ (assoc ○ pullʳ hexagon₁ ○ (sym-assoc ○ sym-assoc)) ⟩ 
      ((η ∘ associator.from) ∘ B) ∘ associator.from                                 
        ≈˘⟨ pullˡ (pullˡ *-identityʳ) ⟩ 
      (η ∘ associator.from) * ∘ (η ∘ B) ∘ associator.from                           
        ≈˘⟨ refl⟩∘⟨ (pullˡ *-identityʳ) ⟩ 
      (η ∘ associator.from) * ∘ (η ∘ B) * ∘ (η ∘ associator.from)                   
        ∎
    hexagon₂' : ∀ {X Y Z : Obj} → ((ψ {X ⊗₀ Y} {Z} ∘ ((η ∘ B) ⊗₁ η)) * ∘ (η ∘ associator.to)) * ∘ (ψ ∘ (η ⊗₁ (η ∘ B))) ≈ ((η ∘ associator.to) * ∘ (η ∘ B)) * ∘ (η ∘ associator.to)
    hexagon₂' = begin 
      ((ψ ∘ ((η ∘ B) ⊗₁ η)) * ∘ (η ∘ associator.to)) * ∘ (ψ ∘ (η ⊗₁ (η ∘ B)))     
        ≈⟨ ((*-resp-≈ (pullˡ *-identityʳ)) ⟩∘⟨refl) ⟩ 
      ((ψ ∘ ((η ∘ B) ⊗₁ η)) ∘ associator.to) * ∘ (ψ ∘ (η ⊗₁ (η ∘ B)))             
        ≈˘⟨ *-resp-≈ (∘-resp-≈ˡ (∘-resp-≈ʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (refl , identityʳ)))) ⟩∘⟨ ∘-resp-≈ʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identityʳ , refl)) ⟩ 
      ((ψ ∘ (η ⊗₁ η) ∘ (B ⊗₁ id)) ∘ associator.to) * ∘ (ψ ∘ (η ⊗₁ η) ∘ (id ⊗₁ B)) 
        ≈⟨ *-resp-≈ (∘-resp-≈ˡ (pullˡ ψ-η)) ⟩∘⟨ pullˡ ψ-η ⟩ 
      ((η ∘ (B ⊗₁ id)) ∘ associator.to) * ∘ (η ∘ (id ⊗₁ B))                       
        ≈⟨ pullˡ *-identityʳ ⟩ 
      ((η ∘ (B ⊗₁ id)) ∘ associator.to) ∘ (id ⊗₁ B)                               
        ≈⟨ (assoc ○ pullʳ (sym-assoc ○ hexagon₂) ○ (sym-assoc ○ ∘-resp-≈ˡ sym-assoc)) ⟩
      ((η ∘ associator.to) ∘ B) ∘ associator.to                                   
        ≈˘⟨ pullˡ (pullˡ *-identityʳ) ⟩ 
      (η ∘ associator.to) * ∘ (η ∘ B) ∘ associator.to                             
        ≈˘⟨ refl⟩∘⟨ (pullˡ *-identityʳ) ⟩ 
      (η ∘ associator.to) * ∘ (η ∘ B) * ∘ (η ∘ associator.to)                     
        ≈˘⟨ *-assoc ⟩∘⟨refl ○ assoc ⟩ 
      ((η ∘ associator.to) * ∘ (η ∘ B)) * ∘ (η ∘ associator.to)                   
        ∎ 
