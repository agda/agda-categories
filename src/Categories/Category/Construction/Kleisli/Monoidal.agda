{-# OPTIONS --without-K --safe #-}
module Categories.Category.Construction.Kleisli.Monoidal where

open import Level
open import Data.Product using (_,_)

open import Categories.Category.Core using (Category)
open import Categories.Monad using (Monad)
open import Categories.Monad.Strong using (Strength; RightStrength)
open import Categories.Monad.Commutative using (CommutativeMonad)
open import Categories.Monad.Commutative.Properties using (module CommutativeProperties; module SymmetricProperties)
open import Categories.Category.Construction.Kleisli using (Kleisli; module TripleNotation)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)


import Categories.Morphism.Reasoning as MR
import Categories.Monad.Strong.Properties as StrongProps

private
  variable
    o ℓ e : Level

-- The Kleisli category of a commutative monad (where 𝒞 is symmetric) is monoidal.

module _ {𝒞 : Category o ℓ e} {monoidal : Monoidal 𝒞} (symmetric : Symmetric monoidal) (CM : CommutativeMonad (Symmetric.braided symmetric)) where
  open Category 𝒞
  open MR 𝒞
  open HomReasoning
  open Equiv

  open CommutativeMonad CM hiding (identityˡ)
  open Monad M using (μ)
  open TripleNotation M

  open StrongProps.Left.Shorthands strength
  open StrongProps.Right.Shorthands rightStrength

  open Symmetric symmetric
  open CommutativeProperties braided CM
  open SymmetricProperties symmetric CM

  Kleisli-Monoidal : Monoidal (Kleisli M)
  Kleisli-Monoidal = record
    { ⊗ = record
      { F₀ = λ (X , Y) → X ⊗₀ Y
      ; F₁ = λ (f , g) → ψ ∘ (f ⊗₁ g)
      ; identity = begin 
        (τ * ∘ σ) ∘ (η ⊗₁ η)              ≈˘⟨ refl⟩∘⟨ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identityˡ , identityʳ)) ⟩
        (τ * ∘ σ) ∘ (id ⊗₁ η) ∘ (η ⊗₁ id) ≈⟨ pullʳ (pullˡ η-comm) ⟩ 
        τ * ∘ η ∘ (η ⊗₁ id)               ≈⟨ pullˡ *-identityʳ ⟩ 
        τ ∘ (η ⊗₁ id)                     ≈⟨ RightStrength.η-comm rightStrength ⟩
        η                                 ∎
      ; homomorphism = λ {X} {Y} {Z} {(f , g)} {(h , i)} → begin 
        ψ ∘ ((h * ∘ f) ⊗₁ (i * ∘ g))                           ≈˘⟨ refl⟩∘⟨ (pullˡ (sym ⊗.homomorphism) ○ sym ⊗.homomorphism) ⟩ 
        ψ ∘ (μ.η _ ⊗₁ μ.η _) ∘ (M.F.₁ h ⊗₁ M.F.₁ i) ∘ (f ⊗₁ g) ≈˘⟨ extendʳ ψ-μ ⟩ 
        ψ * ∘ ψ ∘ (M.F.₁ h ⊗₁ M.F.₁ i) ∘ (f ⊗₁ g)              ≈⟨ refl⟩∘⟨ extendʳ ψ-comm ⟩ 
        ψ * ∘ M.F.₁ (h ⊗₁ i) ∘ ψ ∘ (f ⊗₁ g)                    ≈⟨ pullˡ *∘F₁ ⟩ 
        (ψ ∘ (h ⊗₁ i)) * ∘ ψ ∘ (f ⊗₁ g)                        ∎
      ; F-resp-≈ = λ (f≈g , h≈i) → ∘-resp-≈ʳ (⊗.F-resp-≈ (f≈g , h≈i))
      }
    ; unit = unit
    ; unitorˡ = record { from = η ∘ unitorˡ.from ; to = η ∘ unitorˡ.to ; iso = record 
      { isoˡ = begin 
        (η ∘ unitorˡ.to) * ∘ (η ∘ unitorˡ.from) ≈⟨ pullˡ *-identityʳ ⟩ 
        (η ∘ unitorˡ.to) ∘ unitorˡ.from         ≈⟨ cancelʳ unitorˡ.isoˡ ⟩ 
        η                                       ∎ 
      ; isoʳ = begin 
        (η ∘ unitorˡ.from) * ∘ (η ∘ unitorˡ.to) ≈⟨ pullˡ *-identityʳ ⟩ 
        (η ∘ unitorˡ.from) ∘ unitorˡ.to         ≈⟨ cancelʳ unitorˡ.isoʳ ⟩ 
        η                                       ∎ 
      } }
    ; unitorʳ = record { from = η ∘ unitorʳ.from ; to = η ∘ unitorʳ.to ; iso = record 
      { isoˡ = begin 
        (η ∘ unitorʳ.to) * ∘ (η ∘ unitorʳ.from) ≈⟨ pullˡ *-identityʳ ⟩ 
        (η ∘ unitorʳ.to) ∘ unitorʳ.from         ≈⟨ cancelʳ unitorʳ.isoˡ ⟩ 
        η                                       ∎ 
      ; isoʳ = begin 
        (η ∘ unitorʳ.from) * ∘ (η ∘ unitorʳ.to) ≈⟨ pullˡ *-identityʳ ⟩ 
        (η ∘ unitorʳ.from) ∘ unitorʳ.to         ≈⟨ cancelʳ unitorʳ.isoʳ ⟩ 
        η                                       ∎ 
      } }
    ; associator = record { from = η ∘ associator.from ; to = η ∘ associator.to ; iso = record 
      { isoˡ = begin 
        (η ∘ associator.to) * ∘ (η ∘ associator.from) ≈⟨ pullˡ *-identityʳ ⟩ 
        (η ∘ associator.to) ∘ associator.from         ≈⟨ cancelʳ associator.isoˡ ⟩ 
        η                                             ∎ 
      ; isoʳ = begin 
        (η ∘ associator.from) * ∘ (η ∘ associator.to) ≈⟨ pullˡ *-identityʳ ⟩ 
        (η ∘ associator.from) ∘ associator.to         ≈⟨ cancelʳ associator.isoʳ ⟩ 
        η                                             ∎ 
      } }    
    ; unitorˡ-commute-from = λ {X} {Y} {f} → begin 
      (η ∘ unitorˡ.from) * ∘ ψ ∘ (η ⊗₁ f)                   ≈⟨ *⇒F₁ ⟩∘⟨ ψ-σ' ⟩ 
      M.F.₁ unitorˡ.from ∘ σ ∘ (id ⊗₁ f)                    ≈⟨ pullˡ (Strength.identityˡ strength) ⟩ 
      unitorˡ.from ∘ (id ⊗₁ f)                              ≈⟨ unitorˡ-commute-from ⟩ 
      f ∘ unitorˡ.from                                      ≈˘⟨ pullˡ *-identityʳ ⟩ 
      f * ∘ η ∘ unitorˡ.from                                ∎
    ; unitorˡ-commute-to = λ {X} {Y} {f} → begin 
      (η ∘ unitorˡ.to) * ∘ f                                       ≈⟨ *⇒F₁ ⟩∘⟨refl ⟩ 
      M.F.₁ unitorˡ.to ∘ f                                         ≈˘⟨ refl⟩∘⟨ (cancelˡ unitorˡ.isoʳ) ⟩ 
      M.F.₁ unitorˡ.to ∘ unitorˡ.from ∘ unitorˡ.to ∘ f             ≈˘⟨ pullʳ (pullˡ (Strength.identityˡ strength)) ⟩
      (M.F.₁ unitorˡ.to ∘ M.F.₁ unitorˡ.from) ∘ σ ∘ unitorˡ.to ∘ f ≈⟨ elimˡ (sym M.F.homomorphism ○ (M.F.F-resp-≈ unitorˡ.isoˡ ○ M.F.identity)) ⟩
      σ ∘ unitorˡ.to ∘ f                                           ≈˘⟨ pullʳ (sym unitorˡ-commute-to) ⟩ 
      (σ ∘ (id ⊗₁ f)) ∘ unitorˡ.to                                 ≈˘⟨ ψ-σ' ⟩∘⟨refl ⟩ 
      (ψ ∘ (η ⊗₁ f)) ∘ unitorˡ.to                                  ≈˘⟨ pullˡ *-identityʳ ⟩ 
      (ψ ∘ (η ⊗₁ f)) * ∘ η ∘ unitorˡ.to                            ∎
    ; unitorʳ-commute-from = λ {X} {Y} {f} → begin 
      (η ∘ unitorʳ.from) * ∘ ψ ∘ (f ⊗₁ η) ≈⟨ *⇒F₁ ⟩∘⟨ ψ-τ' ⟩ 
      M.F.₁ unitorʳ.from ∘ τ ∘ (f ⊗₁ id)  ≈⟨ pullˡ (RightStrength.identityˡ rightStrength) ⟩ 
      unitorʳ.from ∘ (f ⊗₁ id)            ≈⟨ unitorʳ-commute-from ⟩ 
      f ∘ unitorʳ.from                    ≈˘⟨ pullˡ *-identityʳ ⟩ 
      f * ∘ η ∘ unitorʳ.from              ∎
    ; unitorʳ-commute-to = λ {X} {Y} {f} → begin 
      (η ∘ unitorʳ.to) * ∘ f                                       ≈⟨ *⇒F₁ ⟩∘⟨refl ⟩ 
      M.F.₁ unitorʳ.to ∘ f                                         ≈˘⟨ refl⟩∘⟨ (cancelˡ unitorʳ.isoʳ) ⟩ 
      M.F.₁ unitorʳ.to ∘ unitorʳ.from ∘ unitorʳ.to ∘ f             ≈˘⟨ pullʳ (pullˡ (RightStrength.identityˡ rightStrength)) ⟩
      (M.F.₁ unitorʳ.to ∘ M.F.₁ unitorʳ.from) ∘ τ ∘ unitorʳ.to ∘ f ≈⟨ elimˡ (sym M.F.homomorphism ○ (M.F.F-resp-≈ unitorʳ.isoˡ ○ M.F.identity)) ⟩
      τ ∘ unitorʳ.to ∘ f                                           ≈˘⟨ pullʳ (sym unitorʳ-commute-to) ⟩ 
      (τ ∘ (f ⊗₁ id)) ∘ unitorʳ.to                                 ≈˘⟨ ψ-τ' ⟩∘⟨refl ⟩ 
      (ψ ∘ (f ⊗₁ η)) ∘ unitorʳ.to                                  ≈˘⟨ pullˡ *-identityʳ ⟩ 
      (ψ ∘ (f ⊗₁ η)) * ∘ η ∘ unitorʳ.to                            ∎
    ; assoc-commute-from = λ {X} {Y} {f} {A} {B} {g} {U} {V} {h} → begin 
      (η ∘ associator.from) * ∘ ψ ∘ ((ψ ∘ (f ⊗₁ g)) ⊗₁ h)     ≈⟨ *⇒F₁ ⟩∘⟨refl ⟩ 
      M.F.₁ associator.from ∘ ψ ∘ ((ψ ∘ (f ⊗₁ g)) ⊗₁ h)       ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (refl , identityˡ)) ⟩ 
      M.F.₁ associator.from ∘ ψ ∘ (ψ ⊗₁ id) ∘ ((f ⊗₁ g) ⊗₁ h) ≈⟨ (sym-assoc ○ pullˡ (assoc ○ ψ-assoc-from) ○ assoc²βε) ⟩ 
      ψ ∘ (id ⊗₁ ψ) ∘ associator.from ∘ ((f ⊗₁ g) ⊗₁ h)       ≈˘⟨ pullʳ (pullʳ (sym assoc-commute-from)) ⟩ 
      (ψ ∘ (id ⊗₁ ψ) ∘ (f ⊗₁ (g ⊗₁ h))) ∘ associator.from     ≈⟨ (refl⟩∘⟨ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identityˡ , refl))) ⟩∘⟨refl ⟩ 
      (ψ ∘ (f ⊗₁ (ψ ∘ (g ⊗₁ h)))) ∘ associator.from           ≈˘⟨ pullˡ *-identityʳ ⟩ 
      (ψ ∘ (f ⊗₁ (ψ ∘ (g ⊗₁ h)))) * ∘ (η ∘ associator.from)   ∎
    ; assoc-commute-to = λ {X} {Y} {f} {A} {B} {g} {U} {V} {h} → begin 
      (η ∘ associator.to) * ∘ ψ ∘ (f ⊗₁ (ψ ∘ (g ⊗₁ h)))     ≈⟨ *⇒F₁ ⟩∘⟨refl ⟩ 
      M.F.₁ associator.to ∘ ψ ∘ (f ⊗₁ (ψ ∘ (g ⊗₁ h)))       ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identityˡ , refl)) ⟩ 
      M.F.₁ associator.to ∘ ψ ∘ (id ⊗₁ ψ) ∘ (f ⊗₁ (g ⊗₁ h)) ≈⟨ (sym-assoc ○ (pullˡ (assoc ○ ψ-assoc-to) ○ assoc²βε)) ⟩ 
      ψ ∘ (ψ ⊗₁ id) ∘ associator.to ∘ (f ⊗₁ (g ⊗₁ h))       ≈˘⟨ pullʳ (pullʳ (sym assoc-commute-to)) ⟩
      (ψ ∘ (ψ ⊗₁ id) ∘ ((f ⊗₁ g) ⊗₁ h)) ∘ associator.to     ≈⟨ (refl⟩∘⟨ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (refl , identityˡ))) ⟩∘⟨refl ⟩ 
      (ψ ∘ ((ψ ∘ (f ⊗₁ g)) ⊗₁ h)) ∘ associator.to           ≈˘⟨ pullˡ *-identityʳ ⟩ 
      (ψ ∘ ((ψ ∘ (f ⊗₁ g)) ⊗₁ h)) * ∘ (η ∘ associator.to)   ∎
    ; triangle = begin 
      (ψ ∘ (η ⊗₁ (η ∘ unitorˡ.from))) * ∘ (η ∘ associator.from) ≈⟨ pullˡ *-identityʳ ⟩ 
      (ψ ∘ (η ⊗₁ (η ∘ unitorˡ.from))) ∘ associator.from         ≈˘⟨ pullˡ (pullʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identityʳ , refl))) ⟩ 
      (ψ ∘ (η ⊗₁ η)) ∘ (id ⊗₁ unitorˡ.from) ∘ associator.from   ≈⟨ (refl⟩∘⟨ triangle) ⟩ 
      (ψ ∘ (η ⊗₁ η)) ∘ (unitorʳ.from ⊗₁ id)                     ≈⟨ pullʳ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (refl , identityʳ)) ⟩  
      ψ ∘ ((η ∘ unitorʳ.from) ⊗₁ η)                             ∎
    ; pentagon = begin 
      (ψ ∘ (η ⊗₁ (η ∘ associator.from))) * ∘ (η ∘ associator.from) * ∘ (ψ ∘ ((η ∘ associator.from) ⊗₁ η)) 
        ≈⟨ refl⟩∘⟨ *⇒F₁ ⟩∘⟨refl ⟩ 
      (ψ ∘ (η ⊗₁ (η ∘ associator.from))) * ∘ M.F.₁ associator.from ∘ (ψ ∘ ((η ∘ associator.from) ⊗₁ η))   
        ≈⟨ pullˡ (*∘F₁ ○ *-resp-≈ assoc) ⟩ 
      (ψ ∘ (η ⊗₁ (η ∘ associator.from)) ∘ associator.from) * ∘ (ψ ∘ ((η ∘ associator.from) ⊗₁ η))         
        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (refl , identityʳ)) ⟩ 
      (ψ ∘ (η ⊗₁ (η ∘ associator.from)) ∘ associator.from) * ∘ (ψ ∘ (η ⊗₁ η) ∘ (associator.from ⊗₁ id))  
        ≈⟨ refl⟩∘⟨ pullˡ ψ-η ⟩ 
      (ψ ∘ (η ⊗₁ (η ∘ associator.from)) ∘ associator.from) * ∘ (η ∘ (associator.from ⊗₁ id))            
        ≈⟨ pullˡ *-identityʳ ⟩ 
      (ψ ∘ (η ⊗₁ (η ∘ associator.from)) ∘ associator.from) ∘ (associator.from ⊗₁ id)                    
        ≈˘⟨ sym-assoc ○ (∘-resp-≈ʳ sym-assoc ○ pullˡ (pullʳ (pullˡ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identityʳ , refl))))) ⟩ 
      ψ ∘ (η ⊗₁ η) ∘ (id ⊗₁ associator.from) ∘ associator.from ∘ (associator.from ⊗₁ id)                 
        ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ pentagon) ⟩ 
      ψ ∘ (η ⊗₁ η) ∘ (associator.from ∘ associator.from)                                               
        ≈⟨ (pullˡ ψ-η) ○ sym-assoc ⟩ 
      (η ∘ associator.from) ∘ associator.from                                                         
        ≈˘⟨ pullˡ *-identityʳ ⟩ 
      (η ∘ associator.from) * ∘ (η ∘ associator.from)                                                 
        ∎
    }
