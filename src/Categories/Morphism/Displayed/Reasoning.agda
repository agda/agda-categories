{-# OPTIONS --safe --without-K #-}

-- Utilities for reasoning about displayed morphisms

open import Categories.Category
open import Categories.Category.Displayed

module Categories.Morphism.Displayed.Reasoning {o ℓ e o′ ℓ′ e′} {B : Category o ℓ e} (C : Displayed B o′ ℓ′ e′) where

open import Categories.Morphism.Reasoning.Core B

open Category B
open Definitions B
open Displayed C
open Equiv′
open HomReasoning′
open Definitions′ C

private
  variable
    X Y : Obj
    f g h i j k l a b c : X ⇒ Y
    X′ Y′ : Obj[ X ]
    f′ g′ h′ i′ j′ k′ l′ a′ b′ c′ : X′ ⇒[ f ] Y′

module Identity′ where
  id′-comm : ∀ {A B X Y} {f : A ⇒ B} {f′ : X ⇒[ f ] Y} → f′ ∘′ id′ ≈[ id-comm ] id′ ∘′ f′
  id′-comm = trans′ identityʳ′ (sym′ identityˡ′)

  id′-comm-sym : ∀ {A B X Y} {f : A ⇒ B} {f′ : X ⇒[ f ] Y} → id′ ∘′ f′ ≈[ id-comm-sym ] f′ ∘′ id′
  id′-comm-sym = trans′ identityˡ′ (sym′ identityʳ′)

open Identity′ public

module Pulls′ {ab≈c : a ∘ b ≈ c} (a′b′≈[]c′ : a′ ∘′ b′ ≈[ ab≈c ] c′) where

  pullʳ′ : (f′ ∘′ a′) ∘′ b′ ≈[ pullʳ ab≈c ] f′ ∘′ c′
  pullʳ′ {f′ = f′} = begin′
    (f′ ∘′ a′) ∘′ b′ ≈[]⟨ assoc′ ⟩
    f′ ∘′ (a′ ∘′ b′) ≈[]⟨ refl′⟩∘′⟨ a′b′≈[]c′ ⟩
    f′ ∘′ c′         ∎′

  pullˡ′ : a′ ∘′ (b′ ∘′ f′) ≈[ pullˡ ab≈c ] c′ ∘′ f′
  pullˡ′ {f′ = f′} = begin′
    a′ ∘′ (b′ ∘′ f′) ≈[]⟨ sym-assoc′ ⟩
    (a′ ∘′ b′) ∘′ f′ ≈[]⟨ a′b′≈[]c′ ⟩∘′⟨refl′ ⟩
    c′ ∘′ f′         ∎′

open Pulls′ public

module Extends′ {s : CommutativeSquare f g h i} (s′ : CommutativeSquare′ f′ g′ h′ i′ s) where
  extendˡ′ : CommutativeSquare′ f′ g′ (a′ ∘′ h′) (a′ ∘′ i′) (extendˡ s)
  extendˡ′ {a′ = a′} = begin′
    (a′ ∘′ h′) ∘′ f′ ≈[]⟨ pullʳ′ s′ ⟩
    a′ ∘′ (i′ ∘′ g′) ≈[]⟨ sym-assoc′ ⟩
    (a′ ∘′ i′) ∘′ g′ ∎′

  extendʳ′ : CommutativeSquare′ (f′ ∘′ a′) (g′ ∘′ a′) h′ i′ (extendʳ s)
  extendʳ′ {a′ = a′} = begin′
    h′ ∘′ (f′ ∘′ a′) ≈[]⟨ pullˡ′ s′ ⟩
    (i′ ∘′ g′) ∘′ a′ ≈[]⟨ assoc′ ⟩
    i′ ∘′ (g′ ∘′ a′) ∎′

  extend²′ : CommutativeSquare′ (f′ ∘′ b′) (g′ ∘′ b′) (a′ ∘′ h′) (a′ ∘′ i′) (extend² s)
  extend²′ {b′ = b′} {a′ = a′} = begin′
    (a′ ∘′ h′) ∘′ (f′ ∘′ b′) ≈[]⟨ pullʳ′ extendʳ′ ⟩
    a′ ∘′ (i′ ∘′ (g′ ∘′ b′)) ≈[]⟨ sym-assoc′ ⟩
    (a′ ∘′ i′) ∘′ (g′ ∘′ b′) ∎′

open Extends′ public

glue′ : ∀ {sq₁ : CommutativeSquare f g h i} {sq₂ : CommutativeSquare j k l f}
        → CommutativeSquare′ f′ g′ h′ i′ sq₁
        → CommutativeSquare′ j′ k′ l′ f′ sq₂
        → CommutativeSquare′ j′ (g′ ∘′ k′) (h′ ∘′ l′) i′ (glue sq₁ sq₂)
glue′ {f′ = f′} {g′ = g′} {h′ = h′} {i′ = i′} {j′ = j′} {k′ = k′} {l′ = l′} sq₁′ sq₂′ = begin′
  (h′ ∘′ l′) ∘′ j′ ≈[]⟨ pullʳ′ sq₂′ ⟩
  h′ ∘′ (f′ ∘′ k′) ≈[]⟨ extendʳ′ sq₁′ ⟩
  i′ ∘′ (g′ ∘′ k′) ∎′

sym-glue′ : ∀ {sq₁ : CommutativeSquare f g h i} {sq₂ : CommutativeSquare j k g l}
            → CommutativeSquare′ f′ g′ h′ i′ sq₁
            → CommutativeSquare′ j′ k′ g′ l′ sq₂
            → CommutativeSquare′ (f′ ∘′ j′) k′ h′ (i′ ∘′ l′) (sym-glue sq₁ sq₂)
sym-glue′ {f′ = f′} {g′ = g′} {h′ = h′} {i′ = i′} {j′ = j′} {k′ = k′} {l′ = l′} sq₁′ sq₂′ = begin′
  h′ ∘′ (f′ ∘′ j′) ≈[]⟨ pullˡ′ sq₁′ ⟩
  (i′ ∘′ g′) ∘′ j′ ≈[]⟨ extendˡ′ sq₂′ ⟩
  (i′ ∘′ l′) ∘′ k′ ∎′
