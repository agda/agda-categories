{-# OPTIONS --without-K --safe #-}
module Categories.Category.Construction.F-Coalgebras where

open import Level using (Level; _⊔_)

open import Categories.Category.Core using (Category)
open import Categories.Functor using (Functor; Endofunctor)
open import Categories.Functor.Coalgebra using (F-Coalgebra; F-Coalgebra-Morphism)
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level

F-Coalgebras : {C : Category o ℓ e} → Endofunctor C → Category (o ⊔ ℓ) (ℓ ⊔ e) e
F-Coalgebras {C = C} F = record
  { Obj = F-Coalgebra F
  ; _⇒_ = F-Coalgebra-Morphism
  ; _≈_ = λ α₁ α₂ → f α₁ ≈ f α₂
  ; id = record { f = id ; commutes = ∘-resp-≈ˡ identity ○ id-comm-sym }
  ; _∘_ = λ α₁ α₂ → record { f = f α₁ ∘ f α₂ ; commutes = commut α₁ α₂ }
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  ; ∘-resp-≈ = ∘-resp-≈
  }
  where
    open Category C using (_∘_; id; _≈_; assoc; sym-assoc; identityˡ; identityʳ; identity²; ∘-resp-≈; ∘-resp-≈ˡ; module Equiv; module HomReasoning)
    open MR C using (id-comm-sym; pushˡ; pushʳ)
    open HomReasoning using (begin_; step-≈; _∎; _○_)
    open Equiv using (refl; sym; trans)
    open Functor F using (F₁; homomorphism; identity)
    open F-Coalgebra using (α)
    open F-Coalgebra-Morphism using (f; commutes)
    commut : {A B C : F-Coalgebra F} (α₁ : F-Coalgebra-Morphism B C) (α₂ : F-Coalgebra-Morphism A B) →
      F₁ (f α₁ ∘ f α₂) ∘ α A ≈ α C ∘ (f α₁ ∘ f α₂)
    commut {A} {B} {C} α₁ α₂ = begin
      F₁ (f α₁ ∘ f α₂) ∘ α A        ≈⟨ pushˡ homomorphism ⟩
      F₁ (f α₁) ∘ (F₁ (f α₂) ∘ α A) ≈⟨ pushʳ (commutes α₂) ⟩
      (F₁ (f α₁) ∘ α B) ∘ f α₂      ≈⟨ pushˡ (commutes α₁) ⟩
      α C ∘ (f α₁ ∘ f α₂)           ∎
