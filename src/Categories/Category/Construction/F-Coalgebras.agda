{-# OPTIONS --without-K --safe #-}
module Categories.Category.Construction.F-Coalgebras where

open import Level

open import Categories.Category
open import Categories.Functor hiding (id)
open import Categories.Functor.Coalgebra
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
    open Category C
    open MR C
    open HomReasoning
    open Equiv
    open Functor F
    open F-Coalgebra
    open F-Coalgebra-Morphism
    commut : {A B C : F-Coalgebra F} (α₁ : F-Coalgebra-Morphism B C) (α₂ : F-Coalgebra-Morphism A B) →
      F₁ (f α₁ ∘ f α₂) ∘ α A ≈ α C ∘ (f α₁ ∘ f α₂)
    commut {A} {B} {C} α₁ α₂ = begin
      F₁ (f α₁ ∘ f α₂) ∘ α A        ≈⟨ pushˡ homomorphism ⟩
      F₁ (f α₁) ∘ (F₁ (f α₂) ∘ α A) ≈⟨ pushʳ (commutes α₂) ⟩
      (F₁ (f α₁) ∘ α B) ∘ f α₂      ≈⟨ pushˡ (commutes α₁) ⟩      
      α C ∘ (f α₁ ∘ f α₂)           ∎
