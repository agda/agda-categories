{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Monad

module Categories.Category.Construction.EilenbergMoore {o ℓ e} {C : Category o ℓ e} (M : Monad C) where

open import Level

open import Categories.Morphism.Reasoning C

private
  module C = Category C
  module M = Monad M
  open C
  open M.F
  open HomReasoning

record Module : Set (o ⊔ ℓ ⊔ e) where
  field
    A        : Obj
    action   : F₀ A ⇒ A
    commute  : action ∘ F₁ action ≈ action ∘ M.μ.η A
    identity : action ∘ M.η.η A ≈ C.id

record Module⇒ (X Y : Module) : Set (ℓ ⊔ e) where
  private
    module X = Module X
    module Y = Module Y
  field
    arr     : X.A ⇒ Y.A
    commute : arr ∘ X.action ≈ Y.action ∘ F₁ arr

EilenbergMoore : Category (o ⊔ ℓ ⊔ e) (ℓ ⊔ e) e
EilenbergMoore = record
  { Obj       = Module
  ; _⇒_       = Module⇒
  ; _≈_       = λ f g → Module⇒.arr f ≈ Module⇒.arr g
  ; id        = record
    { arr     = C.id
    ; commute = id-comm-sym ○ ∘-resp-≈ʳ (⟺ identity)
    }
  ; _∘_       = compose
  ; assoc     = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv     = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  ; ∘-resp-≈  = ∘-resp-≈
  }
  where
    open Equiv
    compose : ∀ {X Y Z} → Module⇒ Y Z → Module⇒ X Y → Module⇒ X Z
    compose {X} {Y} {Z} f g = record
      { arr     = f.arr ∘ g.arr
      ; commute = begin
        (f.arr ∘ g.arr) ∘ Module.action X       ≈⟨ pullʳ g.commute ⟩
        f.arr ∘ Module.action Y ∘ F₁ g.arr      ≈⟨ pullˡ f.commute ⟩
        (Module.action Z ∘ F₁ f.arr) ∘ F₁ g.arr ≈˘⟨ pushʳ homomorphism ⟩
        Module.action Z ∘ F₁ (f.arr ∘ g.arr)    ∎
      }
      where module f = Module⇒ f
            module g = Module⇒ g
