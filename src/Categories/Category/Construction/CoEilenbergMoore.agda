{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Comonad

-- verbatim dual of Categories.Category.Construction.EilenbergMoore
module Categories.Category.Construction.CoEilenbergMoore {o ℓ e} {C : Category o ℓ e} (M : Comonad C) where

open import Level

open import Categories.Morphism.Reasoning C

private
  module C = Category C
  module M = Comonad M
  open C
  open M.F
  open HomReasoning
  open Equiv

-- helper for composition in diagrammatic order: bad idea?
_؛_ : {A B C : Obj} → (f : A ⇒ B) → (g : B ⇒ C) → (A ⇒ C)
f ؛ g = g ∘ f

record Comodule : Set (o ⊔ ℓ ⊔ e) where
  field
    A        : Obj
    coaction   : A ⇒ F₀ A
    commute  : F₁ coaction ∘ coaction ≈ M.δ.η A ∘ coaction
    identity : M.ε.η A ∘ coaction ≈ C.id

record Comodule⇒ (X Y : Comodule) : Set (ℓ ⊔ e) where
  private
    module X = Comodule X
    module Y = Comodule Y
  field
    arr     : X.A ⇒ Y.A
    commute : Y.coaction ∘ arr ≈ F₁ arr ∘ X.coaction

CoEilenbergMoore : Category (o ⊔ ℓ ⊔ e) (ℓ ⊔ e) e
CoEilenbergMoore =
 record
  { Obj = Comodule
  ; _⇒_ = Comodule⇒
  ; _≈_ = λ f g → Comodule⇒.arr f ≈ Comodule⇒.arr g
  ; id = record { arr = C.id ; commute = identityʳ ○ introˡ identity }
  ; _∘_ = compose
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = record { refl = refl ; sym = sym ; trans = trans }
  ; ∘-resp-≈ = ∘-resp-≈
  }
  where
   open Equiv
   compose : ∀ {X Y Z} → Comodule⇒ Y Z → Comodule⇒ X Y → Comodule⇒ X Z
   compose {X} {Y} {Z} f g = record
    { arr     = f.arr ∘ g.arr
    ; commute = begin
       Comodule.coaction Z ∘ f.arr ∘ g.arr       ≈⟨ pullˡ f.commute ⟩
       (F₁ f.arr ∘ Comodule.coaction Y) ∘ g.arr  ≈⟨ pullʳ g.commute ⟩
       F₁ f.arr ∘ F₁ g.arr ∘ Comodule.coaction X ≈⟨ pullˡ (sym homomorphism) ⟩
       F₁ (f.arr ∘ g.arr) ∘ Comodule.coaction X  ∎
    }
    where module f = Comodule⇒ f
          module g = Comodule⇒ g
