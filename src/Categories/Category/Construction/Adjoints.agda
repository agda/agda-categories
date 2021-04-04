{-# OPTIONS --without-K --safe #-}

module Categories.Category.Construction.Adjoints where

open import Level
open import Data.Product using (_×_ ; _,_)

open import Categories.Category
open import Categories.Category.Helper
open import Categories.Adjoint
open import Categories.Adjoint.Compose
open import Categories.Adjoint.Mate
open import Categories.Functor renaming (id to idF)
open import Categories.NaturalTransformation renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism
open import Categories.NaturalTransformation.Equivalence renaming (_≃_ to _≊_)

import Categories.Morphism.Reasoning as MR

private
  variable
    o o′ ℓ ℓ′ e e′ : Level

-- category of adjunctions between two fixed categories
module _ (C : Category o ℓ e) (D : Category o′ ℓ′ e′) where
  private
    module C = Category C
    module D = Category D

  record AdjointObj : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
    field
      L   : Functor C D
      R   : Functor D C
      L⊣R : L ⊣ R

    module L = Functor L
    module R = Functor R
    module L⊣R = Adjoint L⊣R

  record Adjoint⇒ (X Y : AdjointObj) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
    private
      module X = AdjointObj X
      module Y = AdjointObj Y

    field
      mate : HaveMate X.L⊣R Y.L⊣R

    open HaveMate mate public

  private
    _≈_ : ∀ {A B} → Adjoint⇒ A B → Adjoint⇒ A B → Set (o ⊔ e ⊔ o′ ⊔ e′)
    f ≈ g = Adjoint⇒.α f ≊ Adjoint⇒.α g × Adjoint⇒.β f ≊ Adjoint⇒.β g

    id : {X : AdjointObj} → Adjoint⇒ X X
    id {X} = record
      { mate = record
        { α    = idN
        ; β    = idN
        ; mate = record
          { commute₁ = C.∘-resp-≈ˡ R.identity
          ; commute₂ = D.∘-resp-≈ʳ L.identity
          }
        }
      }
      where open AdjointObj X

    _∘_ : ∀ {X Y Z} → Adjoint⇒ Y Z → Adjoint⇒ X Y → Adjoint⇒ X Z
    _∘_ {X} {Y} {Z} f g = record
      { mate = record
        { α    = f.α ∘ᵥ g.α
        ; β    = g.β ∘ᵥ f.β
        ; mate = record
          { commute₁ = λ {W} →
            let open C.HomReasoning
                open MR C
            in begin
            X.R.F₁ (f.α.η W D.∘ g.α.η W) C.∘ X.L⊣R.unit.η W            ≈⟨ X.R.homomorphism ⟩∘⟨refl ⟩
            (X.R.F₁ (f.α.η W) C.∘ X.R.F₁ (g.α.η W)) C.∘ X.L⊣R.unit.η W ≈⟨ pullʳ g.commute₁ ⟩
            X.R.F₁ (f.α.η W) C.∘ g.β.η (Y.L.F₀ W) C.∘ Y.L⊣R.unit.η W   ≈⟨ pullˡ (g.β.sym-commute _) ⟩
            (g.β.η (Z.L.F₀ W) C.∘ Y.R.F₁ (f.α.η W)) C.∘ Y.L⊣R.unit.η W ≈⟨ pullʳ f.commute₁ ⟩
            g.β.η (Z.L.F₀ W) C.∘ f.β.η (Z.L.F₀ W) C.∘ Z.L⊣R.unit.η W   ≈⟨ C.sym-assoc ⟩
            (g.β.η (Z.L.F₀ W) C.∘ f.β.η (Z.L.F₀ W)) C.∘ Z.L⊣R.unit.η W ∎
          ; commute₂ = λ {W} →
            let open D.HomReasoning
                open MR D
            in begin
              X.L⊣R.counit.η W D.∘ X.L.F₁ (g.β.η W C.∘ f.β.η W)            ≈⟨ refl⟩∘⟨ X.L.homomorphism ⟩
              X.L⊣R.counit.η W D.∘ X.L.F₁ (g.β.η W) D.∘ X.L.F₁ (f.β.η W)   ≈⟨ pullˡ g.commute₂ ⟩
              (Y.L⊣R.counit.η W D.∘ g.α.η (Y.R.F₀ W)) D.∘ X.L.F₁ (f.β.η W) ≈⟨ pullʳ (g.α.commute _) ⟩
              Y.L⊣R.counit.η W D.∘ Y.L.F₁ (f.β.η W) D.∘ g.α.η (Z.R.F₀ W)   ≈⟨ pullˡ f.commute₂ ⟩
              (Z.L⊣R.counit.η W D.∘ f.α.η (Z.R.F₀ W)) D.∘ g.α.η (Z.R.F₀ W) ≈⟨ D.assoc ⟩
              Z.L⊣R.counit.η W D.∘ f.α.η (Z.R.F₀ W) D.∘ g.α.η (Z.R.F₀ W)   ∎
          }
        }
      }
      where module X = AdjointObj X
            module Y = AdjointObj Y
            module Z = AdjointObj Z
            module f = Adjoint⇒ f
            module g = Adjoint⇒ g

  Adjoints : Category (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) (o ⊔ e ⊔ o′ ⊔ e′)
  Adjoints = categoryHelper record
     { Obj       = AdjointObj
     ; _⇒_       = Adjoint⇒
     ; _≈_       = _≈_
     ; id        = id
     ; _∘_       = _∘_
     ; assoc     = D.assoc , C.sym-assoc
     ; identityˡ = D.identityˡ , C.identityʳ
     ; identityʳ = D.identityʳ , C.identityˡ
     ; equiv     = record
       { refl  = D.Equiv.refl , C.Equiv.refl
       ; sym   = λ { (eq₁ , eq₂) → D.Equiv.sym eq₁ , C.Equiv.sym eq₂ }
       ; trans = λ { (eq₁ , eq₂) (eq₃ , eq₄) → D.Equiv.trans eq₁ eq₃ , C.Equiv.trans eq₂ eq₄ }
       }
     ; ∘-resp-≈  = λ { (eq₁ , eq₂) (eq₃ , eq₄) → D.∘-resp-≈ eq₁ eq₃ , C.∘-resp-≈ eq₄ eq₂ }
     }


module _ o ℓ e where
  private
    _≈_ : ∀ {A B : Category o ℓ e} → AdjointObj A B → AdjointObj A B → Set (o ⊔ ℓ ⊔ e)
    f ≈ g = f.L ≃ g.L × f.R ≃ g.R
      where module f = AdjointObj f
            module g = AdjointObj g

    id : {A : Category o ℓ e} → AdjointObj A A
    id = record
      { L   = idF
      ; R   = idF
      ; L⊣R = ⊣-id
      }

    _∘_ : {A B C : Category o ℓ e} → AdjointObj B C → AdjointObj A B → AdjointObj A C
    f ∘ g = record
      { L   = f.L ∘F g.L
      ; R   = g.R ∘F f.R
      ; L⊣R = g.L⊣R ∘⊣ f.L⊣R
      }
      where module f = AdjointObj f
            module g = AdjointObj g

  Adjunctions : Category (suc (o ⊔ ℓ ⊔ e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
  Adjunctions = categoryHelper record
    { Obj       = Category o ℓ e
    ; _⇒_       = AdjointObj
    ; _≈_       = _≈_
    ; id        = id
    ; _∘_       = _∘_
    ; assoc     = λ {_ _ _ _ f g h} → associator (AdjointObj.L f) (AdjointObj.L g) (AdjointObj.L h)
                                    , sym-associator (AdjointObj.R h) (AdjointObj.R g) (AdjointObj.R f)
    ; identityˡ = unitorˡ , unitorʳ
    ; identityʳ = unitorʳ , unitorˡ
    ; equiv     = record
      { refl  = ≃.refl , ≃.refl
      ; sym   = λ { (α , β) → ≃.sym α , ≃.sym β }
      ; trans = λ { (α₁ , β₁) (α₂ , β₂) → ≃.trans α₁ α₂ , ≃.trans β₁ β₂ }
      }
    ; ∘-resp-≈  = λ { (α₁ , β₁) (α₂ , β₂) → α₁ ⓘₕ α₂ , β₂ ⓘₕ β₁ }
    }
