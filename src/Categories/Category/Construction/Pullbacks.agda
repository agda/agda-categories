{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Construction.Pullbacks {o ℓ e} (C : Category o ℓ e) where

open import Level using (_⊔_)
open import Function using (_$_)
open import Data.Product using (_×_; _,_)

open import Categories.Diagram.Pullback C
open import Categories.Morphism.Reasoning C

open Category C

record PullbackObj W : Set (o ⊔ ℓ ⊔ e) where
  field
    {A} {B}  : Obj
    arr₁     : A ⇒ W
    arr₂     : B ⇒ W
    pullback : Pullback arr₁ arr₂

  module pullback = Pullback pullback

open HomReasoning

record Pullback⇒ W (X Y : PullbackObj W) : Set (o ⊔ ℓ ⊔ e) where
  module X = PullbackObj X
  module Y = PullbackObj Y
  field
    mor₁     : X.A ⇒ Y.A
    mor₂     : X.B ⇒ Y.B
    commute₁ : Y.arr₁ ∘ mor₁ ≈ X.arr₁
    commute₂ : Y.arr₂ ∘ mor₂ ≈ X.arr₂

  pbarr : X.pullback.P ⇒ Y.pullback.P
  pbarr = Y.pullback.universal $ begin
    Y.arr₁ ∘ mor₁ ∘ X.pullback.p₁ ≈⟨ pullˡ commute₁ ⟩
    X.arr₁ ∘ X.pullback.p₁        ≈⟨ X.pullback.commute ⟩
    X.arr₂ ∘ X.pullback.p₂        ≈˘⟨ pullˡ commute₂ ⟩
    Y.arr₂ ∘ mor₂ ∘ X.pullback.p₂ ∎

open Pullback⇒

Pullbacks : Obj → Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
Pullbacks W = record
  { Obj       = PullbackObj W
  ; _⇒_       = Pullback⇒ W
  ; _≈_       = λ f g → mor₁ f ≈ mor₁ g × mor₂ f ≈ mor₂ g
  ; id        = record
    { mor₁     = id
    ; mor₂     = id
    ; commute₁ = identityʳ
    ; commute₂ = identityʳ
    }
  ; _∘_       = λ f g → record
    { mor₁     = mor₁ f ∘ mor₁ g
    ; mor₂     = mor₂ f ∘ mor₂ g
    ; commute₁ = pullˡ (commute₁ f) ○ commute₁ g
    ; commute₂ = pullˡ (commute₂ f) ○ commute₂ g
    }
  ; assoc     = assoc , assoc
  ; sym-assoc = sym-assoc , sym-assoc
  ; identityˡ = identityˡ , identityˡ
  ; identityʳ = identityʳ , identityʳ
  ; identity² = identity² , identity²
  ; equiv     = record
    { refl  = refl , refl
    ; sym   = λ { (eq₁ , eq₂) → sym eq₁ , sym eq₂ }
    ; trans = λ { (eq₁ , eq₂) (eq₃ , eq₄) → trans eq₁ eq₃ , trans eq₂ eq₄ }
    }
  ; ∘-resp-≈  = λ { (eq₁ , eq₂) (eq₃ , eq₄) → ∘-resp-≈ eq₁ eq₃ , ∘-resp-≈ eq₂ eq₄ }
  }
  where open Equiv
