{-# OPTIONS --without-K --safe #-}
module Categories.Comonad.Relative where

open import Level

open import Categories.Category using (Category)
open import Categories.Functor using (Functor; Endofunctor; _∘F_) renaming (id to idF)
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (_≃_)
open import Categories.NaturalTransformation.Equivalence
open NaturalIsomorphism

private
  variable
    o ℓ e o′ ℓ′ e′ : Level
    C : Category o ℓ e
    D : Category o′ ℓ′ e′

record Comonad {C : Category o ℓ e} {D : Category o′ ℓ′ e′} (J : Functor C D) : Set (o ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private
    module C = Category C
    module D = Category D
    module J = Functor J
    open D using (_⇒_; _∘_; _≈_)
  field
    F₀ : C.Obj → D.Obj
    counit : {c : C.Obj} → F₀ c ⇒ J.₀ c
    cobind : {x y : C.Obj} → (F₀ x ⇒ J.₀ y) → F₀ x ⇒ F₀ y
    identityʳ : {x y : C.Obj} { k : F₀ x ⇒ J.₀ y} → counit ∘ cobind k ≈ k
    identityˡ : {x : C.Obj} → cobind {x} counit ≈ D.id
    assoc : {x y z : C.Obj} {k : F₀ x ⇒ J.₀ y} {l : F₀ y ⇒ J.₀ z} →
      cobind (l ∘ cobind k) ≈ cobind l ∘ cobind k
    cobind-≈ : {x y : C.Obj} {k h : F₀ x ⇒ J.₀ y} → k ≈ h → cobind k ≈ cobind h

-- From a Relative Comonad, we can extract a functor
RComonad⇒Functor : {J : Functor C D} → Comonad J → Functor C D
RComonad⇒Functor {C = C} {D = D} {J = J} r = record
  { F₀ = F₀
  ; F₁ = λ f → cobind (J.₁ f ∘ counit)
  ; identity = identity′
  ; homomorphism = hom′
  ; F-resp-≈ = λ f≈g → cobind-≈ (∘-resp-≈ˡ (J.F-resp-≈ f≈g))
  }
  where
  open Comonad r
  module C = Category C
  module D = Category D
  module J = Functor J
  open Category D hiding (identityˡ; identityʳ; assoc)
  open HomReasoning
  open MR D
  identity′ : {c : C.Obj} → cobind {c} (J.₁ C.id ∘ counit) ≈ id
  identity′ = begin
     cobind (J.₁ C.id ∘ counit) ≈⟨ cobind-≈ (elimˡ J.identity) ⟩
     cobind counit              ≈⟨ identityˡ ⟩
     id                         ∎
  hom′ : {X Y Z : C.Obj} {f : X C.⇒ Y} {g : Y C.⇒ Z} →
      cobind (J.₁ (g C.∘ f) ∘ counit) ≈ cobind (J.₁ g ∘ counit) ∘ cobind (J.₁ f ∘ counit)
  hom′ {f = f} {g} = begin
    cobind (J.₁ (g C.∘ f) ∘ counit)                         ≈⟨ cobind-≈ (pushˡ J.homomorphism) ⟩
    cobind (J.₁ g ∘ J.₁ f ∘ counit)                         ≈⟨ cobind-≈ (pushʳ (⟺ identityʳ)) ⟩
    cobind ((J.₁ g ∘ counit) ∘ (cobind (J.F₁ f ∘ counit)))  ≈⟨ assoc ⟩
    cobind (J.₁ g ∘ counit) ∘ cobind (J.F₁ f ∘ counit)      ∎
