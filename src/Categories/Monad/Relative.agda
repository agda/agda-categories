{-# OPTIONS --without-K --safe #-}
module Categories.Monad.Relative where

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

record Monad {C : Category o ℓ e} {D : Category o′ ℓ′ e′} (J : Functor C D) : Set (o ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private
    module C = Category C
    module D = Category D
    module J = Functor J
    open D using (_⇒_; _∘_; _≈_)
  field
    F₀ : C.Obj → D.Obj
    unit : {c : C.Obj} → J.₀ c ⇒ F₀ c
    extend : {x y : C.Obj} → (J.₀ x ⇒ F₀ y) → F₀ x ⇒ F₀ y
    identityʳ : {x y : C.Obj} { k : J.₀ x ⇒ F₀ y} → extend k ∘ unit ≈ k
    identityˡ : {x : C.Obj} → extend {x} unit ≈ D.id
    assoc : {x y z : C.Obj} {k : J.₀ x ⇒ F₀ y} {l : J.₀ y ⇒ F₀ z} → extend (extend l ∘ k) ≈ extend l ∘ extend k
    extend-≈ : {x y : C.Obj} {k h : J.₀ x ⇒ F₀ y} → k ≈ h → extend k ≈ extend h

-- From a Relative Monad, we can extract a functor
RMonad⇒Functor : {J : Functor C D} → Monad J → Functor C D
RMonad⇒Functor {C = C} {D = D} {J = J} r = record
  { F₀ = F₀
  ; F₁ = λ f → extend (unit ∘ J.₁ f)
  ; identity = identity′
  ; homomorphism = hom′
  ; F-resp-≈ = λ f≈g → extend-≈ (∘-resp-≈ʳ (J.F-resp-≈ f≈g))
  }
  where
  open Monad r
  module C = Category C
  module D = Category D
  module J = Functor J
  open Category D hiding (identityˡ; identityʳ; assoc)
  open HomReasoning
  open MR D
  identity′ : {c : C.Obj} → extend {c} (unit ∘ J.₁ C.id) ≈ id
  identity′ = begin
     extend (unit ∘ J.₁ C.id) ≈⟨ extend-≈ (elimʳ J.identity) ⟩
     extend unit              ≈⟨ identityˡ ⟩
     id                       ∎
  hom′ : {X Y Z : C.Obj} {f : X C.⇒ Y} {g : Y C.⇒ Z} →
      extend (unit ∘ J.₁ (g C.∘ f)) ≈ extend (unit ∘ J.₁ g) ∘ extend (unit ∘ J.F₁ f)
  hom′ {f = f} {g} = begin
    extend (unit ∘ J.₁ (g C.∘ f))                     ≈⟨ extend-≈ (pushʳ J.homomorphism) ⟩
    extend ((unit ∘ J.₁ g) ∘ J.₁ f)                   ≈⟨ extend-≈ (pushˡ (⟺ identityʳ)) ⟩
    extend (extend (unit ∘ J.₁ g) ∘ (unit ∘ J.F₁ f))  ≈⟨ assoc ⟩
    extend (unit ∘ J.₁ g) ∘ extend (unit ∘ J.F₁ f)    ∎
