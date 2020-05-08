{-# OPTIONS --without-K --safe #-}

module Categories.Category.Construction.Graphs where

-- The "Underlying Graph" <-> "Free Category on a Graph" Adjunction.
-- Lots of surprises here, of various level of surprisingness
-- 1. The Free Category rises universe levels of arrows (and equivalences); the Underlying Graph does not
--   (due to the Transitive Closure "Star" construction)
-- 2. As a consequence of (1), the eventual Adjunction will be for all Levels being the same
-- 3. If you want a Functor Categories Graph, then the object/hom levels are straightforward,
--   but if you use "Categories" with NaturalIsomorphism, then the 2-point Groupoid is contractible
--   (thus equivalent to the 1-point Category), and yet those two Graphs shouldn't be considered to
--   be the same!  So _≡F_ must be used so that we have no wiggle room when mapping Graphs around.
--   Interestingly, this only shows up when trying to prove that the Underlying Functor respects
--   _≈_, which is not traditionally a requirement of a Functor! This requirement is usually left
--   implicit.  If we were to allow Functor to not respect _≈_, things would be fine. But of course
--   we couldn't do any reasonable equational reasoning anymore.  Of course, if _≈_ were the global
--   _≡_, this isn't an issue, but that is definitely not wanted here.
-- 4. A lot of weird little lemmas about _≡_ and subst/transport are needed, because we're in a mixed
--   reasoning situation with both ≡ and ≈ present.  These could probably be generalized and factored
--   into a separate module (or into the standard library).

open import Level
open import Function using (_$_; flip) renaming (id to idFun; _∘_ to _⊚_)
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as EqR
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties hiding (trans)
open import Data.Product using (proj₁; proj₂; _,_)

open import Categories.Category
open import Categories.Functor using (Functor)
open import Categories.Functor.Equivalence
open import Categories.Category.Instance.StrictCats
open import Categories.Utils.EqReasoning
open import Categories.NaturalTransformation hiding (id)
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (refl; sym; trans; isEquivalence)
open import Categories.Adjoint
import Categories.Morphism.HeterogeneousIdentity as HId

-- a graph has vertices Obj and edges _⇒_, where edges form a setoid over _≈_.
record Graph o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  infix 4 _≈_ _⇒_

  field
    Obj   : Set o
    _⇒_   : Rel Obj ℓ
    _≈_   : ∀ {A B} → Rel (A ⇒ B) e
    equiv : ∀ {A B} → IsEquivalence (_≈_ {A} {B})

  setoid : {A B : Obj} → Setoid _ _
  setoid {A} {B} = record
    { Carrier       = A ⇒ B
    ; _≈_           = _≈_
    ; isEquivalence = equiv
    }

  module Equiv {A} {B} = IsEquivalence (equiv {A} {B})
  module EdgeReasoning {A B : Obj} = EqR (setoid {A} {B})

private
  variable
    o o′ ℓ ℓ′ e e′ : Level

-- This doesn't belong here... but will do for now
module PathEquiv {o ℓ e : Level} {Obj : Set o} {_⇒_ : Obj → Obj → Set ℓ} (_≈_ : {A B : Obj} → Rel (A ⇒ B) e)
  (equiv : {A B : Obj} → IsEquivalence ( _≈_ {A} {B})) where

  private
    module E {A} {B} = IsEquivalence (equiv {A} {B})

  open E renaming (refl to ≈refl; sym to ≈sym; trans to ≈trans)

  infix 4 _≈*_
  data _≈*_ : {A B : Obj} (p q : Star _⇒_ A B) → Set (o ⊔ ℓ ⊔ e) where
      ε : {A : Obj} → _≈*_ {A} ε ε
      _◅_ : {A B C : Obj} {x y : A ⇒ B} {p q : Star _⇒_ B C} (x≈y : x ≈ y) (p≈q : p ≈* q) → x ◅ p ≈* y ◅ q

  refl : {A B : Obj} {p : Star _⇒_ A B} → p ≈* p
  refl {p = ε} = ε
  refl {p = x ◅ p} = ≈refl ◅ refl

  sym : {A B : Obj} {p q : Star _⇒_ A B} → p ≈* q → q ≈* p
  sym ε = ε
  sym (x≈y ◅ eq) = ≈sym x≈y ◅ sym eq

  ≡⇒≈* : {A B : Obj} {p q : Star _⇒_ A B} → p ≡ q → p ≈* q
  ≡⇒≈* ≡.refl = refl

  ≡⇒≈ : {A B : Obj} → {p q : A ⇒ B} → p ≡ q → p ≈ q
  ≡⇒≈ ≡.refl = ≈refl

  trans : {A B : Obj} {p q r : Star _⇒_ A B} → p ≈* q → q ≈* r → p ≈* r
  trans ε ε = ε
  trans (x≈y ◅ ss) (y≈z ◅ tt) = ≈trans x≈y y≈z ◅ trans ss tt

  isEquivalence : {A B : Obj} → IsEquivalence (λ (p q : Star _⇒_ A B) → p ≈* q)
  isEquivalence = record { refl = refl ; sym = sym ; trans = trans }

  setoid : Obj → Obj → Setoid (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)
  setoid A B = record { _≈_ = _≈*_ ; isEquivalence = isEquivalence {A} {B} }

  -- convenient to define here
  --
  -- FIXME: this should go into the standard library at
  -- Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties
  ◅◅-identityʳ : {A B : Obj} → (f : Star _⇒_ A B) → f ◅◅ ε ≈* f
  ◅◅-identityʳ ε = ε
  ◅◅-identityʳ (x ◅ f) = ≈refl ◅ ◅◅-identityʳ f

  module PathEqualityReasoning {A B} where
    open EqR (setoid A B) public

module _ (G : Graph o ℓ e) where
  open Graph G
  private module P = PathEquiv {o} {ℓ} {e} {Obj} {_⇒_} _≈_ equiv
  open P

  Free : Category o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)
  Free = record
    { Obj       = Obj
    ; _⇒_       = Star _⇒_
    ; _≈_       = _≈*_
    ; id        = ε
    ; _∘_       = _▻▻_
    ; assoc     = λ {_ _ _ _} {f g h} → sym $ ≡⇒≈* $ ◅◅-assoc f g h
    ; sym-assoc = λ {_ _ _ _} {f g h} → ≡⇒≈* $ ◅◅-assoc f g h
    ; identityˡ = λ {_ _ f} → ◅◅-identityʳ f
    ; identityʳ = refl
    ; identity² = refl
    ; equiv     = isEquivalence
    ; ∘-resp-≈  = resp
    }
    where resp : ∀ {A B C} {f h : Star _⇒_ B C} {g i : Star _⇒_ A B} →
                   f ≈* h → g ≈* i → (f ▻▻ g) ≈* (h ▻▻ i)
          resp eq ε = eq
          resp eq (eq₁ ◅ eq₂) = eq₁ ◅ (resp eq eq₂)

  open P public renaming (_≈*_ to [_]_≈*_)

record GraphMorphism (G : Graph o ℓ e) (G′ : Graph o′ ℓ′ e′) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private
    module G  = Graph G
    module G′ = Graph G′

  field
    M₀       : G.Obj → G′.Obj
    M₁       : ∀ {A B} → A G.⇒ B → M₀ A G′.⇒ M₀ B
    M-resp-≈ : ∀ {A B} {f g : A G.⇒ B} → f G.≈ g → M₁ f G′.≈ M₁ g

idGHom : {G : Graph o ℓ e} → GraphMorphism G G
idGHom = record { M₀ = idFun ; M₁ = idFun ; M-resp-≈ = idFun }

_∘GM_ : {G₁ G₂ G₃ : Graph o ℓ e} (m₁ : GraphMorphism G₂ G₃) (m₂ : GraphMorphism G₁ G₂) → GraphMorphism G₁ G₃
m₁ ∘GM m₂ = record
  { M₀ = M₀ m₁ ⊚ M₀ m₂
  ; M₁ = M₁ m₁ ⊚ M₁ m₂
  ; M-resp-≈ = M-resp-≈ m₁ ⊚ M-resp-≈ m₂
  }
  where open GraphMorphism

module Trsp (G : Graph o ℓ e) where
  open Graph G

  -- Two shorthands that will be useful for the definition of morphism
  -- equality: transport the domain or codomain of an edge along an
  -- equality.

  infixr 9 _◂_
  infixl 9 _▸_

  _◂_ : ∀ {A B C} → A ≡ B → B ⇒ C → A ⇒ C
  p ◂ f = ≡.subst (_⇒ _) (≡.sym p) f

  _▸_ : ∀ {A B C} → A ⇒ B → B ≡ C → A ⇒ C
  f ▸ p = ≡.subst (_ ⇒_) p f

  -- Some simple properties of transports

  ◂-▸-comm : ∀ {A B C D} (p : A ≡ B) (f : B ⇒ C) (q : C ≡ D) →
             p ◂ (f ▸ q) ≡ (p ◂ f) ▸ q
  ◂-▸-comm ≡.refl f ≡.refl = ≡.refl

  ◂-trans : ∀ {A B C D} (p : A ≡ B) (q : B ≡ C) (f : C ⇒ D) →
            p ◂ q ◂ f ≡ (≡.trans p q) ◂ f
  ◂-trans ≡.refl ≡.refl f = ≡.refl

  ▸-trans : ∀ {A B C D} (f : A ⇒ B) (p : B ≡ C) (q : C ≡ D) →
            f ▸ p ▸ q ≡ f ▸ ≡.trans p q
  ▸-trans f ≡.refl ≡.refl = ≡.refl

  ◂-resp-≈ : ∀ {A B C} (p : A ≡ B) {f g : B ⇒ C} → f ≈ g → p ◂ f ≈ p ◂ g
  ◂-resp-≈ ≡.refl f≈g = f≈g

  ▸-resp-≈ : ∀ {A B C} {f g : A ⇒ B} → f ≈ g → (p : B ≡ C) → f ▸ p ≈ g ▸ p
  ▸-resp-≈ f≈g ≡.refl = f≈g

module TrspGM {G : Graph o ℓ e} {H : Graph o′ ℓ′ e′}
              (m : GraphMorphism G H) where
  module G = Graph G
  module H = Graph H
  open GraphMorphism m
  open Trsp G
  open Trsp H using () renaming (_◂_ to _◃_; _▸_ to _▹_)

  M-resp-▸ : ∀ {A B C} (f : A G.⇒ B) (p : B ≡ C) →
             M₁ (f ▸ p) ≡ M₁ f ▹ ≡.cong M₀ p
  M-resp-▸ f ≡.refl = ≡.refl

  M-resp-◂ : ∀ {A B C} (p : A ≡ B) (f : B G.⇒ C) →
             M₁ (p ◂ f) ≡ ≡.cong M₀ p ◃ M₁ f
  M-resp-◂ ≡.refl f = ≡.refl

record GraphMorphism≈ {G : Graph o ℓ e} {G′ : Graph o′ ℓ′ e′}
                      (M M′ : GraphMorphism G G′) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private
    module G  = Graph G
    module G′ = Graph G′
    module M  = GraphMorphism M
    module M′ = GraphMorphism M′
  open Trsp G′

  -- Pick a presentation of equivalence for graph morphisms that works
  -- well with functor equality.

  field
    M₀≡ : ∀ {X} → M.M₀ X ≡ M′.M₀ X
    M₁≡ : ∀ {A B} {f : A G.⇒ B} → M.M₁ f ▸ M₀≡ G′.≈ M₀≡ ◂ M′.M₁ f

Graphs : ∀ o ℓ e → Category (suc (o ⊔ ℓ ⊔ e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
Graphs o ℓ e = record
  { Obj       = Graph o ℓ e
  ; _⇒_       = GraphMorphism
  ; _≈_       = GraphMorphism≈
  ; id        = idGHom
  ; _∘_       = _∘GM_
  ; assoc     = λ {_ _ _ G} → record { M₀≡ = ≡.refl ; M₁≡ = Equiv.refl G }
  ; sym-assoc = λ {_ _ _ G} → record { M₀≡ = ≡.refl ; M₁≡ = Equiv.refl G }
  ; identityˡ = λ {_ G}     → record { M₀≡ = ≡.refl ; M₁≡ = Equiv.refl G }
  ; identityʳ = λ {_ G}     → record { M₀≡ = ≡.refl ; M₁≡ = Equiv.refl G }
  ; identity² = λ {G}       → record { M₀≡ = ≡.refl ; M₁≡ = Equiv.refl G }
  ; equiv     = λ {_ G} → record
    { refl  = record { M₀≡ = ≡.refl ; M₁≡ = Equiv.refl G }
    ; sym   = λ {i j} eq → record
      { M₀≡ = ≡.sym (M₀≡ eq)
      ; M₁≡ = λ {_ _ f} →
        let open EdgeReasoning G
            open Trsp G
        in begin
          M₁ j f ▸ ≡.sym (M₀≡ eq)
        ≡˘⟨ ≡.cong (_◂ (M₁ j f ▸ _)) (≡.trans-symˡ (M₀≡ eq)) ⟩
          ≡.trans (≡.sym $ M₀≡ eq) (M₀≡ eq) ◂ (M₁ j f ▸ ≡.sym (M₀≡ eq))
        ≡˘⟨ ◂-trans (≡.sym $ M₀≡ eq) (M₀≡ eq) _ ⟩
          ≡.sym (M₀≡ eq) ◂ M₀≡ eq ◂ (M₁ j f ▸ ≡.sym (M₀≡ eq))
        ≡⟨ ≡.cong (≡.sym (M₀≡ eq) ◂_)
                  (◂-▸-comm (M₀≡ eq) (M₁ j f) (≡.sym $ M₀≡ eq)) ⟩
          ≡.sym (M₀≡ eq) ◂ ((M₀≡ eq ◂ M₁ j f) ▸ ≡.sym (M₀≡ eq))
        ≈˘⟨ ◂-resp-≈ (≡.sym (M₀≡ eq)) (▸-resp-≈ (M₁≡ eq) (≡.sym (M₀≡ eq))) ⟩
          ≡.sym (M₀≡ eq) ◂ (M₁ i f ▸ M₀≡ eq ▸ ≡.sym (M₀≡ eq))
        ≡⟨ ≡.cong (≡.sym (M₀≡ eq) ◂_)
                  (▸-trans (M₁ i f) (M₀≡ eq) (≡.sym (M₀≡ eq))) ⟩
          ≡.sym (M₀≡ eq) ◂ (M₁ i f ▸ ≡.trans (M₀≡ eq) (≡.sym (M₀≡ eq)))
        ≡⟨ ≡.cong (λ p → ≡.sym (M₀≡ eq) ◂ (M₁ i f ▸ p)) (≡.trans-symʳ (M₀≡ eq)) ⟩
          ≡.sym (M₀≡ eq) ◂ M₁ i f
        ∎
      }
    ; trans = λ {i j k} eq eq′ → record
      { M₀≡ = ≡.trans (M₀≡ eq) (M₀≡ eq′)
      ; M₁≡ = λ {_ _ f} →
        let open EdgeReasoning G
            open Trsp G
        in begin
          M₁ i f ▸ ≡.trans (M₀≡ eq) (M₀≡ eq′)
        ≡˘⟨ ▸-trans (M₁ i f) (M₀≡ eq) (M₀≡ eq′) ⟩
          (M₁ i f ▸ M₀≡ eq) ▸ M₀≡ eq′
        ≈⟨ ▸-resp-≈ (M₁≡ eq) (M₀≡ eq′) ⟩
          (M₀≡ eq ◂ M₁ j f) ▸ M₀≡ eq′
        ≡˘⟨ ◂-▸-comm (M₀≡ eq) (M₁ j f) (M₀≡ eq′) ⟩
          M₀≡ eq ◂ (M₁ j f ▸ M₀≡ eq′)
        ≈⟨ ◂-resp-≈ (M₀≡ eq) (M₁≡ eq′) ⟩
          M₀≡ eq ◂ (M₀≡ eq′ ◂ M₁ k f)
        ≡⟨ ◂-trans (M₀≡ eq) (M₀≡ eq′) (M₁ k f) ⟩
          ≡.trans (M₀≡ eq) (M₀≡ eq′) ◂ M₁ k f
        ∎
      }
    }
  ; ∘-resp-≈  = λ {_ G H} {f g h i} eq eq′ → record
    { M₀≡ = ≡.trans (≡.cong (M₀ f) (M₀≡ eq′)) (M₀≡ eq)
    ; M₁≡ = λ {_ _ j} →
      let open EdgeReasoning H
          open Trsp H
          open Trsp G using () renaming (_▸_ to _▹_; _◂_ to _◃_)
          open TrspGM
      in begin
        M₁ (f ∘GM h) j ▸ ≡.trans (≡.cong (M₀ f) (M₀≡ eq′)) (M₀≡ eq)
      ≡˘⟨ ▸-trans (M₁ f (M₁ h j)) (≡.cong (M₀ f) (M₀≡ eq′)) (M₀≡ eq) ⟩
        M₁ f (M₁ h j) ▸ ≡.cong (M₀ f) (M₀≡ eq′) ▸ M₀≡ eq
      ≡˘⟨ ≡.cong (_▸ M₀≡ eq) (M-resp-▸ f (M₁ h j) (M₀≡ eq′)) ⟩
        M₁ f (M₁ h j ▹ M₀≡ eq′) ▸ M₀≡ eq
      ≈⟨ M₁≡ eq ⟩
        M₀≡ eq ◂ M₁ g (M₁ h j ▹ M₀≡ eq′)
      ≈⟨ ◂-resp-≈ (M₀≡ eq) (M-resp-≈ g (M₁≡ eq′)) ⟩
        M₀≡ eq ◂ M₁ g (M₀≡ eq′ ◃ M₁ i j)
      ≡⟨ ≡.cong (M₀≡ eq ◂_) (M-resp-◂ g (M₀≡ eq′) (M₁ i j)) ⟩
        M₀≡ eq ◂ ≡.cong (M₀ g) (M₀≡ eq′) ◂ M₁ g (M₁ i j)
      ≡⟨ ◂-trans (M₀≡ eq) (≡.cong (M₀ g) (M₀≡ eq′)) (M₁ g (M₁ i j)) ⟩
        ≡.trans (M₀≡ eq) (≡.cong (M₀ g) (M₀≡ eq′)) ◂ M₁ g (M₁ i j)
      ≡˘⟨ ≡.cong (_◂ M₁ g (M₁ i j)) (≡.naturality (λ _ → M₀≡ eq)) ⟩
        ≡.trans (≡.cong (M₀ f) (M₀≡ eq′)) (M₀≡ eq) ◂ M₁ g (M₁ i j)
      ∎
    }
  }
  where
    open Graph
    open GraphMorphism
    open GraphMorphism≈

open _≡F_

-- Put the rest of the Graph stuff here too:
Underlying₀ : Category o ℓ e → Graph o ℓ e
Underlying₀ C = record { Obj = C.Obj ; _⇒_ = C._⇒_ ; _≈_ = C._≈_ ; equiv = C.equiv }
  where module C = Category C

Underlying₁ : {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → Functor C D → GraphMorphism (Underlying₀ C) (Underlying₀ D)
Underlying₁ F = record { M₀ = F.F₀ ; M₁ = F.F₁ ; M-resp-≈ = F.F-resp-≈ }
  where module F = Functor F

Underlying : Functor (Cats o ℓ e) (Graphs o ℓ e)
Underlying = record
  { F₀ = Underlying₀
  ; F₁ = Underlying₁
  ; identity = λ {A} → record { M₀≡ = ≡.refl ; M₁≡ = Category.Equiv.refl A }
  ; homomorphism = λ where {Z = Z} → record { M₀≡ = ≡.refl ; M₁≡ = Category.Equiv.refl Z }
  ; F-resp-≈ = λ {A} {B} {F} {G} F≈G → record
    { M₀≡ = λ {X} → eq₀ F≈G X
    ; M₁≡ = λ {x} {y} {f} →
      let open Category B
          open HId B
          open Trsp (Underlying₀ B)
          open Functor
          open Graph.EdgeReasoning (Underlying₀ B)
      in begin
        F₁ F f ▸ eq₀ F≈G y         ≈⟨ hid-subst-cod (F₁ F f) (eq₀ F≈G y) ⟩
        hid (eq₀ F≈G y) ∘ F₁ F f   ≈⟨ eq₁ F≈G f ⟩
        F₁ G f ∘ hid (eq₀ F≈G x)   ≈˘⟨ hid-subst-dom (eq₀ F≈G x) (F₁ G f) ⟩
        eq₀ F≈G x ◂ F₁ G f         ∎
    }
  }
  where
  open NaturalTransformation
  open NaturalIsomorphism

-- Transports on paths

module TrspStar (G : Graph o ℓ e) where
  open Graph G
  open Trsp (Underlying₀ (Free G)) public using () renaming
    ( _◂_ to _◂*_
    ; _▸_ to _▸*_
    )
  open Trsp G

  -- Lemmas relating transports to path operations.

  ◂*-▸*-ε : ∀ {A B : Obj} (p : A ≡ B) → ε ▸* p ≡ p ◂* ε
  ◂*-▸*-ε ≡.refl = ≡.refl

  ◂*-◅ : ∀ {A B C D : Obj} (p : A ≡ B) (f : B ⇒ C) (fs : Star _⇒_ C D) →
         p ◂* (f ◅ fs) ≡ (p ◂ f) ◅ fs
  ◂*-◅ ≡.refl f fs = ≡.refl

  ◅-▸* : ∀ {A B C D : Obj} (f : A ⇒ B) (fs : Star _⇒_ B C) (p : C ≡ D) →
         (f ◅ fs) ▸* p ≡ f ◅ (fs ▸* p)
  ◅-▸* f fs ≡.refl = ≡.refl

  ◅-◂*-▸ : ∀ {A B C D : Obj} (f : A ⇒ B) (p : B ≡ C) (fs : Star _⇒_ C D) →
           _≡_ {_} {Star _⇒_ A D} (f ◅ (p ◂* fs)) ((f ▸ p) ◅ fs)
  ◅-◂*-▸ f ≡.refl fs = ≡.refl

-- define these ahead of time
module _ {G₁ G₂ : Graph o ℓ e} (G⇒ : GraphMorphism G₁ G₂) where
  open Graph G₁ renaming (_⇒_ to _⇒₁_; Obj to Obj₁)
  open Graph G₂ renaming (_⇒_ to _⇒₂_; Obj to Obj₂; module Equiv to Equiv₂)
  open GraphMorphism G⇒

  mapGraph : {A B : Obj₁} → Star _⇒₁_ A B → Star _⇒₂_ (M₀ A) (M₀ B)
  mapGraph ε = ε
  mapGraph (x ◅ y) = M₁ x ◅ mapGraph y

  map-hom : {X Y Z : Graph.Obj G₁} (f : Star _⇒₁_ X Y) {g : Star _⇒₁_ Y Z} →
      [ G₂ ] mapGraph (f ◅◅ g) ≈* (mapGraph f ◅◅ mapGraph g)
  map-hom ε {g} = refl G₂
  map-hom (x ◅ f) {g} = Equiv₂.refl ◅ map-hom f

  map-resp : {A B : Obj₁} (f : Star _⇒₁_ A B) {g : Star _⇒₁_ A B} →
      [ G₁ ] f ≈* g → [ G₂ ] mapGraph f ≈* mapGraph g
  map-resp ε ε = ε
  map-resp (x ◅ f) (f≈* ◅ eq) = M-resp-≈ f≈* ◅ map-resp f eq

-- don't want a single global GraphMorphism
module _ {G : Graph o ℓ e} where
  open Graph G

  map-id : {A B : Obj} (f : Star _⇒_ A B) → [ G ] mapGraph (idGHom {G = G}) f ≈* f
  map-id ε        = ε
  map-id (fs ◅ f) = Equiv.refl ◅ map-id f

module _ {X Y Z : Graph o ℓ e} {G₁ : GraphMorphism X Y} {G₂ : GraphMorphism Y Z} where
  open Graph X

  map-∘ : {A B : Obj} (f : Star _⇒_ A B) → [ Z ] (mapGraph (G₂ ∘GM G₁) f) ≈* mapGraph G₂ (mapGraph G₁ f)
  map-∘ ε        = ε
  map-∘ (fs ◅ f) = Graph.Equiv.refl Z ◅ map-∘ f

module _ {G H : Graph o ℓ e} {f g : GraphMorphism G H}
         (f≈g : GraphMorphism≈ f g) where
  open Graph G
  open GraphMorphism
  open GraphMorphism≈ f≈g
  open TrspStar H
  open Trsp H

  map-M₁≡ : {A B : Obj} (hs : Star _⇒_ A B) →
            [ H ] mapGraph f hs ▸* M₀≡ ≈* M₀≡ ◂* mapGraph g hs
  map-M₁≡ ε        = ≡⇒≈* H (◂*-▸*-ε M₀≡)
  map-M₁≡ (hs ◅ h) = begin
    (M₁ f hs ◅ mapGraph f h) ▸* M₀≡   ≡⟨ ◅-▸* (M₁ f hs) _ M₀≡ ⟩
    M₁ f hs ◅ (mapGraph f h ▸* M₀≡)   ≈⟨ Graph.Equiv.refl H ◅ map-M₁≡ h ⟩
    M₁ f hs ◅ (M₀≡ ◂* mapGraph g h)   ≡⟨ ◅-◂*-▸ (M₁ f hs) M₀≡ _ ⟩
    (M₁ f hs ▸ M₀≡) ◅ mapGraph g h    ≈⟨ M₁≡ ◅ (refl H) ⟩
    (M₀≡ ◂ M₁ g hs) ◅ mapGraph g h    ≡˘⟨ ◂*-◅ M₀≡ (M₁ g hs) _ ⟩
    M₀≡ ◂* (M₁ g hs ◅ mapGraph g h)   ∎
    where open PathEqualityReasoning H

module _ (C : Category o ℓ e) where
  open Category C
  open Definitions C
  open HomReasoning

  -- A helper that should probably go into Categories.Morphism.Reasoning...

  toSquare : ∀ {A B} {f g : A ⇒ B} → f ≈ g → CommutativeSquare f id id g
  toSquare {_} {_} {f} {g} f≈g = begin
        id ∘ f   ≈⟨ identityˡ ⟩
        f        ≈⟨ f≈g ⟩
        g        ≈˘⟨ identityʳ ⟩
        g ∘ id   ∎

CatF : Functor (Graphs o ℓ e) (Cats o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e))
CatF = record
  { F₀ = Free
  ; F₁ = λ {G₁} {G₂} G⇒ → record
    { F₀ = M₀ G⇒
    ; F₁ = mapGraph G⇒
    ; identity = refl G₂
    ; homomorphism = λ {_} {_} {_} {f} → map-hom G⇒ f
    ; F-resp-≈ = λ { {f = f} → map-resp G⇒ f}
    }
  ; identity = λ {G} → record
    { eq₀ = λ _ → ≡.refl
    ; eq₁ = λ f → toSquare (Free G) (map-id f)
    }
  ; homomorphism = λ {_} {_} {G} → record
    { eq₀ = λ _ → ≡.refl
    ; eq₁ = λ h → toSquare (Free G) (map-∘ h)
    }
  ; F-resp-≈ = λ {_} {G} {f} {g} f≈g → record
    { eq₀ = λ _ → M₀≡ f≈g
    ; eq₁ = λ h →
      let open Category (Free G)
          open HId      (Free G)
          open TrspStar G
          open HomReasoning
      in begin
        mapGraph f h ◅◅ (hid $ M₀≡ f≈g)
      ≈˘⟨ hid-subst-cod (mapGraph f h) (M₀≡ f≈g) ⟩
        mapGraph f h ▸* M₀≡ f≈g
      ≈⟨ map-M₁≡ f≈g h ⟩
        M₀≡ f≈g ◂* mapGraph g h
      ≈⟨ hid-subst-dom (M₀≡ f≈g) (mapGraph g h) ⟩
        (hid $ M₀≡ f≈g) ◅◅ mapGraph g h
      ∎
    }
  }
  where
  open GraphMorphism
  open GraphMorphism≈

-- Because of the Level changes in CatF, sizes must all be same:
CatF-is-Free : (o ℓ e : Level) → Adjoint (CatF {o} {o ⊔ ℓ} {o ⊔ ℓ ⊔ e}) (Underlying)
CatF-is-Free o ℓ e = record
  { unit = ntHelper record
    { η = GM
    ; commute = λ {X} {Y} f → record { M₀≡ = ≡.refl ; M₁≡ = Graph.Equiv.refl Y ◅ ε }
    }
  ; counit = ntHelper record
    { η = λ X → record
      { F₀ = idFun
      ; F₁ = unwind X
      ; identity = Category.Equiv.refl X
      ; homomorphism = λ { {f = f} {g} → unwind-◅◅ X {f = f} {g} }
      ; F-resp-≈ = unwind-resp-≈ X
      }
    ; commute = λ {_} {Y} F → record
      { eq₀ = λ _ → ≡.refl
      ; eq₁ = λ f → toSquare Y (comm F f)
      }
    }
  ; zig = λ {G} → record
    { eq₀ = λ _ → ≡.refl
    ; eq₁ = λ f → toSquare (Free G) (zig′ G f)
    }
  ; zag = λ {B} → record { M₀≡ = ≡.refl ; M₁≡ = Category.identityˡ B  }
  }
  where
  GM : (X : Graph o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)) → GraphMorphism X (Underlying₀ (Free X))
  GM _ = record { M₀ = idFun ; M₁ = return ; M-resp-≈ = λ f≈g → f≈g ◅ ε }
  module _ (X : Category o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)) where
    open Category X
    open HomReasoning
    unwind : {A B : Obj} → Star _⇒_ A B → A ⇒ B
    unwind = fold _⇒_ (flip _∘_) id
    unwind-◅◅ : {A B C : Obj} {f : Star _⇒_ A B} {g : Star _⇒_ B C} →
                unwind (f ◅◅ g) ≈ (unwind g) ∘ (unwind f)
    unwind-◅◅ {f = ε} {g} = Equiv.sym identityʳ
    unwind-◅◅ {f = x ◅ f} {g} = ∘-resp-≈ˡ (unwind-◅◅ {f = f} {g}) ○ assoc
    unwind-resp-≈ : {A B : Obj} {f g : Star _⇒_ A B} → [ Underlying₀ X ] f ≈* g → unwind f ≈ unwind g
    unwind-resp-≈ ε = Equiv.refl
    unwind-resp-≈ (x ◅ eq) = ∘-resp-≈ (unwind-resp-≈ eq) x

  zig′ : (X : Graph o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)) → {A B : Graph.Obj X} → (f : Star (Graph._⇒_ X) A B) →
    [ X ] (unwind (Free X)) (mapGraph (GM X) f) ≈* f
  zig′ A ε        = ε
  zig′ A (fs ◅ f) = Graph.Equiv.refl A ◅ zig′ A f

  module _ {X Y : Category o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)} (F : Functor X Y) where
    open Category X renaming (Obj to Obj₁; _⇒_ to _⇒₁_)
    open Category Y renaming (_≈_ to _≈₂_; module Equiv to EY)
    open Category.HomReasoning Y
    open Functor F
    comm : {A B : Obj₁} (f : Star _⇒₁_ A B) → unwind Y (mapGraph (Underlying₁ F) f) ≈₂ F₁ (unwind X f)
    comm ε = EY.sym identity
    comm (x ◅ f) = EY.sym (homomorphism ○ Category.∘-resp-≈ˡ Y (EY.sym (comm f)))
