{-# OPTIONS --without-K --safe #-}

module Categories.Category.Construction.Graphs where

-- The "Underlying Graph" <-> "Free Category on a Graph" Adjunction.
--   [It's actually a Multidigraph, or Quiver.  Use the latter.]
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
open import Data.Quiver
open import Data.Quiver.Paths
import Data.Quiver.Morphism as QM
open QM using (Morphism)

open import Categories.Category
open import Categories.Functor using (Functor)
open import Categories.Functor.Equivalence
open import Categories.Category.Instance.StrictCats
open import Categories.Utils.EqReasoning
open import Categories.NaturalTransformation hiding (id)
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (refl; sym; trans; isEquivalence)
open import Categories.Adjoint
import Categories.Morphism.HeterogeneousIdentity as HId
import Categories.Category.Construction.FreeQuiver as FQ

private
  variable
    o o′ ℓ ℓ′ e e′ : Level

module Trsp (G : Quiver o ℓ e) where
  open Quiver G

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

module TrspGM {G : Quiver o ℓ e} {H : Quiver o′ ℓ′ e′}
              (m : Morphism G H) where
  module G = Quiver G
  module H = Quiver H
  open Morphism m
  open Trsp G
  open Trsp H using () renaming (_◂_ to _◃_; _▸_ to _▹_)

  M-resp-▸ : ∀ {A B C} (f : A G.⇒ B) (p : B ≡ C) →
             M₁ (f ▸ p) ≡ M₁ f ▹ ≡.cong M₀ p
  M-resp-▸ f ≡.refl = ≡.refl

  M-resp-◂ : ∀ {A B C} (p : A ≡ B) (f : B G.⇒ C) →
             M₁ (p ◂ f) ≡ ≡.cong M₀ p ◃ M₁ f
  M-resp-◂ ≡.refl f = ≡.refl

record GraphMorphism≈ {G : Quiver o ℓ e} {G′ : Quiver o′ ℓ′ e′}
                      (M M′ : Morphism G G′) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private
    module G  = Quiver G
    module G′ = Quiver G′
    module M  = Morphism M
    module M′ = Morphism M′
  open Trsp G′

  -- Pick a presentation of equivalence for graph morphisms that works
  -- well with functor equality.

  field
    M₀≡ : ∀ {X} → M.M₀ X ≡ M′.M₀ X
    M₁≡ : ∀ {A B} {f : A G.⇒ B} → M.M₁ f ▸ M₀≡ G′.≈ M₀≡ ◂ M′.M₁ f

Graphs : ∀ o ℓ e → Category (suc (o ⊔ ℓ ⊔ e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
Graphs o ℓ e = record
  { Obj       = Quiver o ℓ e
  ; _⇒_       = Morphism
  ; _≈_       = GraphMorphism≈
  ; id        = QM.id
  ; _∘_       = QM._∘_
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
        M₁ (f QM.∘ h) j ▸ ≡.trans (≡.cong (M₀ f) (M₀≡ eq′)) (M₀≡ eq)
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
    open Quiver
    open Morphism
    open GraphMorphism≈

open _≡F_

-- Put the rest of the Graph stuff here too:
Underlying₀ : Category o ℓ e → Quiver o ℓ e
Underlying₀ C = record { Obj = C.Obj ; _⇒_ = C._⇒_ ; _≈_ = C._≈_ ; equiv = C.equiv }
  where module C = Category C

Underlying₁ : {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → Functor C D → Morphism (Underlying₀ C) (Underlying₀ D)
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
          open Quiver.EdgeReasoning (Underlying₀ B)
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

module TrspStar (G : Quiver o ℓ e) where
  open Quiver G
  open Trsp (Underlying₀ (FQ.PathCategory G)) public using () renaming
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
module _ {G₁ G₂ : Quiver o ℓ e} (G⇒ : Morphism G₁ G₂) where
  open Quiver G₁ renaming (_⇒_ to _⇒₁_; Obj to Obj₁)
  open Quiver G₂ renaming (_⇒_ to _⇒₂_; Obj to Obj₂; module Equiv to Equiv₂)
  open FQ
  open Morphism G⇒

  mapGraph : {A B : Obj₁} → Star _⇒₁_ A B → Star _⇒₂_ (M₀ A) (M₀ B)
  mapGraph ε = ε
  mapGraph (x ◅ y) = M₁ x ◅ mapGraph y

  map-hom : {X Y Z : Quiver.Obj G₁} (f : Star _⇒₁_ X Y) {g : Star _⇒₁_ Y Z} →
      [ G₂ ] mapGraph (f ◅◅ g) ≈* (mapGraph f ◅◅ mapGraph g)
  map-hom ε {g} = refl G₂
  map-hom (x ◅ f) {g} = Equiv₂.refl ◅ map-hom f

  map-resp : {A B : Obj₁} (f : Star _⇒₁_ A B) {g : Star _⇒₁_ A B} →
      [ G₁ ] f ≈* g → [ G₂ ] mapGraph f ≈* mapGraph g
  map-resp ε ε = ε
  map-resp (x ◅ f) (f≈* ◅ eq) = M-resp-≈ f≈* ◅ map-resp f eq

-- don't want a single global Morphism
module _ {G : Quiver o ℓ e} where
  open Quiver G
  open Paths G

  map-id : {A B : Obj} (f : Star _⇒_ A B) → FQ.[ G ] mapGraph (QM.id {G = G}) f ≈* f
  map-id ε        = ε
  map-id (fs ◅ f) = Equiv.refl ◅ map-id f

module _ {X Y Z : Quiver o ℓ e} {G₁ : Morphism X Y} {G₂ : Morphism Y Z} where
  open Quiver X
  open Paths Z

  map-∘ : {A B : Obj} (f : Star _⇒_ A B) → FQ.[ Z ] (mapGraph (G₂ QM.∘ G₁) f) ≈* mapGraph G₂ (mapGraph G₁ f)
  map-∘ ε        = ε
  map-∘ (fs ◅ f) = Quiver.Equiv.refl Z ◅ map-∘ f

module _ {G H : Quiver o ℓ e} {f g : Morphism G H}
         (f≈g : GraphMorphism≈ f g) where
  open Quiver G
  open Paths H
  open Morphism
  open GraphMorphism≈ f≈g
  open TrspStar H
  open Trsp H

  map-M₁≡ : {A B : Obj} (hs : Star _⇒_ A B) →
            FQ.[ H ] mapGraph f hs ▸* M₀≡ ≈* M₀≡ ◂* mapGraph g hs
  map-M₁≡ ε        = FQ.≡⇒≈* H (◂*-▸*-ε M₀≡)
  map-M₁≡ (hs ◅ h) = begin
    (M₁ f hs ◅ mapGraph f h) ▸* M₀≡   ≡⟨ ◅-▸* (M₁ f hs) _ M₀≡ ⟩
    M₁ f hs ◅ (mapGraph f h ▸* M₀≡)   ≈⟨ Quiver.Equiv.refl H ◅ map-M₁≡ h ⟩
    M₁ f hs ◅ (M₀≡ ◂* mapGraph g h)   ≡⟨ ◅-◂*-▸ (M₁ f hs) M₀≡ _ ⟩
    (M₁ f hs ▸ M₀≡) ◅ mapGraph g h    ≈⟨ M₁≡ ◅ (Paths.refl H) ⟩
    (M₀≡ ◂ M₁ g hs) ◅ mapGraph g h    ≡˘⟨ ◂*-◅ M₀≡ (M₁ g hs) _ ⟩
    M₀≡ ◂* (M₁ g hs ◅ mapGraph g h)   ∎
    where open Paths.PathEqualityReasoning H

module _ (C : Category o ℓ e) where
  open Category C
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
  { F₀ = FQ.PathCategory
  ; F₁ = λ {G₁} {G₂} G⇒ → record
    { F₀ = M₀ G⇒
    ; F₁ = mapGraph G⇒
    ; identity = Paths.refl G₂
    ; homomorphism = λ {_} {_} {_} {f} → map-hom G⇒ f
    ; F-resp-≈ = λ { {f = f} → map-resp G⇒ f}
    }
  ; identity = λ {G} → record
    { eq₀ = λ _ → ≡.refl
    ; eq₁ = λ f → toSquare (FQ.PathCategory G) (map-id f)
    }
  ; homomorphism = λ {_} {_} {G} → record
    { eq₀ = λ _ → ≡.refl
    ; eq₁ = λ h → toSquare (FQ.PathCategory G) (map-∘ h)
    }
  ; F-resp-≈ = λ {_} {G} {f} {g} f≈g → record
    { eq₀ = λ _ → M₀≡ f≈g
    ; eq₁ = λ h →
      let open Category (FQ.PathCategory G)
          open HId      (FQ.PathCategory G)
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
  open Morphism
  open GraphMorphism≈

-- Because of the Level changes in CatF, sizes must all be same:
CatF-is-Free : (o ℓ e : Level) → Adjoint (CatF {o} {o ⊔ ℓ} {o ⊔ ℓ ⊔ e}) (Underlying)
CatF-is-Free o ℓ e = record
  { unit = ntHelper record
    { η = GM
    ; commute = λ {X} {Y} f → let open Paths Y in record { M₀≡ = ≡.refl ; M₁≡ = Quiver.Equiv.refl Y ◅ ε }
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
    ; eq₁ = λ f → toSquare (FQ.PathCategory G) (zig′ G f)
    }
  ; zag = λ {B} → record { M₀≡ = ≡.refl ; M₁≡ = Category.identityˡ B  }
  }
  where
  GM : (X : Quiver o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)) → Morphism X (Underlying₀ (FQ.PathCategory X))
  GM X = let open Paths X in record { M₀ = idFun ; M₁ = return ; M-resp-≈ = λ f≈g → f≈g ◅ ε }
  module _ (X : Category o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)) where
    open Category X
    open HomReasoning
    unwind : {A B : Obj} → Star _⇒_ A B → A ⇒ B
    unwind = fold _⇒_ (flip _∘_) id
    unwind-◅◅ : {A B C : Obj} {f : Star _⇒_ A B} {g : Star _⇒_ B C} →
                unwind (f ◅◅ g) ≈ (unwind g) ∘ (unwind f)
    unwind-◅◅ {f = ε} {g} = Equiv.sym identityʳ
    unwind-◅◅ {f = x ◅ f} {g} = ∘-resp-≈ˡ (unwind-◅◅ {f = f} {g}) ○ assoc
    module _ where
      open Paths (Underlying₀ X)
      unwind-resp-≈ : {A B : Obj} {f g : Star _⇒_ A B} → FQ.[ Underlying₀ X ] f ≈* g → unwind f ≈ unwind g
      unwind-resp-≈ ε = Equiv.refl
      unwind-resp-≈ (x ◅ eq) = ∘-resp-≈ (unwind-resp-≈ eq) x

  module _ (X : Quiver o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)) where
    open Paths X
    zig′ : {A B : Quiver.Obj X} → (f : Star (Quiver._⇒_ X) A B) →
      FQ.[ X ] (unwind (FQ.PathCategory X)) (mapGraph (GM X) f) ≈* f
    zig′ ε        = ε
    zig′ (fs ◅ f) = Quiver.Equiv.refl X ◅ zig′ f

  module _ {X Y : Category o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)} (F : Functor X Y) where
    open Category X renaming (Obj to Obj₁; _⇒_ to _⇒₁_)
    open Category Y renaming (_≈_ to _≈₂_; module Equiv to EY)
    open Category.HomReasoning Y
    open Functor F
    comm : {A B : Obj₁} (f : Star _⇒₁_ A B) → unwind Y (mapGraph (Underlying₁ F) f) ≈₂ F₁ (unwind X f)
    comm ε = EY.sym identity
    comm (x ◅ f) = EY.sym (homomorphism ○ Category.∘-resp-≈ˡ Y (EY.sym (comm f)))
