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
-- 4. A lot of weird little lemmas about _≡_ and subst₂ are needed, because we're in a mixed
--    reasoning situation with both ≡ and ≈ present. This is both ugly and tiresome.

open import Level
open import Function using (_$_; flip) renaming (id to idFun; _∘_ to _⊚_)
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties hiding (trans)
open import Data.Product using (proj₁; proj₂; _,_)

open import Categories.Category
open import Categories.Functor using (Functor)
open import Categories.Category.Instance.StrictCats
open import Categories.Utils.EqReasoning
open import Categories.NaturalTransformation hiding (id)
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (refl; sym; trans; isEquivalence)
open import Categories.Adjoint

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

private
  variable
    o o′ ℓ ℓ′ e e′ : Level

-- TODO: move this to stdlib
module _ {i t} {I : Set i} {T : Rel I t} where

  ◅◅-identityʳ : ∀ {i j} → (xs : Star T i j) → xs ◅◅ ε ≡ xs
  ◅◅-identityʳ ε        = ≡.refl
  ◅◅-identityʳ (x ◅ xs) = ≡.cong (x ◅_) (◅◅-identityʳ xs)

module _ (G : Graph o ℓ e) where
  open Graph G
  private
    module equiv {A B} = IsEquivalence (equiv {A} {B})

  ≡⇒≈ : {A B : Obj} {f g : A ⇒ B} → f ≡ g → f ≈ g
  ≡⇒≈ ≡.refl = equiv.refl

  data [_]_≈*_ : {A B : Obj} → Star _⇒_ A B → Star _⇒_ A B → Set (o ⊔ ℓ ⊔ e) where
    ε : ∀ {A} →  [_]_≈*_ (ε {x = A}) ε
    _◅_ : ∀ {A B C} {f g : A ⇒ B} {h i : Star _⇒_ B C} → f ≈ g → [_]_≈*_ h i → [_]_≈*_ (f ◅ h) (g ◅ i)

  refl : ∀ {A B} → Reflexive ([_]_≈*_ {A} {B})
  refl {_} {_} {ε}        = ε
  refl {A} {B} {eq ◅ eq′} = equiv.refl ◅ refl

  sym : ∀ {A B} → Symmetric ([_]_≈*_ {A} {B})
  sym ε          = ε
  sym (eq ◅ eq′) = equiv.sym eq ◅ sym eq′

  trans : ∀ {A B} → Transitive ([_]_≈*_ {A} {B})
  trans ε ε                    = ε
  trans (eq₁ ◅ eq₂) (eq ◅ eq′) = (equiv.trans eq₁ eq) ◅ (trans eq₂ eq′)

  isEquivalence : ∀ {A B} → IsEquivalence ([_]_≈*_ {A} {B})
  isEquivalence = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }

  private
    _≈*_ = [_]_≈*_

  squish-subst₂-ε :  {x z : Obj} (eq₁ : x ≡ z) → ≡.subst₂ (Star _⇒_) eq₁ eq₁ ε ≈* ε
  squish-subst₂-ε ≡.refl = ε

  Free : Category o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)
  Free = record
    { Obj       = Obj
    ; _⇒_       = Star _⇒_
    ; _≈_       = _≈*_
    ; id        = ε
    ; _∘_       = _▻▻_
    ; assoc     = λ {_ _ _ _} {f g h} →
      ≡.subst (λ x → x ≈* ((f ◅◅ g) ◅◅ h)) (◅◅-assoc f g h) refl
    ; identityˡ = λ {_ _ f} → ≡.subst ((f ◅◅ ε) ≈*_) (◅◅-identityʳ f) refl
    ; identityʳ = refl
    ; equiv     = isEquivalence
    ; ∘-resp-≈  = resp
    }
    where resp : ∀ {A B C} {f h : Star _⇒_ B C} {g i : Star _⇒_ A B} →
                   f ≈* h → g ≈* i → (f ▻▻ g) ≈* (h ▻▻ i)
          resp eq ε = eq
          resp eq (eq₁ ◅ eq₂) = eq₁ ◅ (resp eq eq₂)

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

record GraphMorphism≈ {G : Graph o ℓ e} {G′ : Graph o′ ℓ′ e′}
                      (M M′ : GraphMorphism G G′) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private
    module G  = Graph G
    module G′ = Graph G′
    module M  = GraphMorphism M
    module M′ = GraphMorphism M′

  field
    M₀≡ : ∀ {X} → M.M₀ X ≡ M′.M₀ X
    M₁≡ : ∀ {A B} {f : A G.⇒ B} → ≡.subst₂ G′._⇒_ M₀≡ M₀≡ (M.M₁ f) G′.≈ M′.M₁ f

-- lemma to tell us that ≡.subst₂ doesn't get in the way of ≈
module _ (G : Graph o ℓ e) where
  open Graph G
  open ≡
  ≈cong : {A B C D : Obj} {f g : A ⇒ B} →
    (A≡C : A ≡ C) (B≡D : B ≡ D) (eq₁ : f ≈ g) →
    ≡.subst₂ _⇒_ A≡C B≡D f ≈ ≡.subst₂ _⇒_ A≡C B≡D g
  ≈cong ≡.refl ≡.refl eq₁ = eq₁

Graphs : ∀ o ℓ e → Category (suc (o ⊔ ℓ ⊔ e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
Graphs o ℓ e = record
  { Obj       = Graph o ℓ e
  ; _⇒_       = GraphMorphism
  ; _≈_       = GraphMorphism≈
  ; id        = idGHom
  ; _∘_       = _∘GM_
  ; assoc     = λ {_} {_} {_} {D} → record
    { M₀≡ = ≡.refl
    ; M₁≡ = IsEquivalence.refl (Graph.equiv D)
    }
  ; identityˡ = λ {_} {B} → record
    { M₀≡ = ≡.refl
    ; M₁≡ = IsEquivalence.refl (Graph.equiv B)
    }
  ; identityʳ = λ {_} {B} → record
    { M₀≡ = ≡.refl
    ; M₁≡ = IsEquivalence.refl (Graph.equiv B)
    }
  ; equiv     = λ {A B} → record
    { refl  = λ {eq} → record
      { M₀≡ = ≡.refl
      ; M₁≡ = IsEquivalence.refl (Graph.equiv B)
      }
    ; sym   = λ {i j} eq → record
      { M₀≡ = ≡.sym (M₀≡ eq)
      ; M₁≡ = λ {A₁ B₁ f} → let open EqR′ {B} {M₀ i A₁} {M₀ i B₁} in begin
        ≡.subst₂ (Graph._⇒_ B) (≡.sym (M₀≡ eq)) (≡.sym (M₀≡ eq)) (M₁ j f)
          ≈˘⟨ ≈cong B (≡.sym (M₀≡ eq)) (≡.sym (M₀≡ eq)) (M₁≡ eq) ⟩
        ≡.subst₂ (Graph._⇒_ B) (≡.sym (M₀≡ eq)) (≡.sym (M₀≡ eq))
          (≡.subst₂ (Graph._⇒_ B) (M₀≡ eq) (M₀≡ eq) (M₁ i f))
          ≈⟨ ≡⇒≈ B (subst₂-sym-subst₂ (Graph._⇒_ B) {M₁ i f} (M₀≡ eq) (M₀≡ eq)) ⟩
        M₁ i f
          ∎
      }
    ; trans = λ {i j k} eq eq′ → record
      { M₀≡ = ≡.trans (M₀≡ eq) (M₀≡ eq′)
      ; M₁≡ = λ {A₁ B₁ f} →  let open EqR′ {B} {M₀ k A₁} {M₀ k B₁} in begin
        ≡.subst₂ (Graph._⇒_ B) (≡.trans (M₀≡ eq) (M₀≡ eq′)) (≡.trans (M₀≡ eq) (M₀≡ eq′)) (M₁ i f)
          ≈˘⟨  ≡⇒≈ B (subst₂-subst₂ (Graph._⇒_ B) (M₀≡ eq) (M₀≡ eq′) (M₀≡ eq) (M₀≡ eq′))  ⟩
        ≡.subst₂ (Graph._⇒_ B) (M₀≡ eq′) (M₀≡ eq′) (≡.subst₂ (Graph._⇒_ B) (M₀≡ eq) (M₀≡ eq) (M₁ i f))
          ≈⟨ ≈cong B (M₀≡ eq′) (M₀≡ eq′) (M₁≡ eq)  ⟩
        ≡.subst₂ (Graph._⇒_ B) (M₀≡ eq′) (M₀≡ eq′) (M₁ j f)
          ≈⟨ M₁≡ eq′ ⟩
        M₁ k f
          ∎
      }
    }
  ; ∘-resp-≈  = λ {_ B C} {f g h i} eq eq′ → record
    { M₀≡ = λ {X} → ≡.trans (≡.cong (M₀ f) (M₀≡ eq′)) (M₀≡ eq)
    ; M₁≡ = λ {A₁ B₁ j} →  let open EqR′ {C} {M₀ g (M₀ i A₁)} {M₀ g (M₀ i B₁)} in begin
      ≡.subst₂ (Graph._⇒_ C)
               (≡.trans (≡.cong (M₀ f) (M₀≡ eq′)) (M₀≡ eq))
               (≡.trans (≡.cong (M₀ f) (M₀≡ eq′)) (M₀≡ eq)) (M₁ f (M₁ h j))
        ≈˘⟨ ≡⇒≈ C (subst₂-subst₂ (Graph._⇒_ C) (≡.cong (M₀ f) (M₀≡ eq′)) (M₀≡ eq) (≡.cong (M₀ f) (M₀≡ eq′)) (M₀≡ eq)) ⟩
      ≡.subst₂ (Graph._⇒_ C) (M₀≡ eq) (M₀≡ eq)
               (≡.subst₂ (Graph._⇒_ C) (≡.cong (M₀ f) (M₀≡ eq′))
                         (≡.cong (M₀ f) (M₀≡ eq′)) (M₁ f (M₁ h j)))
        ≈⟨  ≈cong C (M₀≡ eq) (M₀≡ eq) (≡⇒≈ C (subst₂-app (Graph._⇒_ C) (M₁ h j) (λ _ _ → M₁ f) (M₀≡ eq′) (M₀≡ eq′)))  ⟩
      ≡.subst₂ (Graph._⇒_ C) (M₀≡ eq) (M₀≡ eq) (M₁ f (≡.subst₂ (Graph._⇒_ B) (M₀≡ eq′) (M₀≡ eq′) (M₁ h j)))
        ≈⟨  ≈cong C (M₀≡ eq) (M₀≡ eq) (M-resp-≈ f (M₁≡ eq′))  ⟩
      ≡.subst₂ (Graph._⇒_ C) (M₀≡ eq) (M₀≡ eq) (M₁ f (M₁ i j))
        ≈⟨ M₁≡ eq ⟩
      M₁ g (M₁ i j)
        ∎
    }
  }
  where open GraphMorphism
        open GraphMorphism≈
        module EqR′ {G : Graph o ℓ e} {A B : Graph.Obj G} = EqR (Graph.setoid G {A} {B})

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
  ; F-resp-≈ = λ f≈g → record { M₀≡ = λ {X} → proj₁ f≈g X ; M₁≡ = λ {_} {_} {f} → proj₂ f≈g f }
  }
  where
  open NaturalTransformation
  open NaturalIsomorphism

-- define these ahead of time
module _ {G₁ G₂ : Graph o ℓ e} (G⇒ : GraphMorphism G₁ G₂) where
  open Graph G₁ renaming (_⇒_ to _⇒₁_; Obj to Obj₁; equiv to equiv₁)
  open Graph G₂ renaming (_⇒_ to _⇒₂_; Obj to Obj₂; equiv to equiv₂)
  open GraphMorphism G⇒

  mapGraph : {A B : Obj₁} → Star _⇒₁_ A B → Star _⇒₂_ (M₀ A) (M₀ B)
  mapGraph ε = ε
  mapGraph (x ◅ y) = M₁ x ◅ mapGraph y

  map-hom : {X Y Z : Graph.Obj G₁} (f : Star _⇒₁_ X Y) {g : Star _⇒₁_ Y Z} →
      [ G₂ ] mapGraph (f ◅◅ g) ≈* (mapGraph f ◅◅ mapGraph g)
  map-hom ε {g} = refl G₂
  map-hom (x ◅ f) {g} = IsEquivalence.refl equiv₂ ◅ map-hom f

  map-resp : {A B : Obj₁} (f : Star _⇒₁_ A B) {g : Star _⇒₁_ A B} →
      [ G₁ ] f ≈* g → [ G₂ ] mapGraph f ≈* mapGraph g
  map-resp ε ε = ε
  map-resp (x ◅ f) (f≈* ◅ eq) = M-resp-≈ f≈* ◅ map-resp f eq

-- don't want a single global GraphMorphism
module _ {G₁ : Graph o ℓ e} where
  open Graph G₁ renaming (_⇒_ to _⇒₁_; Obj to Obj₁; equiv to equiv₁)

  map-id : {A B : Obj₁} (f : Star _⇒₁_ A B) → [ G₁ ] mapGraph (idGHom {G = G₁}) f ≈* f
  map-id ε = ε
  map-id (x ◅ f) = IsEquivalence.refl equiv₁ ◅ map-id f

module _ {X Y Z : Graph o ℓ e} {G₁ : GraphMorphism X Y} {G₂ : GraphMorphism Y Z} where
  open Graph X

  map-∘ : {A B : Obj} (f : Star _⇒_ A B) → [ Z ] (mapGraph (G₂ ∘GM G₁) f) ≈* mapGraph G₂ (mapGraph G₁ f)
  map-∘ ε = ε
  map-∘ (x ◅ f) = IsEquivalence.refl (Graph.equiv Z) ◅ map-∘ f

module _ {X Y : Graph o ℓ e} {G₁ G₂ : GraphMorphism X Y} (G₁≈G₂ : GraphMorphism≈ G₁ G₂) where
  open Graph
  open GraphMorphism G₂
  open GraphMorphism≈ G₁≈G₂

  -- this squish function ought to be quite a bit more general, but it's really hard to figure out its type
  squish-subst₂-◅ : {A B C D E F : Obj Y} {x : _⇒_ Y A B} {y : _⇒_ Y C D} {f : Star (_⇒_ Y) B E} {g : Star (_⇒_ Y) D F} →
                    (eq₁ : A ≡ C) (eq₂ : B ≡ D) (eq₃ : E ≡ F) (x≈y : _≈_ Y (≡.subst₂ (_⇒_ Y) eq₁ eq₂ x) y) →
                    [ Y ] ≡.subst₂ (Star (_⇒_ Y)) eq₂ eq₃ f ≈* g →
                    [ Y ] ≡.subst₂ (Star (_⇒_ Y)) eq₁ eq₃ (x ◅ f) ≈* (y ◅ g)
  squish-subst₂-◅ ≡.refl ≡.refl ≡.refl x≈y rest = x≈y ◅ rest

  map-resp-≈ : {A B : Obj X} (f : Star (_⇒_ X) A B) → [ Y ] ≡.subst₂ (Star (_⇒_ Y)) M₀≡ M₀≡ (mapGraph G₁ f) ≈* mapGraph G₂ f
  map-resp-≈ ε = squish-subst₂-ε Y M₀≡
  map-resp-≈ (x ◅ f) = squish-subst₂-◅ M₀≡ M₀≡ M₀≡ M₁≡ (map-resp-≈ f)

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
  ; identity = (λ _ → ≡.refl) , map-id
  ; homomorphism = (λ _ → ≡.refl) , map-∘
  ; F-resp-≈ = λ G≈H → (λ X → M₀≡ G≈H {X}) , map-resp-≈ G≈H
  }
  where
  open GraphMorphism
  open GraphMorphism≈

-- Because of the Level changes in CatF, sizes must all be same:
CatF-is-Free : (o : Level) → Adjoint (CatF {o} {o} {o}) (Underlying)
CatF-is-Free o = record
  { unit = record
    { η = GM
    ; commute = λ {X} {Y} f → record { M₀≡ = ≡.refl ; M₁≡ = IsEquivalence.refl (Graph.equiv Y) ◅ ε }
    }
  ; counit = record
    { η = λ X → record
      { F₀ = idFun
      ; F₁ = unwind X
      ; identity = Category.Equiv.refl X
      ; homomorphism = λ { {f = f} {g} → unwind-◅◅ X {f = f} {g} }
      ; F-resp-≈ = unwind-resp-≈ X
      }
    ; commute = λ {X} {Y} F → ( (λ _ → ≡.refl) , comm F )
    }
  ; zig = λ {A} → (λ _ → ≡.refl) , zig′ A
  ; zag = λ {B} → record { M₀≡ = ≡.refl ; M₁≡ = Category.identityˡ B  }
  }
  where
  GM : (X : Graph o o o) → GraphMorphism X (Underlying₀ (Free X))
  GM _ = record { M₀ = idFun ; M₁ = return ; M-resp-≈ = λ f≈g → f≈g ◅ ε }
  module _ (X : Category o o o) where
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

  zig′ : (X : Graph o o o) → {A B : Graph.Obj X} → (f : Star (Graph._⇒_ X) A B) →
    let Y = Free X in [ X ] (unwind Y) (mapGraph (GM X) f) ≈* f
  zig′ A ε = ε
  zig′ A (x ◅ f) = IsEquivalence.refl (Graph.equiv A) ◅ zig′ A f
  module _ {X Y : Category o o o} (F : Functor X Y) where
    open Category X renaming (Obj to Obj₁; _⇒_ to _⇒₁_)
    open Category Y renaming (_≈_ to _≈₂_; module Equiv to EY)
    open Category.HomReasoning Y
    open Functor F
    comm : {A B : Obj₁} (f : Star _⇒₁_ A B) → unwind Y (mapGraph (Underlying₁ F) f) ≈₂ F₁ (unwind X f)
    comm ε = EY.sym identity
    comm (x ◅ f) = EY.sym (homomorphism ○ Category.∘-resp-≈ˡ Y (EY.sym (comm f)))
