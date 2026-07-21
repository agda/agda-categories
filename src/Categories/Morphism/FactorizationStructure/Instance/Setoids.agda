{-# OPTIONS --without-K --safe #-}
open import Level

-- ------------------------------------------------------------------
-- The category Setoids c ℓ has a [ Surj , Inj ]-factorization system
-- ------------------------------------------------------------------

module Categories.Morphism.FactorizationStructure.Instance.Setoids {c ℓ : Level} where

open import Categories.Morphism.FactorizationStructure
open import Categories.Category.Instance.Setoids
open import Categories.Morphism (Setoids c ℓ) using (Epi; Mono; _≅_)
open import Categories.Morphism.Lifts (Setoids c ℓ) using (MorphismClass; _⊆_; ≈-closed; MorphismClassMember; Diagonal; UniqueDiagonal)
open import Categories.Morphism.Properties (Setoids c ℓ)
open import Categories.Category
open import Function.Bundles using (Func; _⟨$⟩_; Surjection; LeftInverse; Injection; Inverse)
open import Data.Maybe
open import Data.Unit
open import Function.Definitions
open import Relation.Binary using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Properties using (setoid)
import Function.Construct.Composition as compose
import Function.Construct.Constant as constant
import Relation.Binary.Reasoning.Setoid as SetoidR
open import Data.Product.Base

open Category (Setoids c ℓ)
open Definitions (Setoids c ℓ) using (CommutativeSquare)
open import Categories.Morphism (Setoids c ℓ) using (IsIso; Iso; _RetractOf_)
open MorphismClassMember
open import Categories.Morphism.Lifts.Properties (Setoids c ℓ) using (Mono⇒UniqueDiagonal)

private
  variable
    A B C D : Setoid c ℓ

-- A helper to convert properties from `Function.Definitions` to morphism classes
FuncClass : {p : Level}
          → ({A : Set c} {B : Set c} (_≈₁_ : Rel A ℓ) (_≈₂_ : Rel B ℓ) → (A → B) → Set p)
          → ({A B : Setoid c ℓ} → A ⇒ B → Set p)
FuncClass property {A} {B} f = property (Setoid._≈_ A) (Setoid._≈_ B) (Func.to f)

Surj : MorphismClass (c ⊔ ℓ)
Surj = FuncClass Surjective

Inj : MorphismClass (c ⊔ ℓ)
Inj = FuncClass Injective

-- We show that Setoids c ℓ are [ Surj , Inj ]-structured:
open import Categories.Morphism.FactorizationStructure.Core (Setoids c ℓ) Surj Inj

-- --------------------------------------------------------------------
-- 1. Morphism classes Surj and Inj are closed under morphism equality:
-- --------------------------------------------------------------------

Surj-resp-≈ : ≈-closed Surj
Surj-resp-≈ {Y = Y} {f} {g} f≈g f-surjective y = f-surjective y .proj₁ , λ {x'} x'≈x →
  begin
  g ⟨$⟩ x' ≈⟨ f≈g ⟨
  f ⟨$⟩ x' ≈⟨ f-surjective y .proj₂ x'≈x ⟩
  y ∎
  where open SetoidR Y

Inj-resp-≈ : ≈-closed Inj
Inj-resp-≈ {Y = Y} {f} {g} f≈g f-injective {x} {x'} g[x]≈g[x'] =
  f-injective (begin
    f ⟨$⟩ x    ≈⟨ f≈g ⟩
    g ⟨$⟩ x    ≈⟨ g[x]≈g[x'] ⟩
    g ⟨$⟩ x'   ≈⟨ f≈g ⟨
    f ⟨$⟩ x'   ∎)
  where open SetoidR Y

-- -----------------------------------------------------
-- 2. Surj is closed under composition with isomorphisms
-- -----------------------------------------------------

Retract⇒Inverseʳ : (g : C ⇒ D) (g⁻¹ : D ⇒ C) → g⁻¹ RetractOf g
        → Inverseʳ (Setoid._≈_ C) (Setoid._≈_ D) (Func.to g) (Func.to g⁻¹)
Retract⇒Inverseʳ {C} {D} g g⁻¹ g⁻¹∘g≈id y≈g[x] = Setoid.trans C (Func.cong g⁻¹ y≈g[x]) g⁻¹∘g≈id

Iso⇒Inverse : ∀ {f : A ⇒ B} → IsIso f → Inverse A B
Iso⇒Inverse {f = f} f-inv = record
  { to = f .to
  ; from = inv .to
  ; to-cong = f .cong
  ; from-cong = inv .cong
  ; inverse = Retract⇒Inverseʳ inv f isoʳ , Retract⇒Inverseʳ f inv isoˡ
  }
  where open Func
        open IsIso f-inv

Iso∘Surj⊆Surj : ∀ {h : B ⇒ C} → IsIso h → (e : MorphismClassMember Surj A B) → Surj (h ∘ mor e)
Iso∘Surj⊆Surj {B} {C} {A} {h = h} h⁻¹ e =
  compose.surjective (A ._≈_) (B ._≈_) (C ._≈_)
    (e .in-class)
    (Surjection.surjective (LeftInverse.surjection (Inverse.leftInverse (Iso⇒Inverse h⁻¹))))
  where open Setoid
  -- Here, we do not go via Epi, because the direction
  -- `Epi ⊆ Surj` would require c ⊑ ℓ

-- ----------------------------------------------------------------------------------
-- 3. Inj is closed under composition with isomorphisms. Here we show that Inj ≐ Mono
--    and then use the respective property of monomorphisms:
-- ----------------------------------------------------------------------------------

Inj⊆Mono : Inj ⊆ Mono
Inj⊆Mono f-Inj = λ g₁ g₂ f[g₁[x]]≈f[g₂[x]] → f-Inj f[g₁[x]]≈f[g₂[x]]

Mono⊆Inj : Mono ⊆ Inj
Mono⊆Inj f-Mono {x₁} {x₂} f[x₁]≈f[x₂] =
  f-Mono (! x₁) (! x₂) f[x₁]≈f[x₂] {x₁}
  where
    -- we use constant endo-functions instead of
    -- constant functions from Data.Unit.⊤ because
    -- the Setoid C already has the right levels
    !_ : (Setoid.Carrier C) → (C ⇒ C)
    !_ {C} = constant.function C C

Inj∘Iso⊆Inj : ∀ (m : MorphismClassMember Inj B C) {h : A ⇒ B} → IsIso h → Inj (mor m ∘ h)
Inj∘Iso⊆Inj m {h} h⁻¹ =
  Mono⊆Inj {f = mor m ∘ h}
    (Mono-∘ {f = mor m} {g = h}
      (Inj⊆Mono {f = mor m} (m .in-class))
      (Iso⇒Mono {f = h} (IsIso.iso h⁻¹)))

-- ------------------------------------------------------
-- 4. The actual image factorization of a Setoid function
-- ------------------------------------------------------
Im[_] : ∀ {X} {Y} (f : X ⇒ Y) → Setoid c ℓ
Im[_] {X} {Y} f = record
  { Carrier = Setoid.Carrier X
  ; _≈_ = λ x x' → (Setoid._≈_ Y) (f ⟨$⟩ x) (f ⟨$⟩ x')
  ; isEquivalence = record
    { refl = λ {x} → Func.cong f (Setoid.refl X)
    ; sym = Setoid.sym Y
    ; trans = Setoid.trans Y
    }
  }

Dom↠Im[_] : ∀ {X} {Y} (f : X ⇒ Y) → X ↠ Im[ f ]
Dom↠Im[_] f = record
  { mor = record
    { to = λ x → x
    ; cong = Func.cong f
    }
  ; in-class = λ x → x , (λ {x'} → f .Func.cong)
  }

Im[_]↣Codom : ∀ {X} {Y} (f : X ⇒ Y) → Im[ f ] ↣ Y
Im[_]↣Codom f = record
  { mor = record
    { to = Func.to f
    ; cong = λ f[x]≈f[x'] → f[x]≈f[x']
    }
  ; in-class = λ f[x]≈f[x'] → f[x]≈f[x']
  }

diagonalization : {f : A ⇒ C} {g : B ⇒ D} (e : A ↠ B) (m : C ↣ D)
                  → CommutativeSquare (mor e) f g (mor m)
                  → UniqueDiagonal (mor e) f g (mor m)
diagonalization {A} {C} {B} {D} {f} {g} e m g∘e≈m∘f =
  Mono⇒UniqueDiagonal (Inj⊆Mono {f = mor m} (m .in-class)) g∘e≈m∘f d m∘d≈g
  where
    open Setoid
    open SetoidR D

    -- consider a splitting of the surjection e
    s : B .Carrier → A .Carrier
    s b = proj₁ (e .in-class b)

    e∘s : ∀ b → Setoid._≈_ B (mor e ⟨$⟩ (s b)) b
    e∘s b = proj₂ (e .in-class b) (refl A)

    d₀ : B .Carrier → C .Carrier
    d₀ b = f ⟨$⟩ s b

    -- one of the triangles, the other comes
    -- automatically because m ∈ Inj ⊆ Mono
    m∘d≈g : ∀ {b} → Setoid._≈_ D (mor m ⟨$⟩ d₀ b) (g ⟨$⟩ b)
    m∘d≈g {b} = begin
      mor m ⟨$⟩ d₀ b            ≡⟨⟩
      (mor m ∘ f) ⟨$⟩ s b       ≈⟨ g∘e≈m∘f ⟨
      g ⟨$⟩ (mor e ⟨$⟩ s b)      ≈⟨ Func.cong g (e∘s b) ⟩
      g ⟨$⟩ (b) ∎

    d : B ⇒ C
    d = record
      { to = d₀
      ; cong = λ {b} {b'} b≈b' → m .in-class (begin
             mor m ⟨$⟩ d₀ b   ≈⟨ m∘d≈g ⟩
             g ⟨$⟩ b          ≈⟨ Func.cong g b≈b' ⟩
             g ⟨$⟩ b'         ≈⟨ m∘d≈g ⟨
             mor m ⟨$⟩ d₀ b'  ∎)
      }


[Surj,Inj]-factorizations : [ Surj , Inj ]-structured (Setoids c ℓ)
[Surj,Inj]-factorizations = record
  { ℰ-resp-≈ = λ {X} {Y} {f} {g} → Surj-resp-≈ {X} {Y} {f} {g}
  ; ℳ-resp-≈ = λ {X} {Y} {f} {g} → Inj-resp-≈ {X} {Y} {f} {g}
  ; factor = λ {X} f → record
           { Im = Im[ f ]
           ; e = Dom↠Im[ f ]
           ; m = Im[ f ]↣Codom
           ; m∘e≈h = λ {x} → Func.cong f (Setoid.refl X)
           }
  ; Iso∘ℰ = Iso∘Surj⊆Surj
  ; ℳ∘Iso = Inj∘Iso⊆Inj
  ; diagonalization = diagonalization
  }
