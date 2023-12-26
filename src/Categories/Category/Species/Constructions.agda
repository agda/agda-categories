{-# OPTIONS --without-K --safe #-}
module Categories.Category.Species.Constructions where

-- Construction of basic species

open import Level
open import Data.Empty
open import Data.Fin.Base as Fin using (Fin)
open import Data.Fin.Properties using (¬Fin0)
open import Data.Nat.Base using (ℕ; suc; zero)
open import Data.Product as × using (Σ; proj₁; proj₂; _,_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-setoid)
open import Data.Sum.Base as ⊎ using (inj₁; inj₂)
open import Data.Sum.Relation.Binary.Pointwise using (_⊎ₛ_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function.Base using () renaming (id to id→)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality as ≡

open import Categories.Category.Core using (Category)
open import Categories.Category.Construction.ObjectRestriction using (ObjectRestriction)
open import Categories.Category.Construction.Core using (Core)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Instance.FinSetoids using (FinSetoids; IsFiniteSetoid)
open import Categories.Category.Product
open import Categories.Functor.Core using (Functor)
open import Categories.Functor.Construction.Constant using (const)
open import Categories.Functor.Hom
open import Categories.Morphism.IsoEquiv using (_≃_)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)
open import Categories.Category.Species

import Categories.Morphism as Mor

-- Some useful preliminary definitions.  Should be in stdlib
module _ {o ℓ : Level} where
  -- the Setoid version of ⊥
  ⊥-Setoid : Setoid o ℓ
  ⊥-Setoid = record
    { Carrier = Lift o ⊥
    ; _≈_ = λ ()
    ; isEquivalence = record { refl = λ { {()} } ; sym = λ { {()} } ; trans = λ { {()} } } }

  ⊤-Setoid : Setoid o ℓ
  ⊤-Setoid = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤}

  ⊤-FinSetoid : Σ (Setoid o ℓ) IsFiniteSetoid
  ⊤-FinSetoid =
    ⊤-Setoid ,
    1 ,
    record
      { to = λ _ → Fin.zero
      ; from = λ _ → tt
      ; to-cong = λ _ → ≡.refl
      ; from-cong = λ _ → tt
      ; inverse = (λ { {Fin.zero} _ → ≡.refl }) , λ _ → tt
      }

-- We could have 4 levels, and still define Zero and One′.
-- But X needs o ≡ o′ and ℓ ≡ ℓ′.  And then the 'proper' definition of One makes that all the same.
module _ (o : Level) where
  -- Setoid o ℓ is used a lot, name it too
  S = Setoid o o
  FinSet = FinSetoids o o
  𝔹 = Core FinSet
  Sp = Species o o o o

  open Category Sp
  open Mor FinSet
  open _≅_

  -- convenient alias: a structure is an Object of Species
  -- (which is of course a functor)
  Structure = Obj

  Zero : Structure
  Zero = const ⊥-Setoid

  -- One can be specified in two ways.  The traditional one (which doesn't generalize as well)
  -- uses 'counting' directly. Don't even try it here, it just leads to much pain.
  
  -- There is a much nicer specification.
  One : Structure
  One = Hom[ 𝔹 ][ ⊤-FinSetoid ,-]

  -- the 'identity' Functor isn't really, it needs to forget the proof.
  X : Structure
  X = record
    { F₀ = proj₁
    ; F₁ = λ f → record
        { to = from f ⟨$⟩_
        ; cong = Func.cong (from f) }
    ; identity = id→
    ; homomorphism = λ { {f = f} {g} x≈y → Func.cong (from g) (Func.cong (from f) x≈y)}
    ; F-resp-≈ = _≃_.from-≈
    }

  -- generally this should be defined elsewhere
  _+_ : Structure → Structure → Structure
  A + B = record
    { F₀ = λ x → A.₀ x ⊎ₛ B.₀ x
    ; F₁ = λ X≅Y → record
      { to = ⊎.map (A.₁ X≅Y ⟨$⟩_) (B.₁ X≅Y ⟨$⟩_)
      ; cong = λ { (inj₁ x≈y) → inj₁ (Func.cong (A.₁ X≅Y) x≈y )
                 ; (inj₂ x≈y) → inj₂ (Func.cong (B.₁ X≅Y) x≈y)}
      }
    ; identity = λ { (inj₁ x) → inj₁ (A.identity x)
                   ; (inj₂ x) → inj₂ (B.identity x)}
    ; homomorphism = λ { (inj₁ x) → inj₁ (A.homomorphism x)
                       ; (inj₂ x) → inj₂ (B.homomorphism x) }
    ; F-resp-≈ = λ { f≃g (inj₁ x) → inj₁ (A.F-resp-≈ f≃g x)
                   ; f≃g (inj₂ x) → inj₂ (B.F-resp-≈ f≃g x)}
    }
    where
    module A = Functor A
    module B = Functor B

  -- Hadamard product
  _×_ : Structure → Structure → Structure
  A × B = record
    { F₀ = λ x → ×-setoid (A.₀ x) (B.₀ x)
    ; F₁ = λ X≅Y → record
      { to = ×.map (A.₁ X≅Y ⟨$⟩_) (B.₁ X≅Y ⟨$⟩_)
      ; cong = ×.map (Func.cong (A.₁ X≅Y)) (Func.cong (B.₁ X≅Y))
      }
    ; identity = ×.map A.identity B.identity
    ; homomorphism = ×.map A.homomorphism B.homomorphism
    ; F-resp-≈ = λ f≈g → ×.map (A.F-resp-≈ f≈g) (B.F-resp-≈ f≈g)
    }
    where
    module A = Functor A
    module B = Functor B
