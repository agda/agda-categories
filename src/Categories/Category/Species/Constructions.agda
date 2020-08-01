{-# OPTIONS --without-K --safe #-}
module Categories.Category.Species.Constructions where

-- Construction of basic species

open import Level
open import Data.Empty
open import Data.Fin.Base as Fin using (Fin)
open import Data.Fin.Properties using (¬Fin0)
open import Data.Fin.Permutation using (↔⇒≡)
open import Data.Nat.Base using (ℕ; suc; zero)
open import Data.Nat.Properties using (_≟_)
open import Data.Product as × using (Σ; proj₁; proj₂; _,_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Data.Sum.Base as ⊎ using (inj₁; inj₂)
open import Data.Sum.Relation.Binary.Pointwise using (_⊎ₛ_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function.Base using () renaming (id to id→)
open import Function.Equality using (_⟨$⟩_; cong; Π) renaming (id to idΠ)
open import Function.Bundles using (Inverse)
open import Relation.Nullary using (Dec; yes; no)
import Function.Inverse as Inv
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality as ≡
open import Relation.Binary.Indexed.Heterogeneous.Construct.Trivial using (indexedSetoid)

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
      { f = λ _ → Fin.zero
      ; f⁻¹ = λ _ → tt
      ; cong₁ = λ _ → ≡.refl
      ; cong₂ = λ _ → tt
      ; inverse = (λ { Fin.zero → ≡.refl}) , λ _ → tt
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
  -- uses 'counting' directly.
  One′ : Structure
  One′ = record
    { F₀ = on-singleton
    ; F₁ = map-singleton
    ; identity = λ {A} x≈y → identity′ {A} x≈y -- eta expansion needed
    ; homomorphism = λ {X} {Y} {Z} → homomorphism′ {X} {Y} {Z} -- eta needed
    ; F-resp-≈ = resp
    }
    where

    iso⇒Inverse : (A B : Σ S IsFiniteSetoid) (A≅B : A ≅ B) → Inverse (proj₁ A) (proj₁ B)
    iso⇒Inverse (s , n , p) (s′ , n′ , p′) A≅B = record
      { f = from A≅B ⟨$⟩_
      ; f⁻¹ = to A≅B ⟨$⟩_
      ; cong₁ = cong (from A≅B)
      ; cong₂ = cong (to A≅B)
      ; inverse = (λ x → isoʳ A≅B (Setoid.refl s′ {x})) , λ x → isoˡ A≅B (Setoid.refl s {x})
      }

    iso⇒≡ : {A B : Σ S IsFiniteSetoid} (A≅B : A ≅ B) → proj₁ (proj₂ A) ≡.≡ proj₁ (proj₂ B)
    iso⇒≡ {A@(s , n , p)} {B@(s′ , n′ , p′)} A≅B = ↔⇒≡ ( (translate p′) Inv.∘ (translate X Inv.∘ Inv.sym (translate p)))
      where
      X : Inverse (proj₁ A) (proj₁ B)
      X = iso⇒Inverse A B A≅B
      translate : {a b c d : Level} {X : Setoid a b} {Y : Setoid c d} → Inverse X Y → Inv.Inverse X Y
      translate I = record
        { to = record { _⟨$⟩_ = Inverse.f I ; cong = Inverse.cong₁ I }
        ; from = record { _⟨$⟩_ = Inverse.f⁻¹ I ; cong = Inverse.cong₂ I }
        ; inverse-of = record
          { left-inverse-of = Inverse.inverseʳ I
          ; right-inverse-of = Inverse.inverseˡ I
          }
        }

    -- one can do this in 3 cases structurally, but that leads to 9 cases elsewhere
    -- so a dispatch on size makes sense
    on-singleton : Σ S IsFiniteSetoid → S
    on-singleton (s , n , _) with n ≟ 1
    ... | yes p = s
    ... | no ¬p = ⊥-Setoid

    map-singleton : {A B : Σ S IsFiniteSetoid} → A ≅ B → Π (on-singleton A) (indexedSetoid (on-singleton B))
    map-singleton {s , n , p} {s′ , n′ , p′} A≅B with n ≟ 1 | n′ ≟ 1
    map-singleton A≅B | yes ≡.refl | yes ≡.refl = from A≅B
    map-singleton A≅B | yes ≡.refl | no  n′≢1    = ⊥-elim (n′≢1 (≡.sym (iso⇒≡ A≅B)))
    map-singleton A≅B | no  n≢1    | yes n′≡1    = ⊥-elim (n≢1 (≡.trans (iso⇒≡ A≅B) n′≡1))
    map-singleton A≅B | no  n≢1    | no  n′≢1    = idΠ

    identity′ : {A : Σ S IsFiniteSetoid} {x y : Setoid.Carrier (on-singleton A)} →
      let SA = on-singleton A in
      Setoid._≈_ SA x y → Setoid._≈_ SA (map-singleton {A} {A} ≅.refl ⟨$⟩ x) y
    identity′ {s , ℕ.suc ℕ.zero , p} x≈y = x≈y

    homomorphism′ : {X Y Z : Σ S IsFiniteSetoid} {f : X ≅ Y} {g : Y ≅ Z} {x y : Setoid.Carrier (on-singleton X)} →
      Setoid._≈_ (on-singleton X) x y →
      Setoid._≈_ (on-singleton Z) (map-singleton (≅.trans f g) ⟨$⟩ x) (map-singleton g ⟨$⟩ (map-singleton f ⟨$⟩ y))
    homomorphism′ {f = f} {g} x≈y with iso⇒≡ f | iso⇒≡ g
    homomorphism′ {_ , 1 , _} {f = f} {g} x≈y | ≡.refl | ≡.refl = cong (from g) (cong (from f) x≈y)

    resp : {A B : Σ S IsFiniteSetoid} {f g : A ≅ B} →
      (_≃_ FinSet f g) →
      {x y : Setoid.Carrier (on-singleton A)} →
      Setoid._≈_ (on-singleton A) x y → Setoid._≈_ (on-singleton B) (map-singleton f ⟨$⟩ x) (map-singleton g ⟨$⟩ y)
    resp {_ , 1 , _} {f = f} {g} f≈g x≈y with iso⇒≡ f
    resp {_ , 1 , _} {f = f} {g} f≈g x≈y | ≡.refl = _≃_.from-≈ f≈g x≈y

  -- There is a much nicer specification.
  One : Structure
  One = Hom[ 𝔹 ][ ⊤-FinSetoid ,-]

  -- the 'identity' Functor isn't really, it needs to forget the proof.
  X : Structure
  X = record
    { F₀ = proj₁
    ; F₁ = λ f → record
        { _⟨$⟩_ = from f ⟨$⟩_
        ; cong = cong (from f) }
    ; identity = id→
    ; homomorphism = λ { {f = f} {g} x≈y → cong (from g) (cong (from f) x≈y)}
    ; F-resp-≈ = _≃_.from-≈
    }

  -- generally this should be defined elsewhere
  _+_ : Structure → Structure → Structure
  A + B = record
    { F₀ = λ x → A.₀ x ⊎ₛ B.₀ x
    ; F₁ = λ X≅Y → record
      { _⟨$⟩_ = ⊎.map (A.₁ X≅Y ⟨$⟩_) (B.₁ X≅Y ⟨$⟩_)
      ; cong = λ { (inj₁ x≈y) → inj₁ (cong (A.₁ X≅Y) x≈y )
                 ; (inj₂ x≈y) → inj₂ (cong (B.₁ X≅Y) x≈y)}
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
      { _⟨$⟩_ = ×.map (A.₁ X≅Y ⟨$⟩_) (B.₁ X≅Y ⟨$⟩_)
      ; cong = ×.map (cong (A.₁ X≅Y)) (cong (B.₁ X≅Y))
      }
    ; identity = ×.map A.identity B.identity
    ; homomorphism = ×.map A.homomorphism B.homomorphism
    ; F-resp-≈ = λ f≈g → ×.map (A.F-resp-≈ f≈g) (B.F-resp-≈ f≈g)
    }
    where
    module A = Functor A
    module B = Functor B
