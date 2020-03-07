{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Properties.Posets where

open import Level using (_⊔_; Lift; lift)
open import Data.Unit using (⊤; tt)
open import Data.Product as Prod using (_,_; <_,_>) renaming (_×_ to _|×|_)
open import Function using (flip)
open import Relation.Binary using (IsPartialOrder; Poset)
open import Relation.Binary.OrderMorphism
  using (id; _∘_) renaming (_⇒-Poset_ to _⇒_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Categories.Category
import Categories.Category.CartesianClosed as CCC
import Categories.Category.CartesianClosed.Canonical as Canonical
open import Categories.Category.Instance.Posets
open import Categories.Functor using (Functor; Endofunctor)
open import Categories.Utils.Product

open Poset renaming (_≈_ to ₍_₎_≈_; _≤_ to ₍_₎_≤_)
open _⇒_

-- The pointwise partial order on order preserving maps.
--
-- (See the Exponential module below for the definition of the
-- exponential/hom object based on this order.)

module Pointwise {a₁ a₂ a₃ b₁ b₂ b₃} {A : Poset a₁ a₂ a₃} {B : Poset b₁ b₂ b₃}
  where

  infix 4 _≤°_

  _≤°_ : (f g : A ⇒ B) → Set (a₁ ⊔ b₃)
  f ≤° g = ∀ {x} → ₍ B ₎ fun f x ≤ fun g x

  ≤°-isPartialOrder : IsPartialOrder _≗_ _≤°_
  ≤°-isPartialOrder = record
    { isPreorder      = record
      { isEquivalence = ≗-isEquivalence
      ; reflexive     = λ f≗g → reflexive B f≗g
      ; trans         = λ f≤g g≤h → trans B f≤g g≤h
      }
    ; antisym         = λ f≤g g≤f → antisym B f≤g g≤f
    }

  module ≤° = IsPartialOrder ≤°-isPartialOrder

open Pointwise

-- Poset has a duality involution: the poset obtained by reversing the
-- partial order is again a poset.

module Opposite where

  -- NOTE: we flip the direction of the underlying equality _≈_ as
  -- well, so that |op (op A) ≡ A| definitionally.

  op : ∀ {a₁ a₂ a₃} → Poset a₁ a₂ a₃ → Poset a₁ a₂ a₃
  op A = record
    { Carrier           = Carrier A
    ; _≈_               = flip ₍ A ₎_≈_
    ; _≤_               = flip ₍ A ₎_≤_
    ; isPartialOrder    = record
      { isPreorder      = record
        { isEquivalence = record
          { refl        = Eq.refl A
          ; sym         = Eq.sym A
          ; trans       = flip (Eq.trans A)
          }
        ; reflexive     = reflexive A
        ; trans         = flip (trans A)
        }
      ; antisym         = antisym A
      }
    }

  module _ {a₁ a₂ a₃} {A : Poset a₁ a₂ a₃} where

    op-involutive : op (op A) ≡ A
    op-involutive = ≡.refl

    module _ {b₁ b₂ b₃} {B : Poset b₁ b₂ b₃} where

      op₁ : A ⇒ B → op A ⇒ op B
      op₁ f = record { fun = fun f ; monotone = monotone f }

      op₂ : {f g : A ⇒ B} → f ≤° g → op₁ g ≤° op₁ f
      op₂ f≤g = f≤g

  -- op induces an endofunctor on Posets

  op-functor : ∀ {a₁ a₂ a₃} → Endofunctor (Posets a₁ a₂ a₃)
  op-functor = record
    { F₀           = op
    ; F₁           = op₁
    ; identity     = λ {A}       → Eq.refl A
    ; homomorphism = λ {_ _ C}   → Eq.refl C
    ; F-resp-≈     = λ {_ B} x≈y → Eq.sym B x≈y
    }

  module op {a₁ a₂ a₃} = Functor (op-functor {a₁} {a₂} {a₃})

-- The category of posets has terminal objects.

module Terminals where

  unit : ∀ a₁ a₂ a₃ → Poset a₁ a₂ a₃
  unit a₁ a₂ a₃ = record
    { Carrier = Lift a₁ ⊤
    ; _≈_     = λ _ _ → Lift a₂ ⊤
    ; _≤_     = λ _ _ → Lift a₃ ⊤
    }

  module _ {a₁ a₂ a₃ b₁ b₂ b₃} {B : Poset b₁ b₂ b₃} where

    ! : B ⇒ unit a₁ a₂ a₃
    ! = _

    !-unique : (f : B ⇒ unit a₁ a₂ a₃) → ! ≗ f
    !-unique f = _

open Terminals

-- The category of posets has products.

module Products where

  infixr 2 _×_

  _×_ : ∀ {a₁ a₂ a₃ b₁ b₂ b₃} →
        Poset a₁ a₂ a₃ → Poset b₁ b₂ b₃ → Poset (a₁ ⊔ b₁) (a₂ ⊔ b₂) (a₃ ⊔ b₃)
  A × B = record
    { Carrier           = Carrier A |×| Carrier B
    ; _≈_               = ₍ A ₎_≈_ -< _|×|_ >- ₍ B ₎_≈_
    ; _≤_               = ₍ A ₎_≤_ -< _|×|_ >- ₍ B ₎_≤_
    ; isPartialOrder    = record
      { isPreorder      = record
        { isEquivalence = record
          { refl        = Eq.refl A , Eq.refl B
          ; sym         = Prod.map (Eq.sym A) (Eq.sym B)
          ; trans       = Prod.zip (Eq.trans A) (Eq.trans B)
          }
        ; reflexive     = Prod.map (reflexive A) (reflexive B)
        ; trans         = Prod.zip (trans A) (trans B)
        }
      ; antisym         = Prod.zip (antisym A) (antisym B)
      }
    }

  module _ {a₁ a₂ a₃ b₁ b₂ b₃} {A : Poset a₁ a₂ a₃} {B : Poset b₁ b₂ b₃} where

    π₁ : (A × B) ⇒ A
    π₁ = record { fun = Prod.proj₁ ; monotone = Prod.proj₁ }

    π₂ : (A × B) ⇒ B
    π₂ = record { fun = Prod.proj₂ ; monotone = Prod.proj₂ }

    module _ {c₁ c₂ c₃} {C : Poset c₁ c₂ c₃} where

      infix 11 ⟨_,_⟩

      ⟨_,_⟩ : C ⇒ A → C ⇒ B → C ⇒ (A × B)
      ⟨ f , g ⟩ = record
        { fun      = < fun f , fun g >
        ; monotone = < monotone f , monotone g >
        }

      π₁-comp  : {f : C ⇒ A} {g : C ⇒ B} → π₁ ∘ ⟨ f , g ⟩ ≗ f
      π₁-comp = Eq.refl A

      π₂-comp  : {f : C ⇒ A} {g : C ⇒ B} → π₂ ∘ ⟨ f , g ⟩ ≗ g
      π₂-comp = Eq.refl B

      ⟨,⟩-unique : {f : C ⇒ A} {g : C ⇒ B} {h : C ⇒ (A × B)} →
                   π₁ ∘ h ≗ f → π₂ ∘ h ≗ g → ⟨ f , g ⟩ ≗ h
      ⟨,⟩-unique hyp₁ hyp₂ {x} = Eq.sym A hyp₁ , Eq.sym B hyp₂

  infixr 2 _×₁_

  _×₁_ : ∀ {a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ d₁ d₂ d₃}
         {A : Poset a₁ a₂ a₃} {B : Poset b₁ b₂ b₃}
         {C : Poset c₁ c₂ c₃} {D : Poset d₁ d₂ d₃} →
         A ⇒ C → B ⇒ D → (A × B) ⇒ (C × D)
  f ×₁ g = ⟨ f ∘ π₁ , g ∘ π₂ ⟩

open Products

-- The category of posets has exponential objects.
--
-- It's easier to define exponentials with respect to the *canonical*
-- product.  The more generic version can then be given by appealing
-- to uniqueness (up to iso) of products.

module Exponentials where

  -- Use arrow rather than exponential notation for readability.

  infixr 9 _⇨_

  _⇨_ : ∀ {a₁ a₂ a₃ b₁ b₂ b₃} → Poset a₁ a₂ a₃ → Poset b₁ b₂ b₃ →
        Poset (a₁ ⊔ a₃ ⊔ b₁ ⊔ b₃) (a₁ ⊔ b₂) (a₁ ⊔ b₃)
  A ⇨ B = record
    { Carrier           = A ⇒ B
    ; _≈_               = _≗_
    ; _≤_               = _≤°_
    ; isPartialOrder    = ≤°-isPartialOrder
    }

  module _ {a₁ a₂ a₃ b₁ b₂ b₃} {A : Poset a₁ a₂ a₃} {B : Poset b₁ b₂ b₃} where

    eval : (A ⇨ B × A) ⇒ B
    eval = record
      { fun      = λ{ (f , x) → fun f x }
      ; monotone = λ{ {f , _} (f≤g , x≤y) → trans B (monotone f x≤y) f≤g }
      }

    module _ {c₁ c₂ c₃} {C : Poset c₁ c₂ c₃} where

      curry : (C × A) ⇒ B → C ⇒ (A ⇨ B)
      curry f = record
        { fun        = λ x → record
          { fun      = Prod.curry (fun f) x
          ; monotone = Prod.curry (monotone f) (refl C)
          }
        ; monotone   = λ x≤y → monotone f (x≤y , refl A)
        }

      eval-comp : {f : (C × A) ⇒ B} → eval ∘ (curry f ×₁ id) ≗ f
      eval-comp = Eq.refl B

      curry-resp-≗ : {f g : (C × A) ⇒ B} → f ≗ g → curry f ≗ curry g
      curry-resp-≗ hyp = hyp

      curry-unique : {f : C ⇒ (A ⇨ B)} {g : (C × A) ⇒ B} →
                     eval ∘ (f ×₁ id) ≗ g → f ≗ curry g
      curry-unique hyp = hyp

open Exponentials

-- The category of posets is cartesian closed.

Posets-CanonicallyCCC : ∀ {a} → Canonical.CartesianClosed (Posets a a a)
Posets-CanonicallyCCC = record
  { !            = !
  ; π₁           = π₁
  ; π₂           = π₂
  ; ⟨_,_⟩        = ⟨_,_⟩
  ; !-unique     = !-unique
  ; π₁-comp      = λ {_ _ f _ g}   → π₁-comp {f = f} {g}
  ; π₂-comp      = λ {_ _ f _ g}   → π₂-comp {f = f} {g}
  ; ⟨,⟩-unique   = λ {_ _ _ f g h} → ⟨,⟩-unique {f = f} {g} {h}
  ; eval         = eval
  ; curry        = curry
  ; eval-comp    = λ {_ _ _ f}   → eval-comp {f = f}
  ; curry-resp-≈ = λ {_ _ _ f g} → curry-resp-≗ {f = f} {g}
  ; curry-unique = λ {_ _ _ f g} → curry-unique {f = f} {g}
  }

module CanonicallyCartesianClosed {a} =
  Canonical.CartesianClosed (Posets-CanonicallyCCC {a})

Posets-CCC : ∀ {a} → CCC.CartesianClosed (Posets a a a)
Posets-CCC = Canonical.Equivalence.fromCanonical _ Posets-CanonicallyCCC

module CartesianClosed {a} = CCC.CartesianClosed (Posets-CCC {a})
