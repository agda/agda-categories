{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Morphism.IsoEquiv {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level
open import Function using (flip; _on_)
open import Relation.Binary hiding (_⇒_)
import Relation.Binary.Construct.On as On

open import Categories.Morphism 𝒞

open Category 𝒞

private
  variable
    A B C : Obj

-- Two lemmas to set things up: if they exist, inverses are unique.

to-unique : ∀ {f₁ f₂ : A ⇒ B} {g₁ g₂} →
            Iso f₁ g₁ → Iso f₂ g₂ → f₁ ≈ f₂ → g₁ ≈ g₂
to-unique {_} {_} {f₁} {f₂} {g₁} {g₂} iso₁ iso₂ hyp = begin
                 g₁   ≈˘⟨ identityˡ ⟩
     id        ∘ g₁   ≈˘⟨ ∘-resp-≈ˡ Iso₂.isoˡ ⟩
    (g₂ ∘  f₂) ∘ g₁   ≈˘⟨ ∘-resp-≈ˡ (∘-resp-≈ʳ hyp) ⟩
    (g₂ ∘  f₁) ∘ g₁   ≈⟨ assoc ⟩
     g₂ ∘ (f₁  ∘ g₁)  ≈⟨ ∘-resp-≈ʳ Iso₁.isoʳ ⟩
     g₂ ∘  id         ≈⟨ identityʳ ⟩
     g₂               ∎
  where
    open HomReasoning
    module Iso₁ = Iso iso₁
    module Iso₂ = Iso iso₂

from-unique : ∀ {f₁ f₂ : A ⇒ B} {g₁ g₂} →
              Iso f₁ g₁ → Iso f₂ g₂ → g₁ ≈ g₂ → f₁ ≈ f₂
from-unique iso₁ iso₂ hyp = to-unique iso₁⁻¹ iso₂⁻¹ hyp
  where
    iso₁⁻¹ = record { isoˡ = Iso.isoʳ iso₁  ; isoʳ = Iso.isoˡ iso₁ }
    iso₂⁻¹ = record { isoˡ = Iso.isoʳ iso₂  ; isoʳ = Iso.isoˡ iso₂ }

-- Equality of isomorphisms is just equality of the underlying morphism(s).
--
-- Only one equation needs to be given; the equation in the other
-- direction holds automatically (by the above lemmas).
--
-- The reason for wrapping the underlying equality in a record at all
-- is that this helps unification.  Concretely, it allows Agda to
-- infer the isos |i| and |j| being related in function applications
-- where only the equation |i ≃ j| is passed as an explicit argument.

infix 4 _≃_
record _≃_ (i j : A ≅ B) : Set e where
  constructor ⌞_⌟
  open _≅_
  field from-≈ : from i ≈ from j

  to-≈ : to i ≈ to j
  to-≈ = to-unique (iso i) (iso j) from-≈

open _≃_

module _ {A B : Obj} where
  open Equiv

  ≃-refl : Reflexive (_≃_ {A} {B})
  ≃-refl = ⌞ refl ⌟

  ≃-sym : Symmetric (_≃_ {A} {B})
  ≃-sym = λ where ⌞ eq ⌟          → ⌞ sym eq ⌟

  ≃-trans : Transitive (_≃_ {A} {B})
  ≃-trans = λ where ⌞ eq₁ ⌟ ⌞ eq₂ ⌟ → ⌞ trans eq₁ eq₂ ⌟

  ≃-isEquivalence : IsEquivalence (_≃_ {A} {B})
  ≃-isEquivalence = record
    { refl  = ≃-refl
    ; sym   = ≃-sym
    ; trans = ≃-trans
    }

≃-setoid : ∀ {A B : Obj} → Setoid _ _
≃-setoid {A} {B} = record
  { Carrier       = A ≅ B
  ; _≈_           = _≃_
  ; isEquivalence = ≃-isEquivalence
  }

----------------------------------------------------------------------

-- An alternative, more direct notion of equality on isomorphisms that
-- involves no wrapping/unwrapping.

infix 4 _≃′_
_≃′_ : Rel (A ≅ B) e
_≃′_ = _≈_ on _≅_.from

≃′-isEquivalence : IsEquivalence (_≃′_ {A} {B})
≃′-isEquivalence = On.isEquivalence _≅_.from equiv

≃′-setoid : ∀ {A B : Obj} → Setoid _ _
≃′-setoid {A} {B} = record
  { Carrier       = A ≅ B
  ; _≈_           = _≃′_
  ; isEquivalence = ≃′-isEquivalence
  }

-- The two notions of equality are equivalent

≃⇒≃′ : ∀ {i j : A ≅ B} → i ≃ j → i ≃′ j
≃⇒≃′ eq = from-≈ eq

≃′⇒≃ : ∀ {i j : A ≅ B} → i ≃′ j → i ≃ j
≃′⇒≃ {_} {_} {i} {j} eq = ⌞ eq ⌟
