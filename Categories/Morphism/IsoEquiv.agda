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

infix 4 _≃_
record _≃_ (i j : A ≅ B) : Set e where
  open _≅_
  field
    from-≈ : from i ≈ from j
    to-≈   : to i ≈ to j

≃-isEquivalence : IsEquivalence (_≃_ {A} {B})
≃-isEquivalence = record
  { refl  = record
    { from-≈ = refl
    ; to-≈   = refl
    }
  ; sym   = λ where
    record { from-≈ = from-≈ ; to-≈ = to-≈ } → record
      { from-≈ = sym from-≈
      ; to-≈   = sym to-≈
      }
  ; trans = λ where
    record { from-≈ = from-≈ ; to-≈ = to-≈ } record { from-≈ = from-≈′ ; to-≈ = to-≈′ } → record
      { from-≈ = trans from-≈ from-≈′
      ; to-≈   = trans to-≈ to-≈′
      }
  }
  where open _≅_
        open Equiv

≃-setoid : ∀ {A B : Obj} → Setoid _ _
≃-setoid {A} {B} = record
  { Carrier       = A ≅ B
  ; _≈_           = _≃_
  ; isEquivalence = ≃-isEquivalence
  }

----------------------------------------------------------------------

-- An alternative notion of equality on isomorphisms that only
-- considers the first arrow in the iso pair.  The two notions of
-- equality turn out to be equivalent.

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

-- If they exist, inverses are unique.

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

-- The two notions of equality are equivalent

≃⇒≃′ : ∀ {i j : A ≅ B} → i ≃ j → i ≃′ j
≃⇒≃′ eq = _≃_.from-≈ eq

≃′⇒≃ : ∀ {i j : A ≅ B} → i ≃′ j → i ≃ j
≃′⇒≃ {_} {_} {i} {j} eq = record
  { from-≈ = eq
  ; to-≈   = to-unique (iso i) (iso j) eq
  }
  where open _≅_
