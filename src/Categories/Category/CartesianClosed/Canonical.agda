{-# OPTIONS --without-K --safe #-}
open import Categories.Category.Core using (Category)

-- A "canonical" presentation of cartesian closed categories.
--
-- This presentation is equivalent to the one in
-- Categories.Category.CartesianClosed but it is easier to work with
-- in some circumstances.
--
-- Here, exponentials are not defined in terms of arbitrary products,
-- but in terms of a family of "canonical" products.  Since products
-- are defined only up to isomorphism the choice of product does not
-- matter for the property of being cartesian closed, but working with
-- a fixed choice of representatives simplifies the constructions of
-- some instances of CCCs (e.g. Cats).

module Categories.Category.CartesianClosed.Canonical {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level using (levelOfTerm)
open import Function using (flip)

open import Categories.Category.Cartesian 𝒞 using (Cartesian)
import Categories.Category.CartesianClosed 𝒞 as 𝒞-CC
open import Categories.Object.Exponential 𝒞 using (Exponential)
open import Categories.Object.Product 𝒞
open import Categories.Object.Terminal 𝒞 using (Terminal)
open import Categories.Morphism.Reasoning 𝒞

private
  open Category 𝒞
  open HomReasoning

  variable
    A B C : Obj
    f g h : A ⇒ B

-- A (canonical) cartesian closed category is a category with all
-- (canonical) products and exponentials
--
-- This presentation is equivalent to the one in
-- Categories.Category.CartesianClosed.CartesianClosed.
record CartesianClosed : Set (levelOfTerm 𝒞) where
  infixr 7 _×_
  infixr 9 _^_
  infix 10 ⟨_,_⟩

  field

    -- Canonical products

    ⊤    : Obj
    _×_  : Obj → Obj → Obj

    !     : A ⇒ ⊤
    π₁    : A × B ⇒ A
    π₂    : A × B ⇒ B
    ⟨_,_⟩ : C ⇒ A → C ⇒ B → C ⇒ A × B

    !-unique : (f : A ⇒ ⊤) → ! ≈ f

    π₁-comp  : π₁ ∘ ⟨ f , g ⟩ ≈ f
    π₂-comp  : π₂ ∘ ⟨ f , g ⟩ ≈ g

    ⟨,⟩-unique : ∀ {f g} {h : C ⇒ A × B} →
                 π₁ ∘ h ≈ f → π₂ ∘ h ≈ g → ⟨ f , g ⟩ ≈ h

  -- The above defines canonical finite products, making 𝒞 cartesian.

  ⊤-terminal : Terminal
  ⊤-terminal = record { ⊤-is-terminal = record { !-unique = !-unique } }

  ×-product : ∀ {A B} → Product A B
  ×-product {A} {B} =
    record { project₁ = π₁-comp; project₂ = π₂-comp; unique = ⟨,⟩-unique }

  isCartesian : Cartesian
  isCartesian = record
    { terminal = ⊤-terminal
    ; products = record { product = ×-product }
    }

  open Cartesian isCartesian public
    hiding (_×_; π₁; π₂; ⟨_,_⟩)
    renaming (⟨⟩-cong₂ to ⟨,⟩-resp-≈)

  field

    -- Canonical exponentials (w.r.t. the canonical products)

    _^_   : Obj → Obj → Obj
    eval  : B ^ A × A ⇒ B
    curry : C × A ⇒ B → C ⇒ B ^ A

    eval-comp  : eval ∘ (curry f ⁂ id) ≈ f

    curry-resp-≈ : f ≈ g → curry f ≈ curry g
    curry-unique : eval ∘ (f ⁂ id) ≈ g → f ≈ curry g

  -- The above defines canonical exponentials, making 𝒞 cartesian closed.
  --
  -- NOTE: below we use "⊗" to indicate "non-canonical" products.

  ^-exponential : ∀ {A B} → Exponential A B
  ^-exponential {A} {B} = record
    { B^A      = B ^ A
    ; product  = ×-product
    ; eval     = eval
    ; λg       = λ C⊗A f → curry (f ∘ repack ×-product C⊗A)
    ; β        = λ {C} C⊗A {g} →
      begin
        eval ∘ [ C⊗A ⇒ ×-product ] curry (g ∘ repack ×-product C⊗A) ×id
      ≈˘⟨ pullʳ [ ×-product ⇒ ×-product ]×∘⟨⟩ ⟩
        (eval ∘ (curry (g ∘ repack ×-product C⊗A) ⁂ id)) ∘ repack C⊗A ×-product
      ≈⟨ eval-comp ⟩∘⟨refl ⟩
        (g ∘ repack ×-product C⊗A) ∘ repack C⊗A ×-product
      ≈⟨ cancelʳ (repack∘repack≈id ×-product C⊗A) ⟩
        g
      ∎
    ; λ-unique = λ {C} C⊗A {g} {f} hyp →
      curry-unique (begin
        eval ∘ (f ⁂ id)
      ≈˘⟨ pullʳ [ C⊗A ⇒ ×-product ]×∘⟨⟩ ⟩
        (eval ∘ [ C⊗A ⇒ ×-product ] f ×id) ∘ repack ×-product C⊗A
      ≈⟨ hyp ⟩∘⟨refl ⟩
        g ∘ repack ×-product C⊗A
      ∎)
    }

module Equivalence where
  open 𝒞-CC using () renaming (CartesianClosed to CartesianClosed′)

  -- The two presentations of CCCs are equivalent

  fromCanonical : CartesianClosed → CartesianClosed′
  fromCanonical cc = record
    { cartesian = CartesianClosed.isCartesian cc
    ; exp       = CartesianClosed.^-exponential cc
    }

  toCanonical : CartesianClosed′ → CartesianClosed
  toCanonical cc = record
    { ⊤     = ⊤
    ; _×_   = _×_
    ; !     = !
    ; π₁    = π₁
    ; π₂    = π₂
    ; ⟨_,_⟩ = ⟨_,_⟩
    ; !-unique   = !-unique
    ; π₁-comp    = project₁
    ; π₂-comp    = project₂
    ; ⟨,⟩-unique = unique
    ; _^_   = _^_
    ; eval  = eval′
    ; curry = λg
    ; eval-comp    = β′
    ; curry-resp-≈ = λ-cong
    ; curry-unique = λ-unique′
    }
    where open CartesianClosed′ cc
