{-# OPTIONS --without-K --safe #-}

open import Categories.Bicategory using (Bicategory)

-- The 1-cell dual (op) and 2-cell dual (co) of a given bicategory.

module Categories.Bicategory.Opposite where

open import Data.Product using (_,_)

open import Categories.Bicategory.Extras using (module Extras)
open import Categories.Category using (Category)
import Categories.Category.Cartesian as Cartesian
import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning as MorphismReasoning
open import Categories.Category.Product using (Swap)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (NaturalIsomorphism; niHelper)

-- There several ways to dualize a bicategory:
--
--  * flip the 1-cells (op C), or
--  * flip the 2-cells (co C).
--  * flip both (coop C).
--
-- We implement all three.

module _ {o ℓ e t} (C : Bicategory o ℓ e t) where

  open Bicategory C
  open Extras C
  open Shorthands
  private
    module MR {A} {B} where
      open Morphism          (hom A B) public using (module ≅)
      open MorphismReasoning (hom A B) public using (switch-tofromʳ)
  open MR

  -- The 1-cell dual of C.
  --
  -- NOTE.  The definition here is specialized to the particular choice
  -- of tensor product (cartesian) and braiding (swap) used in the
  -- definition of Bicategories.  We could instead have defined the
  -- `enriched' field using the generic `op' operation defined in
  -- Categories.Enriched.Category.Opposite, but that would have resulted
  -- in much more complicated proofs of the triangle and pentagon
  -- identities.  That's because the definition of associativity and the
  -- unit laws in the generic opposite enriched category has to work for
  -- any choice of braiding and is therefore more involved.  When these
  -- laws become natural isomorphism in the definition of Bicategories,
  -- they turn into long chains consisting of mostly identity morphisms
  -- that make the types of the triangle and pentagon identities
  -- enormous.  We can avoid this by specializing the definitions of the
  -- associators and unitors below.
  --
  -- Note also that this version of `op' is almost a (definitional)
  -- involution.  The problematic fields are the triangle and pentagon
  -- identities which are not involutive on the nose.  This could be
  -- fixed by adding additional fields (in the style of `sym-assoc' in
  -- Category).  To also support `co` and `coop` would require two more
  -- variants of each equation, so there would be quite a lot of
  -- redundancy in the end.

  op : Bicategory o ℓ e t
  op = record
    { enriched = record
      { Obj = Obj
      ; hom = λ A B → hom B A
      ; id  = id
      ; ⊚   = ⊚ ∘F Swap
      ; ⊚-assoc = niHelper (record
        { η       = λ{ ((f , g) , h) → ⊚-assoc.⇐.η ((h , g) , f) }
        ; η⁻¹     = λ{ ((f , g) , h) → ⊚-assoc.⇒.η ((h , g) , f) }
        ; commute = λ{ ((α , β) , γ) → ⊚-assoc.⇐.commute ((γ , β) , α) }
        ; iso     = λ _ → record
          { isoˡ = ⊚-assoc.iso.isoʳ _ ; isoʳ = ⊚-assoc.iso.isoˡ _ }
        })
      ; unitˡ = niHelper (record
        { η       = λ{ (_ , g) → unitʳ.⇒.η (g , _) }
        ; η⁻¹     = λ{ (_ , g) → unitʳ.⇐.η (g , _) }
        ; commute = λ{ (_ , β) → unitʳ.⇒.commute (β , _) }
        ; iso     = λ{ (_ , g) → record
          { isoˡ = unitʳ.iso.isoˡ (g , _) ; isoʳ = unitʳ.iso.isoʳ (g , _) } }
        })
      ; unitʳ = niHelper (record
        { η       = λ{ (f , _) → unitˡ.⇒.η (_ , f) }
        ; η⁻¹     = λ{ (f , _) → unitˡ.⇐.η (_ , f) }
        ; commute = λ{ (α , _) → unitˡ.⇒.commute (_ , α) }
        ; iso     = λ{ (f , _) → record
          { isoˡ = unitˡ.iso.isoˡ (_ , f) ; isoʳ = unitˡ.iso.isoʳ (_ , f) } }
        })
      }
    ; triangle = λ {_ _ _ f g} → begin
        ρ⇒ ◁ g ∘ᵥ α⇐   ≈˘⟨ switch-tofromʳ (≅.sym associator) triangle ⟩
        f ▷ λ⇒         ∎
    ; pentagon = λ {_ _ _ _ _ f g h i} → begin
        α⇐ ◁ i ∘ᵥ α⇐ ∘ᵥ f ▷ α⇐     ≈˘⟨ hom.assoc ⟩
        (α⇐ ◁ i ∘ᵥ α⇐) ∘ᵥ f ▷ α⇐   ≈⟨ pentagon-inv ⟩
        α⇐ ∘ᵥ α⇐                   ∎
    }
    where open hom.HomReasoning

  -- The 2-cell dual of C.

  co : Bicategory o ℓ e t
  co = record
    { enriched = record
      { Obj     = Obj
      ; hom     = λ A B → Category.op (hom A B)
      ; id      = Functor.op id
      ; ⊚       = Functor.op ⊚
      ; ⊚-assoc = NaturalIsomorphism.op′ ⊚-assoc
      ; unitˡ   = NaturalIsomorphism.op′ unitˡ
      ; unitʳ   = NaturalIsomorphism.op′ unitʳ
      }
    ; triangle  = triangle-inv
    ; pentagon  = pentagon-inv
    }

-- The combined 1- and 2-cell dual of C.

coop : ∀ {o ℓ e t} → Bicategory o ℓ e t → Bicategory o ℓ e t
coop C = co (op C)
