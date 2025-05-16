{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- Group objects in a cartesian category.
------------------------------------------------------------------------

open import Categories.Category
open import Categories.Category.Cartesian

module Categories.Object.Group {o ℓ e} {𝒞 : Category o ℓ e} (C : Cartesian 𝒞) where

open import Level

open import Categories.Category.BinaryProducts 𝒞 using (BinaryProducts)
open import Categories.Category.Cartesian.Monoidal
open import Categories.Object.Monoid (CartesianMonoidal.monoidal C)
open import Categories.Object.Terminal 𝒞

open Category 𝒞
open Cartesian C
module Π = BinaryProducts products
open BinaryProducts products using (_×_; _⁂_; ⟨_,_⟩)
open Terminal terminal

record IsGroup (G : Obj) : Set (ℓ ⊔ e) where
  -- any group object is also a monoid object
  field
    isMonoid : IsMonoid G

  open IsMonoid isMonoid public

  field
    -- inverse operation
    ι : G ⇒ G
    -- ι is in fact an inverse
    inverseˡ : η ∘ ! ≈ μ ∘ ⟨ ι , id ⟩
    inverseʳ : η ∘ ! ≈ μ ∘ ⟨ id , ι ⟩

record Group : Set (o ⊔ ℓ ⊔ e) where
  field
    Carrier : Obj
    isGroup : IsGroup Carrier

  open IsGroup isGroup public

  monoid : Monoid
  monoid = record { isMonoid = isMonoid }

open Group

record Group⇒ (G H : Group) : Set (ℓ ⊔ e) where
  field
    arr : Carrier G ⇒ Carrier H
    preserves-μ : arr ∘ μ G ≈ μ H ∘ (arr ⁂ arr)
    preserves-η : arr ∘ η G ≈ η H
    preserves-ι : arr ∘ ι G ≈ ι H ∘ arr
