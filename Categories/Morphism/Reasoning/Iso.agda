{-# OPTIONS --without-K --safe #-}
open import Categories.Category

{-
  Various combinators for working with Isomorphisms in the
  context of morphism equalities
  both for Category (Switch) and Groupoid (GroupoidR)
-}

module Categories.Morphism.Reasoning.Iso {o ℓ e} (C : Category o ℓ e) where

open import Level
open import Function renaming (id to idᶠ; _∘_ to _∙_)

open import Categories.Category.Groupoid
open import Categories.Morphism C
open import Categories.Morphism.Reasoning.Core C

open import Relation.Binary hiding (_⇒_)

open Category C
private
  variable
    X Y : Obj
    f h k : X ⇒ Y

open HomReasoning

module Switch (i : X ≅ Y) where
  open _≅_ i

  switch-fromtoˡ : from ∘ h ≈ k → h ≈ to ∘ k
  switch-fromtoˡ {h = h} {k = k} pf = begin
    h               ≈˘⟨ cancelˡ isoˡ ⟩
    to ∘ (from ∘ h) ≈⟨ refl⟩∘⟨ pf ⟩
    to ∘ k          ∎

  switch-tofromˡ : to ∘ h ≈ k → h ≈ from ∘ k
  switch-tofromˡ {h = h} {k = k} pf = begin
    h               ≈˘⟨ cancelˡ isoʳ ⟩
    from ∘ (to ∘ h) ≈⟨ refl⟩∘⟨ pf ⟩
    from ∘ k        ∎

  switch-fromtoʳ : h ∘ from ≈ k → h ≈ k ∘ to
  switch-fromtoʳ {h = h} {k = k} pf = begin
    h               ≈˘⟨ cancelʳ isoʳ ⟩
    (h ∘ from) ∘ to ≈⟨ pf ⟩∘⟨refl ⟩
    k ∘ to          ∎

  switch-tofromʳ : h ∘ to ≈ k → h ≈ k ∘ from
  switch-tofromʳ {h = h} {k = k} pf = begin
    h               ≈˘⟨ cancelʳ isoˡ ⟩
    (h ∘ to) ∘ from ≈⟨ pf ⟩∘⟨refl ⟩
    k ∘ from        ∎

open Switch public


module GroupoidR (G : Groupoid C) where
  open Groupoid G using (_⁻¹; iso; equiv-obj)

  switch-fromtoˡ′ : f ∘ h ≈ k → h ≈ f ⁻¹ ∘ k
  switch-fromtoˡ′ = switch-fromtoˡ (equiv-obj _)

  switch-tofromˡ′ : f ⁻¹ ∘ h ≈ k → h ≈ f ∘ k
  switch-tofromˡ′ = switch-tofromˡ (equiv-obj _)

  switch-fromtoʳ′ : h ∘ f ≈ k → h ≈ k ∘ f ⁻¹
  switch-fromtoʳ′ = switch-fromtoʳ (equiv-obj _)

  switch-tofromʳ′ : h ∘ f ⁻¹ ≈ k → h ≈ k ∘ f
  switch-tofromʳ′ = switch-tofromʳ (equiv-obj _)
