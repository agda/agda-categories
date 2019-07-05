{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Categories.Square.Iso {o ℓ e} (C : Category o ℓ e) where

open import Level
open import Function renaming (id to idᶠ; _∘_ to _∙_)

open import Categories.Category.Groupoid
open import Categories.Morphism C
open import Categories.Square.Core C

open import Relation.Binary hiding (_⇒_)

open Category C
private
  variable
    X Y Z W : Obj
    f g h k : X ⇒ Y

open HomReasoning

module Switch (i : X ≅ Y) where
  open _≅_ i

  switch-fromtoˡ : from ∘ h ≈ k → h ≈ to ∘ k
  switch-fromtoˡ {h = h} {k = k} pf = begin
    h               ≈⟨ sym (cancelˡ isoˡ) ⟩
    to ∘ (from ∘ h) ≈⟨ ∘-resp-≈ʳ pf ⟩
    to ∘ k          ∎

  switch-tofromˡ : to ∘ h ≈ k → h ≈ from ∘ k
  switch-tofromˡ {h = h} {k = k} pf = begin
    h               ≈⟨ sym (cancelˡ isoʳ) ⟩
    from ∘ (to ∘ h) ≈⟨ ∘-resp-≈ʳ pf ⟩
    from ∘ k        ∎

  switch-fromtoʳ : h ∘ from ≈ k → h ≈ k ∘ to
  switch-fromtoʳ {h = h} {k = k} pf = begin
    h               ≈⟨ sym (cancelʳ isoʳ) ⟩
    (h ∘ from) ∘ to ≈⟨ ∘-resp-≈ˡ pf ⟩
    k ∘ to          ∎

  switch-tofromʳ : h ∘ to ≈ k → h ≈ k ∘ from
  switch-tofromʳ {h = h} {k = k} pf = begin
    h               ≈⟨ sym (cancelʳ isoˡ) ⟩
    (h ∘ to) ∘ from ≈⟨ ∘-resp-≈ˡ pf ⟩
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
