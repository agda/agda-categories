{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Categories.Square.Iso {o ℓ e} (C : Category o ℓ e) where

open import Level
open import Function renaming (id to idᶠ; _∘_ to _∙_)

open import Categories.Morphisms C
open import Categories.Square.Core C

open import Relation.Binary hiding (_⇒_)

open Category C
private
  variable
    X Y Z W : Obj
    h k : X ⇒ Y
    
open HomReasoning

module Switch (i : X ≅ Y) where
  open _≅_ i

  switch-fromtoˡ : from ∘ h ≈ k → h ≈ to ∘ k
  switch-fromtoˡ {h = h} {k = k} pf = begin
    h               ≈⟨ sym (cancelLeft isoˡ) ⟩
    to ∘ (from ∘ h) ≈⟨ ∘-resp-≈ʳ pf ⟩
    to ∘ k          ∎

  switch-tofromˡ : to ∘ h ≈ k → h ≈ from ∘ k
  switch-tofromˡ {h = h} {k = k} pf = begin
    h               ≈⟨ sym (cancelLeft isoʳ) ⟩
    from ∘ (to ∘ h) ≈⟨ ∘-resp-≈ʳ pf ⟩
    from ∘ k        ∎

  switch-fromtoʳ : h ∘ from ≈ k → h ≈ k ∘ to
  switch-fromtoʳ {h = h} {k = k} pf = begin
    h               ≈⟨ sym (cancelRight isoʳ) ⟩
    (h ∘ from) ∘ to ≈⟨ ∘-resp-≈ˡ pf ⟩
    k ∘ to          ∎

  switch-tofromʳ : h ∘ to ≈ k → h ≈ k ∘ from
  switch-tofromʳ {h = h} {k = k} pf = begin
    h               ≈⟨ sym (cancelRight isoˡ) ⟩
    (h ∘ to) ∘ from ≈⟨ ∘-resp-≈ˡ pf ⟩
    k ∘ from        ∎

open Switch public
