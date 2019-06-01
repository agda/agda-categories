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
    
open HomReasoning

module Switch (i : X ≅ Y) where
  open _≅_ i

  switch-fgˡ : ∀ {h : W ⇒ X} {k : W ⇒ Y} → (f ∘ h ≈ k) → (h ≈ g ∘ k)
  switch-fgˡ {h = h} {k} pf = begin
    h           ≈⟨ sym (cancelLeft isoˡ) ⟩
    g ∘ (f ∘ h) ≈⟨ ∘-resp-≈ʳ pf ⟩
    g ∘ k       ∎

  switch-gfˡ : ∀ {h : W ⇒ Y} {k : W ⇒ X} → (g ∘ h ≈ k) → (h ≈ f ∘ k)
  switch-gfˡ {h = h} {k} pf = begin
    h           ≈⟨ sym (cancelLeft isoʳ) ⟩
    f ∘ (g ∘ h) ≈⟨ ∘-resp-≈ʳ pf ⟩
    f ∘ k       ∎

  switch-fgʳ : ∀ {h : Y ⇒ W} {k : X ⇒ W} → (h ∘ f ≈ k) → (h ≈ k ∘ g)
  switch-fgʳ {h = h} {k} pf = begin
    h           ≈⟨ sym (cancelRight isoʳ) ⟩
    (h ∘ f) ∘ g ≈⟨ ∘-resp-≈ˡ pf ⟩
    k ∘ g       ∎

  switch-gfʳ : ∀ {h : X ⇒ W} {k : Y ⇒ W} → (h ∘ g ≈ k) → (h ≈ k ∘ f)
  switch-gfʳ {h = h} {k} pf = begin
    h           ≈⟨ sym (cancelRight isoˡ) ⟩
    (h ∘ g) ∘ f ≈⟨ ∘-resp-≈ˡ pf ⟩
    k ∘ f       ∎

open Switch public
