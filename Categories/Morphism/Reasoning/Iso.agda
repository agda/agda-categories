{-# OPTIONS --without-K --safe #-}
open import Categories.Category

{-
  Various combinators for working with Isomorphisms in the
  context of morphism equalities
  both for Category (Switch) and IsGroupoid (GroupoidR)
-}

module Categories.Morphism.Reasoning.Iso {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level
open import Function renaming (id to idᶠ; _∘_ to _∙_)

open import Categories.Category.Groupoid using (IsGroupoid)
open import Categories.Morphism 𝒞
open import Categories.Morphism.Reasoning.Core 𝒞

open import Relation.Binary hiding (_⇒_)

open Category 𝒞
private
  variable
    A B C D X Y : Obj
    f g h k : X ⇒ Y

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

  cancel-fromʳ : h ∘ from ≈ k ∘ from → h ≈ k
  cancel-fromʳ {h = h} {k = k} pf = begin
    h               ≈˘⟨ cancelʳ isoʳ ⟩
    (h ∘ from) ∘ to ≈⟨ pf ⟩∘⟨refl ⟩
    (k ∘ from) ∘ to ≈⟨ cancelʳ isoʳ ⟩
    k               ∎

  cancel-fromˡ : from ∘ h ≈ from ∘ k → h ≈ k
  cancel-fromˡ {h = h} {k = k} pf = begin
    h               ≈˘⟨ cancelˡ isoˡ ⟩
    to ∘ (from ∘ h) ≈⟨ refl⟩∘⟨ pf ⟩
    to ∘ (from ∘ k) ≈⟨ cancelˡ isoˡ ⟩
    k               ∎

  cancel-toʳ : h ∘ to ≈ k ∘ to → h ≈ k
  cancel-toʳ {h = h} {k = k} pf = begin
    h               ≈˘⟨ cancelʳ isoˡ ⟩
    (h ∘ to) ∘ from ≈⟨ pf ⟩∘⟨refl ⟩
    (k ∘ to) ∘ from ≈⟨ cancelʳ isoˡ ⟩
    k               ∎

  cancel-toˡ : to ∘ h ≈ to ∘ k → h ≈ k
  cancel-toˡ {h = h} {k = k} pf = begin
    h               ≈˘⟨ cancelˡ isoʳ ⟩
    from ∘ (to ∘ h) ≈⟨ refl⟩∘⟨ pf ⟩
    from ∘ (to ∘ k) ≈⟨ cancelˡ isoʳ ⟩
    k               ∎

open Switch public

module _ where
  open _≅_

  -- We can flip an iso f in a commuting triangle, like so:
  --
  --          f                       f⁻¹
  --    A --------> B            A <-------- B
  --     \    ≃    /              \    ≃    /
  --      \       /                \       /
  --     g \     / h     ===>     g \     / h
  --        \   /                    \   /
  --         V V                      V V
  --          C                        C
  --
  flip-iso : (f : A ≅ B) {g : A ⇒ C} {h : B ⇒ C} →
             g ≈ h ∘ from f → g ∘ to f ≈ h
  flip-iso f tr₁ = sym (switch-fromtoʳ f (sym tr₁))

  -- Consider two commuting squares
  --
  --         f₁                      f₂
  --    A -------> B            A -------> B
  --    |          |            |          |
  --    |          |            |          |
  --  ≃ | h₁       | h₂       ≃ | h₁       | h₂
  --    |          |            |          |
  --    V          V            V          V
  --    C -------> D            C -------> D
  --         g₁                      g₂
  --
  -- with h₁ an isomorphism.  Then g₁ ≈ g₂ if f₁ ≈ f₂.

  push-eq : (h₁ : A ≅ C) {f₁ f₂ : A ⇒ B} {g₁ g₂ : C ⇒ D} {h₂ : B ⇒ D} →
            CommutativeSquare f₁ (from h₁) h₂ g₁ →
            CommutativeSquare f₂ (from h₁) h₂ g₂ →
            f₁ ≈ f₂ → g₁ ≈ g₂
  push-eq h₁ {f₁} {f₂} {g₁} {g₂} {h₂} sq₁ sq₂ hyp = begin
    g₁                  ≈˘⟨ flip-iso h₁ sq₁ ⟩
    (h₂ ∘ f₁) ∘ to h₁   ≈⟨ ∘-resp-≈ˡ (∘-resp-≈ʳ hyp) ⟩
    (h₂ ∘ f₂) ∘ to h₁   ≈⟨ flip-iso h₁ sq₂ ⟩
    g₂                  ∎

-- conjugates
module _ (i : A ≅ B) (j : X ≅ Y) where
  private
    module i = _≅_ i
    module j = _≅_ j

  conjugate-from : f ∘ i.from ≈ j.from ∘ g → j.to ∘ f ≈ g ∘ i.to
  conjugate-from {f = f} {g = g} eq = begin
    j.to ∘ f                   ≈⟨ introʳ i.isoʳ ⟩
    (j.to ∘ f) ∘ i.from ∘ i.to ≈⟨ center eq ⟩
    j.to ∘ (j.from ∘ g) ∘ i.to ≈⟨ center⁻¹ j.isoˡ refl ⟩
    id ∘ g ∘ i.to              ≈⟨ identityˡ ⟩
    g ∘ i.to                   ∎

  conjugate-to : j.to ∘ f ≈ g ∘ i.to → f ∘ i.from ≈ j.from ∘ g
  conjugate-to {f = f} {g = g} eq = begin
    f ∘ i.from                   ≈⟨ introˡ j.isoʳ ⟩
    (j.from ∘ j.to) ∘ f ∘ i.from ≈⟨ center eq ⟩
    j.from ∘ (g ∘ i.to) ∘ i.from ≈⟨ center⁻¹ refl i.isoˡ ⟩
    (j.from ∘ g) ∘ id            ≈⟨ identityʳ ⟩
    j.from ∘ g                   ∎

module GroupoidR (G : IsGroupoid 𝒞) where
  open IsGroupoid G using (_⁻¹; iso; equiv-obj)

  switch-fromtoˡ′ : f ∘ h ≈ k → h ≈ f ⁻¹ ∘ k
  switch-fromtoˡ′ = switch-fromtoˡ (equiv-obj _)

  switch-tofromˡ′ : f ⁻¹ ∘ h ≈ k → h ≈ f ∘ k
  switch-tofromˡ′ = switch-tofromˡ (equiv-obj _)

  switch-fromtoʳ′ : h ∘ f ≈ k → h ≈ k ∘ f ⁻¹
  switch-fromtoʳ′ = switch-fromtoʳ (equiv-obj _)

  switch-tofromʳ′ : h ∘ f ⁻¹ ≈ k → h ≈ k ∘ f
  switch-tofromʳ′ = switch-tofromʳ (equiv-obj _)
