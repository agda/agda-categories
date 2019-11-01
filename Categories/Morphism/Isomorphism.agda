{-# OPTIONS --without-K --safe #-}
open import Categories.Category

-- Properties of isomorphisms

module Categories.Morphism.Isomorphism {o ℓ e} (𝒞 : Category o ℓ e) where

import Categories.Category.Construction.Core as Core
open import Categories.Category.Groupoid using (IsGroupoid)
import Categories.Category.Groupoid.Properties as GroupoidProps
import Categories.Morphism as Morphism
import Categories.Morphism.Properties as MorphismProps
import Categories.Morphism.IsoEquiv as IsoEquiv
import Categories.Morphism.Reasoning as MR

open Core 𝒞 using (Core; Core-isGroupoid; CoreGroupoid)
open Morphism 𝒞
open MorphismProps 𝒞
open IsoEquiv 𝒞 using (_≃_; ⌞_⌟)

open Category 𝒞

private
  module MCore where
    open IsGroupoid    Core-isGroupoid public
    open MorphismProps Core public
    open Morphism      Core public
    open GroupoidProps CoreGroupoid public

  variable
    A B C D E F : Obj

open MCore using () renaming (_∘_ to _∘ᵢ_) public

CommutativeIso = IsGroupoid.CommutativeSquare Core-isGroupoid

module _ where
  open _≅_

  -- projecting isomorphism commutations to morphism commutations

  project-triangle : {g : A ≅ B} {f : C ≅ A} {h : C ≅ B} → g ∘ᵢ f ≃ h → from g ∘ from f ≈ from h
  project-triangle = _≃_.from-≈

  project-square : {g : A ≅ B} {f : C ≅ A} {i : D ≅ B} {h : C ≅ D} → g ∘ᵢ f ≃ i ∘ᵢ h → from g ∘ from f ≈ from i ∘ from h
  project-square = _≃_.from-≈

  -- direct lifting from morphism commutations to isomorphism commutations

  lift-triangle : {f : A ≅ B} {g : C ≅ A} {h : C ≅ B} → from f ∘ from g ≈ from h → f ∘ᵢ g ≃ h
  lift-triangle = ⌞_⌟

  lift-square : {f : A ≅ B} {g : C ≅ A} {h : D ≅ B} {i : C ≅ D} → from f ∘ from g ≈ from h ∘ from i → f ∘ᵢ g ≃ h ∘ᵢ i
  lift-square = ⌞_⌟

  lift-pentagon : {f : A ≅ B} {g : C ≅ A} {h : D ≅ C} {i : E ≅ B} {j : D ≅ E} →
                   from f ∘ from g ∘ from h ≈ from i ∘ from j → f ∘ᵢ g ∘ᵢ h ≃ i ∘ᵢ j
  lift-pentagon = ⌞_⌟

  open MR Core
  open MCore using (_⁻¹)
  open MCore.HomReasoning
  open MR.GroupoidR _ Core-isGroupoid

  squares×≃⇒≃ : {f f′ : A ≅ B} {g : A ≅ C} {h : B ≅ D} {i i′ : C ≅ D} →
                CommutativeIso f g h i → CommutativeIso f′ g h i′ → i ≃ i′ → f ≃ f′
  squares×≃⇒≃ sq₁ sq₂ eq = MCore.isos×≈⇒≈ eq helper₁ (MCore.≅.sym helper₂) sq₁ sq₂
    where
      helper₁ = record { iso = MCore.iso }
      helper₂ = record { iso = MCore.iso }

  -- imagine a triangle prism, if all the sides and the top face commute, the bottom face commute.
  triangle-prism : {i′ : A ≅ B} {f′ : C ≅ A} {h′ : C ≅ B} {i : D ≅ E} {j : D ≅ A}
    {k : E ≅ B} {f : F ≅ D} {g : F ≅ C} {h : F ≅ E} →
    i′ ∘ᵢ f′ ≃ h′ →
    CommutativeIso i j k i′ → CommutativeIso f g j f′ → CommutativeIso h g k h′ →
    i ∘ᵢ f ≃ h
  triangle-prism {i′ = i′} {f′} {_} {i} {_} {k} {f} {g} {_} eq sq₁ sq₂ sq₃ =
    squares×≃⇒≃ glued sq₃ eq
    where
      glued : CommutativeIso (i ∘ᵢ f) g k (i′ ∘ᵢ f′)
      glued = sym (glue (sym sq₁) (sym sq₂))

  elim-triangleˡ : {f : A ≅ B} {g : C ≅ A} {h : D ≅ C} {i : D ≅ B} {j : D ≅ A} →
                   f ∘ᵢ g ∘ᵢ h ≃ i → f ∘ᵢ j ≃ i → g ∘ᵢ h ≃ j
  elim-triangleˡ perim tri = MCore.mono _ _ (perim ○ ⟺ tri)

  elim-triangleˡ′ : {f : A ≅ B} {g : C ≅ A} {h : D ≅ C} {i : D ≅ B} {j : C ≅ B} →
                    f ∘ᵢ g ∘ᵢ h ≃ i → j ∘ᵢ h ≃ i → f ∘ᵢ g ≃ j
  elim-triangleˡ′ {f = f} {g} {h} {i} {j} perim tri = MCore.epi _ _ ( begin
    (f ∘ᵢ g) ∘ᵢ h ≈⟨ MCore.assoc ⟩
    f ∘ᵢ g ∘ᵢ h   ≈⟨ perim ⟩
    i             ≈˘⟨ tri ⟩
    j ∘ᵢ h        ∎ )

  cut-squareʳ : {g : A ≅ B} {f : A ≅ C} {h : B ≅ D} {i : C ≅ D} {j : B ≅ C} →
                CommutativeIso g f h i → i ∘ᵢ j ≃ h → j ∘ᵢ g ≃ f
  cut-squareʳ {g = g} {f = f} {h = h} {i = i} {j = j} sq tri = begin
    j ∘ᵢ g            ≈⟨ switch-fromtoˡ′ {f = i} {h = j} {k = h} tri ⟩∘⟨ refl ⟩
    (i ⁻¹ ∘ᵢ h) ∘ᵢ g  ≈⟨ MCore.assoc ⟩
    i ⁻¹ ∘ᵢ h ∘ᵢ g    ≈˘⟨ switch-fromtoˡ′ {f = i} {h = f} {k = h ∘ᵢ g} (sym sq) ⟩
    f                 ∎
