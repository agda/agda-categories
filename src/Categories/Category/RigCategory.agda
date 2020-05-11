{-# OPTIONS --without-K --safe #-}
-- Actually, we're cheating (for expediency); this is
-- Symmetric Rig, not just Rig.
open import Categories.Category

module Categories.Category.RigCategory {o ℓ e} (C : Category o ℓ e) where

open import Level
open import Data.Fin.Base using () renaming (zero to 0F; suc to sucF)
open import Data.Product using (_,_)

open import Categories.Functor.Core
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Braided
open import Categories.Category.Monoidal.Symmetric
open import Categories.NaturalTransformation.NaturalIsomorphism
open import Categories.NaturalTransformation using (_∘ᵥ_; _∘ₕ_; _∘ˡ_; _∘ʳ_; NaturalTransformation)
open import Categories.Morphism C

-- Should probably split out Distributive Category out and make this be 'over' that.
record RigCategory {M⊎ M× : Monoidal C} (S⊎ : Symmetric M⊎)
   (S× : Symmetric M×) : Set (o ⊔ ℓ ⊔ e) where

  private
    module C = Category C

  open C hiding (_≈_)
  open Commutation C
  module M⊎ = Monoidal M⊎
  module M× = Monoidal M×
  module S⊎ = Symmetric S⊎
  module S× = Symmetric S×
  open M⊎ renaming (_⊗₀_ to _⊕₀_; _⊗₁_ to _⊕₁_)
  open M×

  private
    0C : C.Obj
    0C = M⊎.unit
    1C : C.Obj
    1C = M×.unit

  private
    B⊗ : ∀ {X Y} → X ⊗₀ Y ⇒ Y ⊗₀ X
    B⊗ {X} {Y} = S×.braiding.⇒.η (X , Y)
    B⊕ : ∀ {X Y} → X ⊕₀ Y ⇒ Y ⊕₀ X
    B⊕ {X} {Y} = S⊎.braiding.⇒.η (X , Y)

  field
    annₗ : ∀ {X} → 0C ⊗₀ X ≅ 0C
    annᵣ : ∀ {X} → X ⊗₀ 0C ≅ 0C
    distribₗ : ∀ {X Y Z} → X ⊗₀ (Y ⊕₀ Z) ≅ (X ⊗₀ Y) ⊕₀ (X ⊗₀ Z)
    distribᵣ : ∀ {X Y Z} → (X ⊕₀ Y) ⊗₀ Z ≅ (X ⊗₀ Z) ⊕₀ (Y ⊗₀ Z)

  private
    λ* : ∀ {X} → 0C ⊗₀ X ⇒ 0C
    λ* {X} = _≅_.from (annₗ {X})
    ρ* : ∀ {X} → X ⊗₀ 0C ⇒ 0C
    ρ* {X} = _≅_.from (annᵣ {X})
    module dl {X} {Y} {Z} = _≅_ (distribₗ {X} {Y} {Z})
    module dr {X} {Y} {Z} = _≅_ (distribᵣ {X} {Y} {Z})
    ⊗λ⇒ = M×.unitorˡ.from
    ⊗λ⇐ = M×.unitorˡ.to
    ⊗ρ⇒ = M×.unitorʳ.from
    ⊗ρ⇐ = M×.unitorʳ.to
    ⊗α⇒ = M×.associator.from
    ⊗α⇐ = M×.associator.to
    ⊕λ⇒ = M⊎.unitorˡ.from
    ⊕λ⇐ = M⊎.unitorˡ.to
    ⊕ρ⇒ = M⊎.unitorʳ.from
    ⊕ρ⇐ = M⊎.unitorʳ.to
    ⊕α⇒ = M⊎.associator.from
    ⊕α⇐ = M⊎.associator.to


  -- need II, IX, X, XV
  -- choose I, IV, VI, XI, XIII, XIX, XXIII and (XVI, XVII)
  field
    laplazaI : ∀ {A B C} →
      [ A ⊗₀ (B ⊕₀ C) ⇒ (A ⊗₀ C) ⊕₀ (A ⊗₀ B) ]⟨
        dl.from        ⇒⟨ (A ⊗₀ B) ⊕₀ (A ⊗₀ C) ⟩
        B⊕
      ≈
        C.id ⊗₁ B⊕    ⇒⟨ A ⊗₀ (C ⊕₀ B) ⟩
        dl.from
      ⟩
    laplazaII : ∀ {A B C} →
      [ (A ⊕₀ B) ⊗₀ C ⇒ (C ⊗₀ A) ⊕₀ (C ⊗₀ B) ]⟨
        B⊗             ⇒⟨ C ⊗₀ (A ⊕₀ B) ⟩
        dl.from
      ≈
        dr.from        ⇒⟨ (A ⊗₀ C) ⊕₀ (B ⊗₀ C) ⟩
        B⊗ ⊕₁ B⊗
      ⟩
    laplazaIV : {A B C D : Obj} →
      [ (A ⊕₀ B ⊕₀ C) ⊗₀ D ⇒ ((A ⊗₀ D) ⊕₀ (B ⊗₀ D)) ⊕₀ (C ⊗₀ D) ]⟨
         dr.from            ⇒⟨ (A ⊗₀ D) ⊕₀ ((B ⊕₀ C) ⊗₀ D) ⟩
         C.id ⊕₁ dr.from   ⇒⟨ (A ⊗₀ D) ⊕₀ ((B ⊗₀ D) ⊕₀ (C ⊗₀ D)) ⟩
         ⊕α⇐
      ≈
         ⊕α⇐ ⊗₁ C.id       ⇒⟨ ((A ⊕₀ B) ⊕₀ C) ⊗₀ D ⟩
         dr.from            ⇒⟨ ((A ⊕₀ B) ⊗₀ D) ⊕₀ (C ⊗₀ D) ⟩
         dr.from ⊕₁ C.id
      ⟩

    laplazaVI : {A B C D : Obj} →
      [ A ⊗₀ B ⊗₀ (C ⊕₀ D) ⇒ ((A ⊗₀ B) ⊗₀ C) ⊕₀ ((A ⊗₀ B) ⊗₀ D) ]⟨
          C.id ⊗₁ dl.from   ⇒⟨ A ⊗₀ ((B ⊗₀ C) ⊕₀ (B ⊗₀ D)) ⟩
          dl.from            ⇒⟨ (A ⊗₀ B ⊗₀ C) ⊕₀ (A ⊗₀ B ⊗₀ D) ⟩
          ⊗α⇐ ⊕₁ ⊗α⇐
      ≈
        ⊗α⇐                ⇒⟨ (A ⊗₀ B) ⊗₀ (C ⊕₀ D) ⟩
        dl.from
      ⟩
    laplazaIX : ∀ {A B C D} → [ (A ⊕₀ B) ⊗₀ (C ⊕₀ D) ⇒ (((A ⊗₀ C) ⊕₀ (B ⊗₀ C)) ⊕₀ (A ⊗₀ D)) ⊕₀ (B ⊗₀ D) ]⟨
        dr.from                ⇒⟨ (A ⊗₀ (C ⊕₀ D)) ⊕₀ (B ⊗₀ (C ⊕₀ D)) ⟩
        dl.from ⊕₁ dl.from     ⇒⟨ ((A ⊗₀ C) ⊕₀ (A ⊗₀ D)) ⊕₀ ((B ⊗₀ C) ⊕₀ (B ⊗₀ D)) ⟩
        ⊕α⇐                    ⇒⟨ (((A ⊗₀ C) ⊕₀ (A ⊗₀ D)) ⊕₀ (B ⊗₀ C)) ⊕₀ (B ⊗₀ D) ⟩
        ⊕α⇒ ⊕₁ C.id           ⇒⟨ ((A ⊗₀ C) ⊕₀ ((A ⊗₀ D) ⊕₀ (B ⊗₀ C))) ⊕₀ (B ⊗₀ D) ⟩
        (C.id ⊕₁ B⊕) ⊕₁ C.id  ⇒⟨ ((A ⊗₀ C) ⊕₀ ((B ⊗₀ C) ⊕₀ (A ⊗₀ D))) ⊕₀ (B ⊗₀ D) ⟩
        ⊕α⇐ ⊕₁ C.id
      ≈
        dl.from                ⇒⟨ ((A ⊕₀ B) ⊗₀ C) ⊕₀ ((A ⊕₀ B) ⊗₀ D) ⟩
        dr.from ⊕₁ dr.from     ⇒⟨ ((A ⊗₀ C) ⊕₀ (B ⊗₀ C)) ⊕₀ ((A ⊗₀ D) ⊕₀ (B ⊗₀ D))  ⟩
        ⊕α⇐
      ⟩
    laplazaX : [ 0C ⊗₀ 0C ⇒ 0C ]⟨ λ* ≈ ρ* ⟩
    laplazaXI : ∀ {A B} →
      [ 0C ⊗₀ (A ⊕₀ B) ⇒ 0C ]⟨
        dl.from   ⇒⟨ (0C ⊗₀ A) ⊕₀ (0C ⊗₀ B) ⟩
        λ* ⊕₁ λ*  ⇒⟨ 0C ⊕₀ 0C ⟩
        ⊕λ⇒
      ≈
        λ*
      ⟩
    laplazaXIII : [ 0C ⊗₀ 1C ⇒ 0C ]⟨ ⊗ρ⇒ ≈ λ* ⟩
    laplazaXV : ∀ {A : Obj} →
      [ A ⊗₀ 0C ⇒ 0C ]⟨
        ρ*
      ≈
        B⊗ ⇒⟨ 0C ⊗₀ A ⟩
        λ*
      ⟩
    laplazaXVI : ∀ {A B} → [ 0C ⊗₀ (A ⊗₀ B) ⇒ 0C ]⟨
        ⊗α⇐        ⇒⟨ (0C ⊗₀ A) ⊗₀ B ⟩
        λ* ⊗₁ C.id  ⇒⟨ 0C ⊗₀ B ⟩
        λ*
      ≈
        λ*
      ⟩
    laplazaXVII : ∀ {A B} → [ A ⊗₀ (0C ⊗₀ B) ⇒ 0C ]⟨
        ⊗α⇐        ⇒⟨ (A ⊗₀ 0C) ⊗₀ B ⟩
        ρ* ⊗₁ C.id ⇒⟨ 0C ⊗₀ B ⟩
        λ*
      ≈
        C.id ⊗₁ λ* ⇒⟨ A ⊗₀ 0C ⟩
        ρ*
      ⟩
    laplazaXIX : ∀ {A B} → [ A ⊗₀ (0C ⊕₀ B) ⇒ A ⊗₀ B ]⟨
        dl.from     ⇒⟨ (A ⊗₀ 0C) ⊕₀ (A ⊗₀ B) ⟩
        ρ* ⊕₁ C.id  ⇒⟨ 0C ⊕₀ (A ⊗₀ B) ⟩
        ⊕λ⇒
      ≈
        C.id ⊗₁ ⊕λ⇒
      ⟩
    laplazaXXIII : ∀ {A B} → [ 1C ⊗₀ (A ⊕₀ B) ⇒ (A ⊕₀ B) ]⟨
        ⊗λ⇒
      ≈
        dl.from ⇒⟨ (1C ⊗₀ A) ⊕₀ (1C ⊗₀ B) ⟩
        ⊗λ⇒ ⊕₁ ⊗λ⇒
      ⟩
