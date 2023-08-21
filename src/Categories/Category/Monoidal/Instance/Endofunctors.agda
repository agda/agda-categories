{-# OPTIONS --without-K --safe #-}
module Categories.Category.Monoidal.Instance.Endofunctors {o ℓ e} where

-- Given a category C, the category of endofunctors on C is a monoidal category.

open import Data.Empty.Polymorphic using (⊥; ⊥-elim)
open import Data.Product using (_,_; uncurry′)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit.Polymorphic using (⊤)
open import Function using (case_of_; flip)
open import Level using (Lift; lift; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Categories.Morphism using (_≅_; Iso)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Cartesian.Monoidal using (module CartesianMonoidal)
open import Categories.Category.Core using (Category)
open import Categories.Category.Cocartesian using (Cocartesian)
open import Categories.Category.Construction.Functors using (Functors)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ₕ_)
open import Categories.Category.Monoidal using (Monoidal; monoidalHelper)
open import Categories.Category.Monoidal.Symmetric using (Symmetric; symmetricHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)

open import Categories.NaturalTransformation.NaturalIsomorphism
  using (NaturalIsomorphism; unitorˡ; unitorʳ; associator)

import Categories.Morphism.Reasoning as MR

Endofunctors : Category o ℓ e → Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) (o ⊔ e)
Endofunctors C = Functors C C

module _ where
  -- Conversion function from natural isomorphisms to isomorphisms in the functor category.
  ≃→≅ : ∀ {C D : Category o ℓ e}
      → {F G : Functor C D}
      → NaturalIsomorphism F G
      → Categories.Morphism._≅_ (Functors C D) F G
  ≃→≅ i = record
    { from = i.F⇒G
    ; to = i.F⇐G
    ; iso = record { isoˡ = λ {x} → Iso.isoˡ (i.iso x) ; isoʳ = λ {x} → Iso.isoʳ (i.iso x) }
    } where module i = NaturalIsomorphism i

module _ where
  Endofunctors-Monoidal : ∀ {C : Category o ℓ e} → Monoidal (Endofunctors C)
  Endofunctors-Monoidal {C} = record
    { ⊗ = record
      { F₀ = uncurry′ _∘F_
      ; F₁ = uncurry′ _∘ₕ_
      ; identity = λ { {F , G} →
        let module F = Functor F
            module G = Functor G in
          begin F.F₁ id ∘ id ≈⟨ F.identity ⟩∘⟨refl ⟩
                id ∘ id ≈⟨ identity² ⟩
                id ∎ }
      ; homomorphism = λ { {F , G} {F₂ , G₂} {F₃ , G₃} {f₁ , f₂} {g₁ , g₂} →
        let module F₃ = Functor F₃
            module F₂ = Functor F₂
            module G = Functor G
            module G₂ = Functor G₂
            module f₁ = NaturalTransformation f₁
            module f₂ = NaturalTransformation f₂
            module g₁ = NaturalTransformation g₁
            module g₂ = NaturalTransformation g₂ in
          begin
            F₃.₁ (g₂.η _ ∘ f₂.η _) ∘ g₁.η (G.₀ _) ∘ f₁.η (G.₀ _) ≈⟨ pushˡ F₃.homomorphism ⟩
            F₃.₁ (g₂.η _) ∘ F₃.₁ (f₂.η _) ∘ g₁.η (G.₀ _) ∘ f₁.η (G.₀ _) ≈⟨ refl⟩∘⟨ extendʳ (g₁.sym-commute _) ⟩
            F₃.₁ (g₂.η _) ∘ g₁.η (G₂.F₀ _) ∘ F₂.F₁ (f₂.η _) ∘ f₁.η (G.₀ _) ≈⟨ sym-assoc ⟩
            (F₃.₁ (g₂.η _) ∘ g₁.η (G₂.₀ _)) ∘ F₂.₁ (f₂.η _) ∘ f₁.η (G.₀ _) ∎ }
      ; F-resp-≈ = λ { {_} {E , D} (f≈₁g , f≈₂g) → Functor.F-resp-≈ E f≈₂g ⟩∘⟨ f≈₁g }
      }
    ; unit = idF
    ; unitorˡ = ≃→≅ unitorˡ
    ; unitorʳ = ≃→≅ unitorʳ
    ; associator = λ {X} {Y} {Z} → ≃→≅ (associator Z Y X)
    ; unitorˡ-commute-from = identityˡ
    ; unitorˡ-commute-to = λ { {f = f} →
        let module f = NaturalTransformation f in
        begin (id ∘ f.η _)        ≈⟨ identityˡ ⟩
              f.η _               ≈⟨ Equiv.sym identityʳ ⟩
              (f.η _ ∘ id)        ≈⟨ Equiv.sym identityʳ ⟩
              ((f.η _ ∘ id) ∘ id) ∎ }
    ; unitorʳ-commute-from = λ { {F} {G} {f = f} →
        let module G = Functor G in
        let module f = NaturalTransformation f in
        begin id ∘ _ ∘ f.η _ ≈⟨ identityˡ ⟩
              G.F₁ _ ∘ f.η _ ≈⟨ elimˡ G.identity ⟩
              f.η _          ≈⟨ Equiv.sym identityʳ ⟩
              f.η _ ∘ id ∎ }
    ; unitorʳ-commute-to = λ { {F} {G} {f = f} →
        let module G = Functor G in
        let module f = NaturalTransformation f in
        begin _ ∘ f.η _              ≈⟨ identityˡ ⟩
              f.η _                  ≈⟨ introˡ G.identity ⟩
              G.F₁ id ∘ f.η _        ≈⟨ Equiv.sym identityʳ ⟩
              (G.F₁ id ∘ f.η _) ∘ id ∎ }
    ; assoc-commute-from = λ { {F} {G} {f = f} {H} {I} {g = g} {J} {K} {h = h} →
        let module G = Functor G in
        let module H = Functor H in
        let module I = Functor I in
        let module J = Functor J in
        let module f = NaturalTransformation f in
        let module g = NaturalTransformation g in
        let module h = NaturalTransformation h in
        begin id ∘ (G.₁ (I.₁ (h.η _)) ∘ G.₁ (g.η (J.₀ _)) ∘ f.η (H.₀ (J.₀ _))) ≈⟨ identityˡ ⟩
              G.₁ (I.₁ (h.η _)) ∘ G.₁ (g.η (J.₀ _)) ∘ f.η (H.₀ (J.₀ _))        ≈⟨ pullˡ (Equiv.sym G.homomorphism) ⟩
              G.₁ (I.₁ (h.η _) ∘ g.η (J.₀ _)) ∘ f.η (H.₀ (J.₀ _))              ≈⟨ Equiv.sym identityʳ ⟩
              (G.₁ (I.₁ (h.η _) ∘ g.η (J.₀ _)) ∘ f.η (H.₀ (J.₀ _))) ∘ id       ∎ }
    ; assoc-commute-to = λ { {F} {G} {f = f} {H} {I} {g = g} {J} {K} {h = h} →
        let module G = Functor G in
        let module H = Functor H in
        let module I = Functor I in
        let module J = Functor J in
        let module f = NaturalTransformation f in
        let module g = NaturalTransformation g in
        let module h = NaturalTransformation h in
        begin id ∘ G.₁ (I.₁ (h.η _) ∘ g.η (J.₀ _)) ∘ f.η (H.₀ (J.₀ _)) ≈⟨ identityˡ ⟩
              G.₁ (I.₁ (h.η _) ∘ g.η (J.₀ _)) ∘ f.η (H.₀ (J.₀ _)) ≈⟨ pushˡ G.homomorphism ⟩
              G.₁ (I.₁ (h.η _)) ∘ G.₁ (g.η (J.₀ _)) ∘ f.η (H.₀ (J.₀ _)) ≈⟨ Equiv.sym identityʳ ⟩
              (G.₁ (I.₁ (h.η _)) ∘ G.₁ (g.η (J.₀ _)) ∘ f.η (H.₀ (J.₀ _))) ∘ id ∎ }
    ; triangle = identityʳ
    ; pentagon = λ { {X} {Y} {Z} →
        let module X = Functor X in
        begin (X.F₁ id ∘ id) ∘ id ∘ X.F₁ (Functor.F₁ Y (Functor.F₁ Z id)) ∘ id  ≈⟨ elimˡ X.identity ⟩∘⟨ identityˡ ⟩
              id ∘ X.F₁ (Functor.F₁ Y (Functor.F₁ Z id)) ∘ id ≈⟨ (refl⟩∘⟨ elimˡ (Functor.identity (X ∘F Y ∘F Z))) ⟩
              id ∘ id ∎ }
    } where open Category C
            open HomReasoning
            open MR C
