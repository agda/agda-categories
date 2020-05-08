{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (module Commutation) renaming (Category to Setoid-Category)
open import Categories.Category.Monoidal using (Monoidal)

module Categories.Enriched.NaturalTransformation
  {o ℓ e} {V : Setoid-Category o ℓ e} (M : Monoidal V) where

open import Level

open import Categories.Category.Monoidal.Properties M using (module Kelly's)
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Utilities M
open import Categories.Enriched.Category M using (Category; _[_,_])
open import Categories.Enriched.Category.Underlying M using (Underlying)
open import Categories.Enriched.Functor M using (Functor; UnderlyingFunctor; _∘F_)
  renaming (id to idF)
open import Categories.Morphism.Reasoning V
  using (pushˡ; pullˡ; cancelʳ; pullʳ; pushʳ; switch-tofromˡ; extendˡ; extendʳ)
import Categories.Morphism.IsoEquiv V as IsoEquiv
open import Categories.NaturalTransformation using (ntHelper)
  renaming (NaturalTransformation to Setoid-NT)

open Setoid-Category V using (_∘_; _⇒_; _≈_; assoc)
  renaming (Obj to ObjV; id to idV)
open Commutation V
open Monoidal M
open Shorthands

module _ {c d : Level} {C : Category c} {D : Category d} where

  private
    module D = Category D using (⊚; id; unitʳ; unitˡ; ⊚-assoc-var)
    module U = Underlying D using (_⇒_; _∘_)

  record NaturalTransformation (F G : Functor C D) : Set (ℓ ⊔ e ⊔ c) where
    eta-equality
    private
      module F = Functor F using (₀; ₁)
      module G = Functor G using (₀; ₁)

    field
      comp    : ∀ X → F.₀ X U.⇒ G.₀ X
      commute : ∀ {X Y} →
        [ C [ X , Y ] ⇒ D [ F.₀ X , G.₀ Y ] ]⟨
          unitorˡ.to      ⇒⟨ unit ⊗₀ C [ X , Y ] ⟩
          comp Y ⊗₁ F.₁   ⇒⟨ D [ F.₀ Y , G.₀ Y ] ⊗₀ D [ F.₀ X , F.₀ Y ] ⟩
          D.⊚
        ≈ unitorʳ.to      ⇒⟨ C [ X , Y ] ⊗₀ unit ⟩
          G.₁ ⊗₁ comp X   ⇒⟨ D [ G.₀ X , G.₀ Y ] ⊗₀ D [ F.₀ X , G.₀ X ] ⟩
          D.⊚
        ⟩

    -- A shorthand for the components of a natural transformation:
    --
    --   α [ X ]
    --
    -- is the X-component of the family { αₓ } of "morphisms" that
    -- forms the natural transformation α.

    infixl 16 _[_]

    _[_] = comp

  open NaturalTransformation
  open D hiding (id)
  open IsoEquiv._≃_

  id : ∀ {F : Functor C D} → NaturalTransformation F F
  id {F} = record
    { comp    = λ _ → D.id
    ; commute = λ {X} {Y} → begin
      ⊚ ∘ D.id ⊗₁ F.₁ ∘ λ⇐                ≈⟨ refl⟩∘⟨ pushˡ serialize₁₂ ⟩
      ⊚ ∘ D.id ⊗₁ idV ∘ idV ⊗₁ F.₁ ∘ λ⇐   ≈⟨ pullˡ unitˡ ⟩
      unitorˡ.from ∘ idV ⊗₁ F.₁ ∘ λ⇐      ≈⟨ pullˡ unitorˡ-commute-from ⟩
      (F.₁ ∘ unitorˡ.from) ∘ λ⇐           ≈⟨ cancelʳ unitorˡ.isoʳ ⟩
      F.₁                                 ≈˘⟨ cancelʳ unitorʳ.isoʳ ⟩
      (F.₁ ∘ unitorʳ.from) ∘ ρ⇐           ≈˘⟨ pullˡ unitorʳ-commute-from ⟩
      unitorʳ.from ∘ F.₁ ⊗₁ idV ∘ ρ⇐      ≈˘⟨ pullˡ unitʳ ⟩
      ⊚ ∘ idV ⊗₁ D.id ∘ F.₁ ⊗₁ idV ∘ ρ⇐   ≈˘⟨ refl⟩∘⟨ pushˡ serialize₂₁ ⟩
      ⊚ ∘ F.₁ ⊗₁ D.id ∘ ρ⇐                ∎
    }
    where module F = Functor F using (₁)

  infixr 9 _∘ᵥ_

  -- Vertical composition

  _∘ᵥ_ : {F G H : Functor C D} →
         NaturalTransformation G H → NaturalTransformation F G →
         NaturalTransformation F H
  _∘ᵥ_ {F} {G} {H} α β = record
    { comp    = λ X → α [ X ] U.∘ β [ X ]
    ; commute = λ {X} {Y} →
      begin
        ⊚ ∘ (⊚ ∘ α [ Y ] ⊗₁ β [ Y ] ∘ λ⇐) ⊗₁ F.₁ ∘ λ⇐
      ≈⟨ helper (α [ Y ]) (β [ Y ]) F.₁ λ⇐ ⟩
        ⊚ ∘ α [ Y ] ⊗₁ (⊚ ∘ β [ Y ] ⊗₁ F.₁ ∘ λ⇐) ∘ λ⇐
      ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ commute β ⟩∘⟨refl ⟩
        ⊚ ∘ α [ Y ] ⊗₁ (⊚ ∘ G.₁ ⊗₁ β [ X ] ∘ ρ⇐) ∘ λ⇐
      ≈˘⟨ helper (α [ Y ]) G.₁ (β [ X ]) ρ⇐ ⟩
        ⊚ ∘ (⊚ ∘ α [ Y ] ⊗₁ G.₁ ∘ λ⇐) ⊗₁ β [ X ] ∘ ρ⇐
      ≈⟨ refl⟩∘⟨ commute α ⟩⊗⟨refl ⟩∘⟨refl ⟩
        ⊚ ∘ (⊚ ∘ H.₁ ⊗₁ α [ X ] ∘ ρ⇐) ⊗₁ β [ X ] ∘ ρ⇐
      ≈˘⟨ refl⟩∘⟨ assoc ⟩⊗⟨refl ⟩∘⟨refl ⟩
        ⊚ ∘ ((⊚ ∘ H.₁ ⊗₁ α [ X ]) ∘ ρ⇐) ⊗₁ β [ X ] ∘ ρ⇐
      ≈⟨ refl⟩∘⟨ split₁ʳ ⟩∘⟨refl ⟩
        ⊚ ∘ ((⊚ ∘ H.₁ ⊗₁ α [ X ]) ⊗₁ β [ X ] ∘ ρ⇐ ⊗₁ idV) ∘ ρ⇐
      ≈⟨ pullˡ (pullˡ ⊚-assoc-var) ⟩
        ((⊚ ∘ H.₁ ⊗₁ (⊚ ∘ α [ X ] ⊗₁ β [ X ]) ∘ α⇒) ∘ ρ⇐ ⊗₁ idV) ∘ ρ⇐
      ≈˘⟨ pushʳ (pushʳ (switch-tofromˡ associator (to-≈ triangle-iso))) ⟩∘⟨refl ⟩
        (⊚ ∘ H.₁ ⊗₁ (⊚ ∘ α [ X ] ⊗₁ β [ X ]) ∘ idV ⊗₁ λ⇐) ∘ ρ⇐
      ≈˘⟨ pushʳ (split₂ʳ ⟩∘⟨refl) ⟩
        ⊚ ∘ H.₁ ⊗₁ ((⊚ ∘ α [ X ] ⊗₁ β [ X ]) ∘ λ⇐) ∘ ρ⇐
      ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ assoc ⟩∘⟨refl ⟩
        ⊚ ∘ H.₁ ⊗₁ (⊚ ∘ α [ X ] ⊗₁ β [ X ] ∘ λ⇐) ∘ ρ⇐
      ∎
    }
    where
      module F = Functor F using (₁)
      module G = Functor G using (₁)
      module H = Functor H using (₁)

      helper : ∀ {X₁ X₂ X₃ X₄ Y₁ Y₂ Z} (f : X₃ U.⇒ X₄) (g : Y₁ ⇒ D [ X₂ , X₃ ])
                 (h : Y₂ ⇒ D [ X₁ , X₂ ]) (i : Z ⇒ Y₁ ⊗₀ Y₂) →
               ⊚ ∘ (⊚ ∘ f ⊗₁ g ∘ λ⇐) ⊗₁ h ∘ i  ≈
               ⊚ ∘ f ⊗₁ (⊚ ∘ g ⊗₁ h ∘ i) ∘ λ⇐
      helper f g h i = begin
          ⊚ ∘ (⊚ ∘ f ⊗₁ g ∘ λ⇐) ⊗₁ h ∘ i
        ≈˘⟨ refl⟩∘⟨ assoc ⟩⊗⟨refl ⟩∘⟨refl ⟩
          ⊚ ∘ ((⊚ ∘ f ⊗₁ g) ∘ λ⇐) ⊗₁ h ∘ i
        ≈⟨ refl⟩∘⟨ split₁ʳ ⟩∘⟨refl ⟩
          ⊚ ∘ ((⊚ ∘ f ⊗₁ g) ⊗₁ h ∘ λ⇐ ⊗₁ idV) ∘ i
        ≈⟨ pullˡ (pullˡ ⊚-assoc-var) ⟩
          ((⊚ ∘ f ⊗₁ (⊚ ∘ g ⊗₁ h) ∘ α⇒) ∘ λ⇐ ⊗₁ idV) ∘ i
        ≈˘⟨ pushʳ (pushʳ (switch-tofromˡ associator (to-≈ Kelly's.coherence-iso₁))) ⟩∘⟨refl ⟩
          (⊚ ∘ f ⊗₁ (⊚ ∘ g ⊗₁ h) ∘ λ⇐) ∘ i
        ≈⟨ pullʳ (pullʳ unitorˡ-commute-to) ⟩
          ⊚ ∘ f ⊗₁ (⊚ ∘ g ⊗₁ h) ∘ idV ⊗₁ i ∘ λ⇐
        ≈˘⟨ refl⟩∘⟨ pushˡ split₂ʳ ⟩
          ⊚ ∘ f ⊗₁ ((⊚ ∘ g ⊗₁ h) ∘ i) ∘ λ⇐
        ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ assoc ⟩∘⟨refl ⟩
          ⊚ ∘ f ⊗₁ (⊚ ∘ g ⊗₁ h ∘ i) ∘ λ⇐
        ∎

  -- A V-enriched natural transformation induces an ordinary natural
  -- transformation on the underlying functors.
  -- Note: essentially all of the typechecking time for this file goes
  -- into Typing.TypeSig for this one function.

  UnderlyingNT : {F G : Functor C D} → NaturalTransformation F G →
                 Setoid-NT {c} {ℓ} {e} {d} {ℓ} {e}
                     (UnderlyingFunctor {c} {d} {C} {D} F)
                     (UnderlyingFunctor {c} {d} {C} {D} G)
  UnderlyingNT {F} {G} α = ntHelper (record
    { η       = comp α
    ; commute = λ {X Y} f →
      begin
        ⊚ ∘ α [ Y ] ⊗₁ (F.₁ ∘ f) ∘ λ⇐          ≈⟨ refl⟩∘⟨ split₂ʳ ⟩∘⟨refl ⟩
        ⊚ ∘ (α [ Y ] ⊗₁ F.₁ ∘ idV ⊗₁ f) ∘ λ⇐   ≈˘⟨ refl⟩∘⟨ extendˡ unitorˡ-commute-to ⟩
        ⊚ ∘ (α [ Y ] ⊗₁ F.₁ ∘ λ⇐) ∘ f          ≈⟨ extendʳ (commute α) ⟩
        ⊚ ∘ (G.₁ ⊗₁ α [ X ] ∘ ρ⇐) ∘ f          ≈⟨ refl⟩∘⟨ extendˡ unitorʳ-commute-to ⟩
        ⊚ ∘ (G.₁ ⊗₁ α [ X ] ∘ f ⊗₁ idV) ∘ ρ⇐   ≈˘⟨ refl⟩∘⟨ split₁ʳ ⟩∘⟨refl ⟩
        ⊚ ∘ (G.₁ ∘ f) ⊗₁ α [ X ] ∘ ρ⇐          ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ to-≈ Kelly's.coherence-iso₃ ⟩
        ⊚ ∘ (G.₁ ∘ f) ⊗₁ α [ X ] ∘ λ⇐          ∎
    })
    where
      module F = Functor F using (₁)
      module G = Functor G using (₁)

  module UnderlyingNT {F} {G} α = Setoid-NT (UnderlyingNT {F} {G} α)

module _ {c d e} {C : Category c} {D : Category d} {E : Category e} where

  private
    module C = Category C
    module D = Category D
    module E = Category E
    module U = Underlying E
  open NaturalTransformation

  infixr 9 _∘ₕ_ _∘ˡ_ _∘ʳ_

  -- Left- and right-hand composition with a functor

  _∘ˡ_ : {G H : Functor C D} (F : Functor D E) →
         NaturalTransformation G H → NaturalTransformation (F ∘F G) (F ∘F H)
  _∘ˡ_ {G} {H} F α = record
    { comp    = λ X → F.₁ ∘ α [ X ]
    ; commute = λ {X Y} →
      begin
        E.⊚ ∘ (F.₁ ∘ α [ Y ]) ⊗₁ (F.₁ ∘ G.₁) ∘ λ⇐    ≈⟨ refl⟩∘⟨ pushˡ ⊗-distrib-over-∘ ⟩
        E.⊚ ∘ (F.₁ ⊗₁ F.₁) ∘ (α [ Y ] ⊗₁ G.₁) ∘ λ⇐   ≈˘⟨ extendʳ F.homomorphism ⟩
        F.₁ ∘ D.⊚ ∘ (α [ Y ] ⊗₁ G.₁) ∘ λ⇐            ≈⟨ refl⟩∘⟨ commute α ⟩
        F.₁ ∘ D.⊚ ∘ (H.₁ ⊗₁ α [ X ]) ∘ ρ⇐            ≈⟨ extendʳ F.homomorphism ⟩
        E.⊚ ∘ (F.₁ ⊗₁ F.₁) ∘ (H.₁ ⊗₁ α [ X ]) ∘ ρ⇐   ≈˘⟨ refl⟩∘⟨ pushˡ ⊗-distrib-over-∘ ⟩
        E.⊚ ∘ (F.₁ ∘ H.₁) ⊗₁ (F.₁ ∘ α [ X ]) ∘ ρ⇐    ∎
    }
    where
      module F = Functor F
      module G = Functor G
      module H = Functor H

  _∘ʳ_ : {G H : Functor D E} →
         NaturalTransformation G H → (F : Functor C D) →
         NaturalTransformation (G ∘F F) (H ∘F F)
  _∘ʳ_ {G} {H} α F = record
    { comp    = λ X → α [ F.₀ X ]
    ; commute = λ {X Y} →
      begin
        E.⊚ ∘ α [ F.₀ Y ] ⊗₁ (G.₁ ∘ F.₁) ∘ λ⇐          ≈⟨ refl⟩∘⟨ split₂ʳ ⟩∘⟨refl ⟩
        E.⊚ ∘ (α [ F.₀ Y ] ⊗₁ G.₁ ∘ idV ⊗₁ F.₁) ∘ λ⇐   ≈˘⟨ refl⟩∘⟨ extendˡ unitorˡ-commute-to ⟩
        E.⊚ ∘ (α [ F.₀ Y ] ⊗₁ G.₁ ∘ λ⇐) ∘ F.₁          ≈⟨ extendʳ (commute α) ⟩
        E.⊚ ∘ (H.₁ ⊗₁ α [ F.₀ X ] ∘ ρ⇐) ∘ F.₁          ≈⟨ refl⟩∘⟨ extendˡ unitorʳ-commute-to ⟩
        E.⊚ ∘ (H.₁ ⊗₁ α [ F.₀ X ] ∘ F.₁ ⊗₁ idV) ∘ ρ⇐   ≈˘⟨ refl⟩∘⟨ split₁ʳ ⟩∘⟨refl ⟩
        E.⊚ ∘ (H.₁ ∘ F.₁) ⊗₁ α [ F.₀ X ] ∘ ρ⇐          ∎
    }
    where
      module F = Functor F
      module G = Functor G
      module H = Functor H

  -- Horizontal composition

  _∘ₕ_ : {H I : Functor D E} {F G : Functor C D} →
          NaturalTransformation H I → NaturalTransformation F G →
          NaturalTransformation (H ∘F F) (I ∘F G)
  _∘ₕ_ {_} {I} {F} {_} α β = (I ∘ˡ β) ∘ᵥ (α ∘ʳ F)
