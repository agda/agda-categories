{-# OPTIONS --without-K --safe #-}

open import Categories.Adjoint
open import Categories.Category
open import Categories.Functor renaming (id to idF)

-- The crude monadicity theorem. This proof is based off of the version
-- provided in "Sheaves In Geometry and Logic" by Maclane and Moerdijk.
module Categories.Adjoint.Monadic.Crude {o ℓ e o′ ℓ′ e′} {𝒞 : Category o ℓ e} {𝒟 : Category o′ ℓ′ e′}
                                        {L : Functor 𝒞 𝒟} {R : Functor 𝒟 𝒞} (adjoint : L ⊣ R) where

open import Level
open import Function using (_$_)
open import Data.Product using (Σ-syntax; _,_)

open import Categories.Adjoint.Properties
open import Categories.Adjoint.Monadic
open import Categories.Adjoint.Monadic.Properties
open import Categories.Category.Equivalence using (StrongEquivalence)
open import Categories.Category.Equivalence.Properties using (pointwise-iso-equivalence)
open import Categories.Functor.Properties
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)
open import Categories.NaturalTransformation
open import Categories.Monad

open import Categories.Diagram.Coequalizer
open import Categories.Diagram.ReflexivePair

open import Categories.Adjoint.Construction.EilenbergMoore
open import Categories.Category.Construction.EilenbergMoore
open import Categories.Category.Construction.Properties.EilenbergMoore

open import Categories.Morphism
open import Categories.Morphism.Notation
open import Categories.Morphism.Properties
import Categories.Morphism.Reasoning as MR

private
  module L = Functor L
  module R = Functor R

  module 𝒞 = Category 𝒞
  module 𝒟 = Category 𝒟

  module adjoint = Adjoint adjoint

  T : Monad 𝒞
  T = adjoint⇒monad adjoint

  𝒞ᵀ : Category _ _ _
  𝒞ᵀ = EilenbergMoore T

  Comparison : Functor 𝒟 𝒞ᵀ
  Comparison = ComparisonF adjoint

  module Comparison = Functor Comparison

  open Coequalizer

-- We could do this with limits, but this is far easier.
PreservesReflexiveCoequalizers : (F : Functor 𝒟 𝒞) → Set _
PreservesReflexiveCoequalizers F = ∀ {A B} {f g : 𝒟 [ A , B ]} → ReflexivePair 𝒟 f g → (coeq : Coequalizer 𝒟 f g) → IsCoequalizer 𝒞 (F.F₁ f) (F.F₁ g) (F.F₁ (arr coeq))
  where
    module F = Functor F

module _ {F : Functor 𝒟 𝒞} (preserves-reflexive-coeq : PreservesReflexiveCoequalizers F) where
  open Functor F

  -- Unfortunately, we need to prove that the 'coequalize' arrows are equal as a lemma
  preserves-coequalizer-unique : ∀ {A B C} {f g : 𝒟 [ A , B ]} {h : 𝒟 [ B , C ]} {eq : 𝒟 [ 𝒟 [ h ∘ f ] ≈ 𝒟 [ h ∘ g ] ]}
                                 → (reflexive-pair : ReflexivePair 𝒟 f g) → (coe : Coequalizer 𝒟 f g)
                                 →  𝒞 [ F₁ (coequalize coe eq) ≈ IsCoequalizer.coequalize (preserves-reflexive-coeq reflexive-pair coe) ([ F ]-resp-square eq) ]
  preserves-coequalizer-unique reflexive-pair coe = IsCoequalizer.unique (preserves-reflexive-coeq reflexive-pair coe) (F-resp-≈ (universal coe) ○ homomorphism)
    where
      open 𝒞.HomReasoning


-- If 𝒟 has coequalizers of reflexive pairs, then the comparison functor has a left adjoint.
module _ (has-reflexive-coequalizers : ∀ {A B} {f g : 𝒟 [ A , B ]} → ReflexivePair 𝒟 f g → Coequalizer 𝒟 f g) where

  private
    reflexive-pair : (M : Module T) → ReflexivePair 𝒟 (L.F₁ (Module.action M)) (adjoint.counit.η (L.₀ (Module.A M)))
    reflexive-pair M = record
      { s = L.F₁ (adjoint.unit.η (Module.A M))
      ; isReflexivePair = record
        { sectionₗ = begin
          𝒟 [ L.F₁ (Module.action M) ∘ L.F₁ (adjoint.unit.η (Module.A M)) ] ≈˘⟨ L.homomorphism ⟩
          L.F₁ (𝒞 [ Module.action M ∘ adjoint.unit.η (Module.A M) ] )       ≈⟨ L.F-resp-≈ (Module.identity M) ⟩
          L.F₁ 𝒞.id                                                         ≈⟨ L.identity ⟩
          𝒟.id                                                              ∎
        ; sectionᵣ = begin
          𝒟 [ adjoint.counit.η (L.₀ (Module.A M)) ∘ L.F₁ (adjoint.unit.η (Module.A M)) ] ≈⟨ adjoint.zig ⟩
          𝒟.id ∎
        }
      }
      where
        open 𝒟.HomReasoning

    -- The key part of the proof. As we have all reflexive coequalizers, we can create the following coequalizer.
    -- We can think of this as identifying the action of the algebra lifted to a "free" structure
    -- and the counit of the adjunction, as the unit of the adjunction (also lifted to the "free structure") is a section of both.
    has-coequalizer : (M : Module T) → Coequalizer 𝒟 (L.F₁ (Module.action M)) (adjoint.counit.η (L.₀ (Module.A M)))
    has-coequalizer M = has-reflexive-coequalizers (reflexive-pair M)

    module Comparison⁻¹ = Functor (Comparison⁻¹ adjoint has-coequalizer)
    module Comparison⁻¹⊣Comparison = Adjoint (Comparison⁻¹⊣Comparison adjoint has-coequalizer)

    -- We have one interesting coequalizer in 𝒞 built out of a T-module's action.
    coequalizer-action : (M : Module T) → Coequalizer 𝒞 (R.F₁ (L.F₁ (Module.action M))) (R.F₁ (adjoint.counit.η (L.₀ (Module.A M))))
    coequalizer-action M = record
      { arr = Module.action M
      ; isCoequalizer = record
        { equality = Module.commute M
        ; coequalize = λ {X} {h} eq → 𝒞 [ h ∘ adjoint.unit.η (Module.A M) ]
        ; universal = λ {C} {h} {eq} → begin
          h                                                                                                       ≈⟨ introʳ adjoint.zag ○ 𝒞.sym-assoc ⟩
          𝒞 [ 𝒞 [ h ∘ R.F₁ (adjoint.counit.η (L.₀ (Module.A M))) ] ∘ adjoint.unit.η (R.F₀ (L.F₀ (Module.A M))) ] ≈⟨ pushˡ (⟺ eq) ⟩
          𝒞 [ h ∘ 𝒞 [ R.F₁ (L.F₁ (Module.action M)) ∘ adjoint.unit.η (R.F₀ (L.F₀ (Module.A M))) ] ]              ≈⟨ pushʳ (adjoint.unit.sym-commute (Module.action M)) ⟩
          𝒞 [ 𝒞 [ h ∘ adjoint.unit.η (Module.A M) ] ∘ Module.action M ]                                          ∎
        ; unique = λ {X} {h} {i} {eq} eq′ → begin
          i ≈⟨ introʳ (Module.identity M) ⟩
          𝒞 [ i ∘ 𝒞 [ Module.action M ∘ adjoint.unit.η (Module.A M) ] ] ≈⟨ pullˡ (⟺ eq′) ⟩
          𝒞 [ h ∘ adjoint.unit.η (Module.A M) ] ∎
        }
      }
      where
        open 𝒞.HomReasoning
        open MR 𝒞

  -- If 'R' preserves reflexive coequalizers, then the unit of the adjunction is a pointwise isomorphism
  unit-iso : PreservesReflexiveCoequalizers R → (X : Module T) → Σ[ h ∈ 𝒞ᵀ [ Comparison.F₀ (Comparison⁻¹.F₀ X) , X ] ] (Iso 𝒞ᵀ (Comparison⁻¹⊣Comparison.unit.η X) h)
  unit-iso preserves-reflexive-coeq X =
    let
        coequalizerˣ = has-coequalizer X
        coequalizerᴿˣ = ((IsCoequalizer⇒Coequalizer 𝒞 (preserves-reflexive-coeq (reflexive-pair X) (has-coequalizer X))))
        coequalizer-iso = up-to-iso 𝒞 (coequalizer-action X) coequalizerᴿˣ
        module coequalizer-iso = _≅_ coequalizer-iso
        open 𝒞
        open 𝒞.HomReasoning
        open MR 𝒞
        α = record
          { arr = coequalizer-iso.to
          ; commute = begin
            coequalizer-iso.to ∘ R.F₁ (adjoint.counit.η _)                                                                                                                ≈⟨ introʳ (R.F-resp-≈ L.identity ○ R.identity) ⟩
            (coequalizer-iso.to ∘ R.F₁ (adjoint.counit.η _)) ∘ R.F₁ (L.F₁ 𝒞.id)                                                                                           ≈⟨ pushʳ (R.F-resp-≈ (L.F-resp-≈ (⟺ coequalizer-iso.isoʳ)) ○ R.F-resp-≈ L.homomorphism ○ R.homomorphism) ⟩
            ((coequalizer-iso.to ∘ R.F₁ (adjoint.counit.η _)) ∘ R.F₁ (L.F₁ (R.F₁ (arr coequalizerˣ) ∘ adjoint.unit.η _))) ∘ R.F₁ (L.F₁ coequalizer-iso.to)                ≈⟨ (refl⟩∘⟨ (R.F-resp-≈ L.homomorphism ○ R.homomorphism)) ⟩∘⟨refl ⟩
            ((coequalizer-iso.to ∘ R.F₁ (adjoint.counit.η _)) ∘  R.F₁ (L.F₁ (R.F₁ (arr coequalizerˣ))) ∘ R.F₁ (L.F₁ (adjoint.unit.η _))) ∘ R.F₁ (L.F₁ coequalizer-iso.to) ≈⟨ center ([ R ]-resp-square (adjoint.counit.commute _)) ⟩∘⟨refl ⟩
            ((coequalizer-iso.to ∘ (R.F₁ (arr coequalizerˣ) ∘ R.F₁ (adjoint.counit.η (L.F₀ _))) ∘ R.F₁ (L.F₁ (adjoint.unit.η _))) ∘ R.F₁ (L.F₁ coequalizer-iso.to))       ≈⟨ (refl⟩∘⟨ cancelʳ (⟺ R.homomorphism ○ R.F-resp-≈ adjoint.zig ○ R.identity)) ⟩∘⟨refl  ⟩
            (coequalizer-iso.to ∘ R.F₁ (arr coequalizerˣ)) ∘ R.F₁ (L.F₁ coequalizer-iso.to)                                                                               ≈˘⟨ universal coequalizerᴿˣ ⟩∘⟨refl ⟩
            Module.action X ∘ R.F₁ (L.F₁ coequalizer-iso.to) ∎
          }
    in α , record { isoˡ = coequalizer-iso.isoˡ ; isoʳ = coequalizer-iso.isoʳ }

  -- If 'R' preserves reflexive coequalizers and reflects isomorphisms, then the counit of the adjunction is a pointwise isomorphism.
  counit-iso : PreservesReflexiveCoequalizers R → Conservative R → (X : 𝒟.Obj) → Σ[ h ∈ 𝒟 [ X , Comparison⁻¹.F₀ (Comparison.F₀ X) ] ] Iso 𝒟 (Comparison⁻¹⊣Comparison.counit.η X) h
  counit-iso preserves-reflexive-coeq conservative X =
    let coequalizerᴿᴷˣ = IsCoequalizer⇒Coequalizer 𝒞 (preserves-reflexive-coeq (reflexive-pair (Comparison.F₀ X)) (has-coequalizer (Comparison.F₀ X)))
        coequalizerᴷˣ = has-coequalizer (Comparison.F₀ X)
        coequalizer-iso = up-to-iso 𝒞 coequalizerᴿᴷˣ (coequalizer-action (Comparison.F₀ X))
        module coequalizer-iso = _≅_ coequalizer-iso
        open 𝒞.HomReasoning
        open 𝒞.Equiv
    in conservative (Iso-resp-≈ 𝒞 coequalizer-iso.iso (⟺ (preserves-coequalizer-unique {R} preserves-reflexive-coeq (reflexive-pair (Comparison.F₀ X)) coequalizerᴷˣ)) refl)

  -- Now, for the final result. Both the unit and counit of the adjunction between the comparison functor and it's inverse are isomorphisms,
  -- so therefore they form natural isomorphism. Therfore, we have an equivalence of categories.
  crude-monadicity : PreservesReflexiveCoequalizers R → Conservative R → StrongEquivalence 𝒞ᵀ 𝒟
  crude-monadicity preserves-reflexlive-coeq conservative = record
    { F = Comparison⁻¹ adjoint has-coequalizer
    ; G = Comparison
    ; weak-inverse = pointwise-iso-equivalence (Comparison⁻¹⊣Comparison adjoint has-coequalizer)
                                               (counit-iso preserves-reflexlive-coeq conservative)
                                               (unit-iso preserves-reflexlive-coeq)
    }
