{-# OPTIONS --without-K --safe #-}

open import Categories.Adjoint
open import Categories.Category
open import Categories.Functor

-- The crude monadicity theorem.
module Categories.Adjoint.Monadic.Crude {o ℓ e o′ ℓ′ e′} {𝒞 : Category o ℓ e} {𝒟 : Category o′ ℓ′ e′}
                                        {L : Functor 𝒞 𝒟} {R : Functor 𝒟 𝒞} (adjoint : L ⊣ R) where

open import Level
open import Function using (_$_)

open import Categories.Adjoint.Properties
open import Categories.Adjoint.Monadic
open import Categories.NaturalTransformation.NaturalIsomorphism
open import Categories.NaturalTransformation
open import Categories.Monad

open import Categories.Diagram.Coequalizer
open import Categories.Diagram.ReflexivePair

open import Categories.Category.Construction.EilenbergMoore
open import Categories.Category.Construction.Properties.EilenbergMoore

open import Categories.Morphism
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

-- If 𝒟 has coequalizers of reflexive pairs, then the comparison functor has a left adjoint.
module _ (has-reflexive-coequalizers : ∀ {A B} {f g : 𝒟 [ A , B ]} → ReflexivePair 𝒟 f g → Coequalizer 𝒟 f g) where

  -- The key part of the proof. As we have all reflexive coequalizers, we can create the following coequalizer.
  -- We can think of this as identifying the action of the algebra lifted to a "free" structure
  -- and the counit of the adjunction, as the unit of the adjunction (also lifted to the "free structure") is a section of both.
  coeq : (M : Module T) → Coequalizer 𝒟 (L.F₁ (Module.action M)) (adjoint.counit.η (L.₀ (Module.A M)))
  coeq M = has-reflexive-coequalizers record
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

  -- If we have coequalizers of reflexive pairs, then we can define an "inverse" to the comparison functor.
  Comparison⁻¹ : Functor 𝒞ᵀ 𝒟
  Comparison⁻¹ = record
    { F₀ = λ M → obj (coeq M)
    ; F₁ = λ {M} {N} α → coequalize (coeq M) $ begin
      𝒟 [ 𝒟 [ arr (coeq N) ∘ L.F₁ (Module⇒.arr α) ] ∘ L.F₁ (Module.action M) ]                             ≈⟨ pullʳ (⟺ L.homomorphism) ⟩
      𝒟 [ arr (coeq N) ∘ L.F₁ (𝒞 [ Module⇒.arr α ∘ Module.action M ]) ]                                    ≈⟨ refl⟩∘⟨ L.F-resp-≈ (Module⇒.commute α) ⟩
      𝒟 [ arr (coeq N) ∘ L.F₁ (𝒞 [ Module.action N ∘ R.F₁ (L.F₁ (Module⇒.arr α)) ]) ]                      ≈⟨ refl⟩∘⟨ L.homomorphism ⟩
      𝒟 [ arr (coeq N) ∘ 𝒟 [ L.F₁ (Module.action N) ∘ L.F₁ (R.F₁ (L.F₁ (Module⇒.arr α))) ] ]               ≈⟨ pullˡ (equality (coeq N)) ⟩
      𝒟 [ 𝒟 [ arr (coeq N) ∘ adjoint.counit.η (L.F₀ (Module.A N)) ] ∘ L.F₁ (R.F₁ (L.F₁ (Module⇒.arr α))) ] ≈⟨ extendˡ (adjoint.counit.commute (L.F₁ (Module⇒.arr α))) ⟩
      𝒟 [ 𝒟 [ arr (coeq N) ∘ L.F₁ (Module⇒.arr α) ] ∘ adjoint.counit.η (L.₀ (Module.A M)) ]                ∎
    ; identity = λ {A} → ⟺ $ unique (coeq A) $ begin
      𝒟 [ arr (coeq A) ∘ L.F₁ 𝒞.id ] ≈⟨ refl⟩∘⟨ L.identity ⟩
      𝒟 [ arr (coeq A) ∘ 𝒟.id ]      ≈⟨ id-comm ⟩
      𝒟 [ 𝒟.id ∘ arr (coeq A) ]      ∎
    ; homomorphism = λ {X} {Y} {Z} {f} {g} → ⟺ $ unique (coeq X) $ begin
      𝒟 [ arr (coeq Z) ∘ L.F₁ (𝒞 [ Module⇒.arr g ∘ Module⇒.arr f ]) ]        ≈⟨ 𝒟.∘-resp-≈ʳ L.homomorphism ○ 𝒟.sym-assoc ⟩
      𝒟 [ 𝒟 [ arr (coeq Z) ∘ L.F₁ (Module⇒.arr g) ] ∘ L.F₁ (Module⇒.arr f) ] ≈⟨ universal (coeq Y) ⟩∘⟨refl ⟩
      𝒟 [ 𝒟 [ coequalize (coeq Y) _ ∘ arr (coeq Y) ] ∘ L.F₁ (Module⇒.arr f) ] ≈⟨ extendˡ (universal (coeq X)) ⟩
      𝒟 [ 𝒟 [ coequalize (coeq Y) _ ∘ coequalize (coeq X) _ ] ∘ arr (coeq X) ] ∎
    ; F-resp-≈ = λ {A} {B} {f} {g} eq → unique (coeq A) $ begin
      𝒟 [ arr (coeq B) ∘ L.F₁ (Module⇒.arr g) ] ≈⟨ refl⟩∘⟨ L.F-resp-≈ (𝒞.Equiv.sym eq) ⟩
      𝒟 [ arr (coeq B) ∘ L.F₁ (Module⇒.arr f) ] ≈⟨ universal (coeq A) ⟩
      𝒟 [ coequalize (coeq A) _ ∘ arr (coeq A) ] ∎
    }
    where
      open 𝒟.HomReasoning
      open MR 𝒟

  module Comparison⁻¹ = Functor Comparison⁻¹

  -- If 𝒟 has reflexive coequalizers, then the "inverse" to the comparison functor is actually adjoint.
  Comparison⁻¹⊣Comparison : Comparison⁻¹ ⊣ Comparison
  Adjoint.unit Comparison⁻¹⊣Comparison = ntHelper record
    { η = λ M → record
      { arr = 𝒞 [ R.F₁ (arr (coeq M)) ∘ adjoint.unit.η (Module.A M) ]
      ; commute = begin
        𝒞 [ 𝒞 [ R.F₁ (arr (coeq M)) ∘ adjoint.unit.η (Module.A M) ] ∘ Module.action M ]                                          ≈⟨ pullʳ (adjoint.unit.commute (Module.action M)) ⟩
        -- It would be nice to have a reasoning combinator doing this "⟺ homomorphism ... homomorphism" pattern
        𝒞 [ R.F₁ (arr (coeq M)) ∘ 𝒞 [ R.F₁ (L.F₁ (Module.action M)) ∘ adjoint.unit.η (R.F₀ (L.F₀ (Module.A M))) ] ]              ≈⟨ pullˡ (⟺ R.homomorphism) ⟩
        𝒞 [ R.F₁ (𝒟 [ arr (coeq M) ∘ L.F₁ (Module.action M) ]) ∘ adjoint.unit.η (R.F₀ (L.F₀ (Module.A M))) ]                     ≈⟨ (R.F-resp-≈ (equality (coeq M)) ⟩∘⟨refl) ⟩
        𝒞 [ R.F₁ (𝒟 [ arr (coeq M) ∘ adjoint.counit.η (L.F₀ (Module.A M)) ]) ∘ adjoint.unit.η (R.F₀ (L.F₀ (Module.A M))) ]       ≈⟨ (R.homomorphism ⟩∘⟨refl) ⟩
        𝒞 [ 𝒞 [ R.F₁ (arr (coeq M)) ∘ R.F₁ (adjoint.counit.η (L.F₀ (Module.A M))) ] ∘ adjoint.unit.η (R.F₀ (L.F₀ (Module.A M))) ] ≈⟨ cancelʳ adjoint.zag ⟩
        -- FIXME Use something like cancel here
        R.F₁ (arr (coeq M))                                                                                                        ≈˘⟨ R.F-resp-≈ (𝒟.identityʳ) ⟩
        R.F₁ (𝒟 [ arr (coeq M) ∘ 𝒟.id ])                                                                                          ≈˘⟨ R.F-resp-≈ (𝒟.∘-resp-≈ʳ adjoint.zig) ⟩
        R.F₁ (𝒟 [ arr (coeq M) ∘ 𝒟 [ adjoint.counit.η (L.F₀ (Module.A M)) ∘ L.F₁ (adjoint.unit.η (Module.A M)) ] ])               ≈⟨ R.F-resp-≈ (MR.extendʳ 𝒟 (adjoint.counit.sym-commute (arr (coeq M)))) ⟩
        R.F₁ (𝒟 [ adjoint.counit.η (obj (coeq M)) ∘ 𝒟 [ L.F₁ (R.F₁ (arr (coeq M))) ∘ L.F₁ (adjoint.unit.η (Module.A M)) ] ])      ≈˘⟨ R.F-resp-≈ (𝒟.∘-resp-≈ʳ L.homomorphism) ⟩
        R.F₁ (𝒟 [ adjoint.counit.η (obj (coeq M)) ∘ L.F₁ (𝒞 [ R.F₁ (arr (coeq M)) ∘ adjoint.unit.η (Module.A M)])])               ≈⟨ R.homomorphism ⟩
        𝒞 [ R.F₁ (adjoint.counit.η (obj (coeq M))) ∘ R.F₁ (L.F₁ (𝒞 [ R.F₁ (arr (coeq M)) ∘ adjoint.unit.η (Module.A M)])) ]       ∎
      }
    ; commute = λ {M} {N} f → begin
      𝒞 [ 𝒞 [ R.F₁ (arr (coeq N)) ∘ adjoint.unit.η (Module.A N) ] ∘ Module⇒.arr f ]               ≈⟨ extendˡ (adjoint.unit.commute (Module⇒.arr f)) ⟩
      𝒞 [ 𝒞 [ R.F₁ (arr (coeq N)) ∘ R.F₁ (L.F₁ (Module⇒.arr f)) ] ∘ adjoint.unit.η (Module.A M) ] ≈˘⟨ R.homomorphism ⟩∘⟨refl ⟩
      𝒞 [ R.F₁ (𝒟 [ arr (coeq N) ∘ L.F₁ (Module⇒.arr f) ]) ∘ adjoint.unit.η (Module.A M) ]        ≈⟨ R.F-resp-≈ (universal (coeq M)) ⟩∘⟨refl ⟩
      𝒞 [ R.F₁ (𝒟 [ (coequalize (coeq M) _) ∘ (arr (coeq M)) ]) ∘ adjoint.unit.η (Module.A M) ]    ≈⟨ pushˡ R.homomorphism ⟩
      𝒞 [ R.F₁ (coequalize (coeq M) _) ∘ 𝒞 [ R.F₁ (arr (coeq M)) ∘ adjoint.unit.η (Module.A M) ] ] ∎
    }
    where
      open 𝒞.HomReasoning
      open MR 𝒞
  Adjoint.counit Comparison⁻¹⊣Comparison = ntHelper record
    { η = λ X → coequalize (coeq (Comparison.F₀ X)) (adjoint.counit.commute (adjoint.counit.η X))
    ; commute = λ {X} {Y} f → begin
      𝒟 [ coequalize (coeq (Comparison.F₀ Y)) _ ∘ coequalize (coeq (Comparison.F₀ X)) _ ]        ≈⟨ unique (coeq (Comparison.F₀ X)) (adjoint.counit.sym-commute f ○ pushˡ (universal (coeq (Comparison.F₀ Y))) ○ pushʳ (universal (coeq (Comparison.F₀ X)))) ⟩
      coequalize (coeq (Comparison.F₀ X)) (extendˡ (adjoint.counit.commute (adjoint.counit.η X))) ≈˘⟨ unique (coeq (Comparison.F₀ X)) (pushʳ (universal (coeq (Comparison.F₀ X)))) ⟩
      𝒟 [ f ∘ coequalize (coeq (Comparison.F₀ X)) _ ]                                            ∎
    }
    where
      open 𝒟.HomReasoning
      open MR 𝒟
  Adjoint.zig Comparison⁻¹⊣Comparison {X} = begin
    𝒟 [ coequalize (coeq (Comparison.F₀ (Comparison⁻¹.F₀ X))) _ ∘ coequalize (coeq X) _ ] ≈⟨ unique (coeq X) (⟺ adjoint.RLadjunct≈id ○ pushˡ (universal (coeq (Comparison.F₀ (Comparison⁻¹.F₀ X)))) ○ pushʳ (universal (coeq X))) ⟩
    coequalize (coeq X) {h = arr (coeq X)} (equality (coeq X))                             ≈˘⟨ unique (coeq X) (⟺ 𝒟.identityˡ) ⟩
    𝒟.id                                                                                  ∎
    where
      open 𝒟.HomReasoning
      open MR 𝒟
  Adjoint.zag Comparison⁻¹⊣Comparison {A} = begin
    𝒞 [ R.F₁ (coequalize (coeq (Comparison.F₀ A)) _) ∘  𝒞 [ R.F₁ (arr (coeq (Comparison.F₀ A))) ∘ adjoint.unit.η (Module.A (Comparison.F₀ A)) ] ] ≈⟨ pullˡ (⟺ R.homomorphism) ⟩
    𝒞 [ R.F₁ (𝒟 [ coequalize (coeq (Comparison.F₀ A)) _ ∘ arr (coeq (Comparison.F₀ A)) ]) ∘ adjoint.unit.η (Module.A (Comparison.F₀ A)) ]         ≈˘⟨ R.F-resp-≈ (universal (coeq (Comparison.F₀ A))) ⟩∘⟨refl ⟩
    𝒞 [ R.F₁ (adjoint.counit.η A) ∘ adjoint.unit.η (R.F₀ A) ]                                                                                      ≈⟨ adjoint.zag ⟩
    𝒞.id                                                                                                                                           ∎
    where
      open 𝒞.HomReasoning
      open MR 𝒞
