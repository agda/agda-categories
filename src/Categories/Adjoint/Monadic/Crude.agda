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

open import Categories.Adjoint.Properties
open import Categories.Adjoint.Monadic
open import Categories.Adjoint.Monadic.Properties
open import Categories.Functor.Properties
open import Categories.NaturalTransformation.NaturalIsomorphism
open import Categories.NaturalTransformation
open import Categories.Monad

open import Categories.Diagram.Coequalizer
open import Categories.Diagram.ReflexivePair

open import Categories.Adjoint.Construction.EilenbergMoore
open import Categories.Category.Construction.EilenbergMoore
open import Categories.Category.Construction.Properties.EilenbergMoore

open import Categories.Morphism
open import Categories.Morphism.Notation
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

-- If 𝒟 has coequalizers of reflexive pairs, then the comparison functor has a left adjoint.
module _ (has-reflexive-coequalizers : ∀ {A B} {f g : 𝒟 [ A , B ]} → ReflexivePair 𝒟 f g → Coequalizer 𝒟 f g) where

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

  coequalizer : (M : Module T) → Coequalizer 𝒞 (R.F₁ (L.F₁ (Module.action M))) (R.F₁ (adjoint.counit.η (L.₀ (Module.A M))))
  coequalizer M = record
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

  -- FIXME: These proofs are _horrible_
  unit-iso : PreservesReflexiveCoequalizers R → NaturalIsomorphism (Comparison ∘F Comparison⁻¹ adjoint has-coequalizer) idF
  unit-iso preserves-reflexive-coeq = record
    { F⇒G = ntHelper record
      { η = λ M → record
        { arr = coequalizer-iso.from M
        ; commute = begin
          𝒞 [ coequalizer-iso.from M ∘ R.F₁ (adjoint.counit.η (obj (has-coequalizer M))) ]                                                                                                                                                      ≈⟨ introʳ (R.F-resp-≈ L.identity ○ R.identity) ⟩
          𝒞 [ 𝒞 [ coequalizer-iso.from M ∘ R.F₁ (adjoint.counit.η (obj (has-coequalizer M))) ] ∘ R.F₁ (L.F₁ 𝒞.id) ]                                                                                                                            ≈⟨ pushʳ (R.F-resp-≈ (L.F-resp-≈ (⟺ (coequalizer-iso.isoˡ M))) ○ (R.F-resp-≈ L.homomorphism) ○ R.homomorphism) ⟩
          𝒞 [ 𝒞 [ 𝒞 [ coequalizer-iso.from M ∘ R.F₁ (adjoint.counit.η (obj (has-coequalizer M))) ] ∘ R.F₁ (L.F₁ (coequalizer-iso.to M)) ] ∘ R.F₁ (L.F₁ (coequalizer-iso.from M)) ]                                                             ≈⟨ 𝒞.Equiv.refl ⟩
          𝒞 [ 𝒞 [ 𝒞 [ coequalizer-iso.from M ∘ R.F₁ (adjoint.counit.η (obj (has-coequalizer M))) ] ∘ R.F₁ (L.F₁ (𝒞 [ R.F₁ (arr (has-coequalizer M)) ∘ adjoint.unit.η (Module.A M) ])) ] ∘ R.F₁ (L.F₁ (coequalizer-iso.from M)) ]               ≈⟨ (refl⟩∘⟨ (R.F-resp-≈ L.homomorphism ○ R.homomorphism)) ⟩∘⟨refl ⟩
          𝒞 [ 𝒞 [ 𝒞 [ coequalizer-iso.from M ∘ R.F₁ (adjoint.counit.η (obj (has-coequalizer M))) ] ∘ 𝒞 [ R.F₁ (L.F₁ (R.F₁ (arr (has-coequalizer M)))) ∘ R.F₁ (L.F₁ (adjoint.unit.η (Module.A M))) ] ] ∘ R.F₁ (L.F₁ (coequalizer-iso.from M)) ] ≈⟨ center ([ R ]-resp-square (adjoint.counit.commute (arr (has-coequalizer M)))) ⟩∘⟨refl ⟩
          𝒞 [ 𝒞 [ coequalizer-iso.from M ∘ 𝒞 [ 𝒞 [ R.F₁ (arr (has-coequalizer M)) ∘ R.F₁ (adjoint.counit.η (L.F₀ (Module.A M))) ] ∘ R.F₁ (L.F₁ (adjoint.unit.η (Module.A M))) ] ] ∘ R.F₁ (L.F₁ (coequalizer-iso.from M)) ]                     ≈⟨ ( (refl⟩∘⟨ (cancelʳ (⟺ R.homomorphism ○ R.F-resp-≈ adjoint.zig ○ R.identity))) ⟩∘⟨refl) ⟩
          𝒞 [ 𝒞 [ coequalizer-iso.from M ∘ R.F₁ (arr (has-coequalizer M)) ] ∘ R.F₁ (L.F₁ (_≅_.from (coequalizer-iso M))) ]                                                                                                                       ≈˘⟨ IsCoequalizer.universal (has-coequalizer′ M) ⟩∘⟨refl ⟩
          𝒞 [ Module.action M ∘ R.F₁ (L.F₁ (coequalizer-iso.from M)) ]                                                                                                                                                                            ∎
        }
      ; commute = λ {M} {N} f → begin
        𝒞 [ IsCoequalizer.coequalize (has-coequalizer′ N) _ ∘ R.F₁ (coequalize (has-coequalizer M) _) ] ≈⟨ refl⟩∘⟨ preserves-coequalizer-unique M ⟩
        -- This is _bad. I should have a lemma somewhere that composition of coequalizers is the same as a coequalizer.
        𝒞 [ IsCoequalizer.coequalize (has-coequalizer′ N) _ ∘ IsCoequalizer.coequalize (has-coequalizer′ M) _ ] ≈⟨ IsCoequalizer.unique (has-coequalizer′ M) (Module⇒.commute f ○ pushˡ (IsCoequalizer.universal (has-coequalizer′ N)) ○ 𝒞.∘-resp-≈ʳ (⟺ R.homomorphism) ○ pushʳ (IsCoequalizer.universal (has-coequalizer′ M))) ⟩
        IsCoequalizer.coequalize (has-coequalizer′ M) (extendˡ (Module.commute M)) ≈˘⟨ IsCoequalizer.unique (has-coequalizer′ M) (pushʳ (IsCoequalizer.universal (has-coequalizer′ M))) ⟩
        𝒞 [ Module⇒.arr f ∘ IsCoequalizer.coequalize (has-coequalizer′ M) _ ] ∎
      }
    ; F⇐G = Comparison⁻¹⊣Comparison.unit adjoint has-coequalizer
    ; iso = λ M → record
      { isoˡ = begin
        -- This is _horrible_. Needs to be refactored
        𝒞 [ 𝒞 [ R.F₁ (arr (has-coequalizer M)) ∘ adjoint.unit.η (Module.A M) ] ∘ IsCoequalizer.coequalize (has-coequalizer′ M) _ ] ≈⟨ IsCoequalizer.unique (has-coequalizer′ M) (pushʳ (IsCoequalizer.universal (has-coequalizer′ M))) ⟩
        -- We should have a helper lemma somewhere for this that isn't as general as coequalize-resp-≈′
        IsCoequalizer.coequalize (has-coequalizer′ M) (extendˡ (Module.commute M)) ≈˘⟨ IsCoequalizer.unique (has-coequalizer′ M) (extendˡ (adjoint.unit.commute (Module.action M)) ○ 𝒞.∘-resp-≈ˡ (IsCoequalizer.equality (has-coequalizer′ M)) ○ pullʳ adjoint.zag ○ id-comm) ⟩
        𝒞.id ∎
      ; isoʳ = begin
        𝒞 [ IsCoequalizer.coequalize (has-coequalizer′ M) _ ∘ 𝒞 [ R.F₁ (arr (has-coequalizer M)) ∘ adjoint.unit.η (Module.A M) ] ] ≈⟨ pullˡ (⟺ (IsCoequalizer.universal (has-coequalizer′ M))) ⟩
        𝒞 [ Module.action M ∘ adjoint.unit.η (Module.A M) ] ≈⟨ Module.identity M ⟩
        𝒞.id ∎
      }
    }
    where
      open 𝒞.HomReasoning
      open MR 𝒞

      coequalizer-iso : (M : Module T) → 𝒞 [ R.F₀ (obj (has-reflexive-coequalizers (reflexive-pair M))) ≅ obj (coequalizer M) ]
      coequalizer-iso M = up-to-iso 𝒞 ((IsCoequalizer⇒Coequalizer 𝒞 (preserves-reflexive-coeq (reflexive-pair M) (has-coequalizer M)))) (coequalizer M)

      -- better name?
      has-coequalizer′ : ∀ (M : Module T) → IsCoequalizer 𝒞 (R.F₁ (L.F₁ (Module.action M))) (R.F₁ (adjoint.counit.η (L.₀ (Module.A M)))) (R.F₁ (arr (has-coequalizer M)))
      has-coequalizer′ M = (preserves-reflexive-coeq (reflexive-pair M) (has-coequalizer M))

      -- This should probably live alongside the definition of preserving reflexive coequalizers.
      preserves-coequalizer-unique : ∀ (M : Module T) → {Z : 𝒟.Obj} {h : 𝒟 [ L.F₀ (Module.A M) , Z ]} {eq : 𝒟 [ 𝒟 [ h ∘ L.F₁ (Module.action M) ] ≈ 𝒟 [ h ∘ adjoint.counit.η (L.₀ (Module.A M)) ] ]}
                                     → 𝒞 [ R.F₁ (coequalize (has-coequalizer M) eq) ≈ IsCoequalizer.coequalize (has-coequalizer′ M) ([ R ]-resp-square eq) ]
      preserves-coequalizer-unique M = begin
        R.F₁ (coequalize (has-coequalizer M) _) ≈⟨ IsCoequalizer.unique (has-coequalizer′ M) (R.F-resp-≈ (universal (has-coequalizer M)) ○ R.homomorphism) ⟩
        IsCoequalizer.coequalize (has-coequalizer′ M) ([ R ]-resp-square _) ∎

      module coequalizer-iso M = _≅_ (coequalizer-iso M)
