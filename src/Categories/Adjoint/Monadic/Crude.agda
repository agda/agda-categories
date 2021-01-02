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

-- TODO: I think a _lot_ of this can be factored out into a helper lemma:
--

-- If 𝒟 has coequalizers of reflexive pairs, then the comparison functor has a left adjoint.
module _ (has-reflexive-coequalizers : ∀ {A B} {f g : 𝒟 [ A , B ]} → ReflexivePair 𝒟 f g → Coequalizer 𝒟 f g) where

  -- The key part of the proof. As we have all reflexive coequalizers, we can create the following coequalizer.
  -- We can think of this as identifying the action of the algebra lifted to a "free" structure
  -- and the counit of the adjunction, as the unit of the adjunction (also lifted to the "free structure") is a section of both.
  has-coequalizer : (M : Module T) → Coequalizer 𝒟 (L.F₁ (Module.action M)) (adjoint.counit.η (L.₀ (Module.A M)))
  has-coequalizer M = has-reflexive-coequalizers record
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

  -- -- If we have coequalizers of reflexive pairs, then we can define an "inverse" to the comparison functor.
  -- Comparison⁻¹ : Functor 𝒞ᵀ 𝒟
  -- Comparison⁻¹ = record
  --   { F₀ = λ M → obj (coeq M)
  --   ; F₁ = λ {M} {N} α → coequalize (coeq M) $ begin
  --     𝒟 [ 𝒟 [ arr (coeq N) ∘ L.F₁ (Module⇒.arr α) ] ∘ L.F₁ (Module.action M) ]                             ≈⟨ pullʳ (⟺ L.homomorphism) ⟩
  --     𝒟 [ arr (coeq N) ∘ L.F₁ (𝒞 [ Module⇒.arr α ∘ Module.action M ]) ]                                    ≈⟨ refl⟩∘⟨ L.F-resp-≈ (Module⇒.commute α) ⟩
  --     𝒟 [ arr (coeq N) ∘ L.F₁ (𝒞 [ Module.action N ∘ R.F₁ (L.F₁ (Module⇒.arr α)) ]) ]                      ≈⟨ refl⟩∘⟨ L.homomorphism ⟩
  --     𝒟 [ arr (coeq N) ∘ 𝒟 [ L.F₁ (Module.action N) ∘ L.F₁ (R.F₁ (L.F₁ (Module⇒.arr α))) ] ]               ≈⟨ pullˡ (equality (coeq N)) ⟩
  --     𝒟 [ 𝒟 [ arr (coeq N) ∘ adjoint.counit.η (L.F₀ (Module.A N)) ] ∘ L.F₁ (R.F₁ (L.F₁ (Module⇒.arr α))) ] ≈⟨ extendˡ (adjoint.counit.commute (L.F₁ (Module⇒.arr α))) ⟩
  --     𝒟 [ 𝒟 [ arr (coeq N) ∘ L.F₁ (Module⇒.arr α) ] ∘ adjoint.counit.η (L.₀ (Module.A M)) ]                ∎
  --   ; identity = λ {A} → ⟺ $ unique (coeq A) $ begin
  --     𝒟 [ arr (coeq A) ∘ L.F₁ 𝒞.id ] ≈⟨ refl⟩∘⟨ L.identity ⟩
  --     𝒟 [ arr (coeq A) ∘ 𝒟.id ]      ≈⟨ id-comm ⟩
  --     𝒟 [ 𝒟.id ∘ arr (coeq A) ]      ∎
  --   ; homomorphism = λ {X} {Y} {Z} {f} {g} → ⟺ $ unique (coeq X) $ begin
  --     𝒟 [ arr (coeq Z) ∘ L.F₁ (𝒞 [ Module⇒.arr g ∘ Module⇒.arr f ]) ]        ≈⟨ 𝒟.∘-resp-≈ʳ L.homomorphism ○ 𝒟.sym-assoc ⟩
  --     𝒟 [ 𝒟 [ arr (coeq Z) ∘ L.F₁ (Module⇒.arr g) ] ∘ L.F₁ (Module⇒.arr f) ] ≈⟨ universal (coeq Y) ⟩∘⟨refl ⟩
  --     𝒟 [ 𝒟 [ coequalize (coeq Y) _ ∘ arr (coeq Y) ] ∘ L.F₁ (Module⇒.arr f) ] ≈⟨ extendˡ (universal (coeq X)) ⟩
  --     𝒟 [ 𝒟 [ coequalize (coeq Y) _ ∘ coequalize (coeq X) _ ] ∘ arr (coeq X) ] ∎
  --   ; F-resp-≈ = λ {A} {B} {f} {g} eq → unique (coeq A) $ begin
  --     𝒟 [ arr (coeq B) ∘ L.F₁ (Module⇒.arr g) ] ≈⟨ refl⟩∘⟨ L.F-resp-≈ (𝒞.Equiv.sym eq) ⟩
  --     𝒟 [ arr (coeq B) ∘ L.F₁ (Module⇒.arr f) ] ≈⟨ universal (coeq A) ⟩
  --     𝒟 [ coequalize (coeq A) _ ∘ arr (coeq A) ] ∎
  --   }
  --   where
  --     open 𝒟.HomReasoning
  --     open MR 𝒟

  -- module Comparison⁻¹ = Functor Comparison⁻¹

    
  


-- -- If 𝒟 has coequalizers of reflexive pairs _and_ R preserves these coequalizers, then the unit of the adjunction
-- -- from the previous section is an
-- module _ (has-reflexive-coequalizers : ∀ {A B} {f g : 𝒟 [ A , B ]} → ReflexivePair 𝒟 f g → Coequalizer 𝒟 f g) where
