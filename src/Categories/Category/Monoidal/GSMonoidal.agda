{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

-- GS-monoidal categories, as introduced by Gadducci & Corradini ("gs" for
-- garbage and sharing): symmetric monoidal categories in which every object
-- carries a commutative comonoid structure, coherently with the tensor, and in
-- which neither comonoid map is required to be natural.
--
-- Requiring the comultiplication to be natural yields counital copy categories
-- (Categories.Category.Monoidal.CounitalCopy); requiring both to be natural
-- yields cartesian categories.

module Categories.Category.Monoidal.GSMonoidal
  {o ℓ e} {𝒞 : Category o ℓ e} {monoidal : Monoidal 𝒞} (symmetric : Symmetric monoidal) where

open import Level using (suc; _⊔_)
open import Data.Product.Base using (_,_)

open import Categories.Object.Monoid using (IsMonoid)

import Categories.Category.Monoidal.Properties
import Categories.Category.Monoidal.Utilities as MonoidalUtils
import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Interchange.Braided as BraidedInterchange
import Categories.Category.Monoidal.Interchange.Symmetric as SymmetricInterchange
import Categories.Category.Monoidal.Symmetric.Properties as SymmetricProps
import Categories.Morphism.Reasoning as MorphismReasoning

record GSMonoidal : Set (suc (o ⊔ ℓ ⊔ e)) where
  open Category 𝒞
  open Symmetric symmetric
  open BraidedProps braided using (braiding-coherence-inv)
    renaming (module Shorthands to BraidedShorthands)
  open BraidedShorthands using (σ⇒; σ⇐; σ⇒-comm)
  open BraidedInterchange braided
    using (module swapInner; swapInner-expand; swapInner-natural)
  open SymmetricInterchange symmetric using (swapInner-unitˡ⁻¹)
  open SymmetricProps symmetric using (braiding-selfInverse)
  open MonoidalUtils monoidal using (module Shorthands)
  open Shorthands
  open Categories.Category.Monoidal.Properties monoidal
    using (monoidal-Op; coherence-inv₃)
  open MorphismReasoning 𝒞 using (cancelˡ; elimˡ; pullˡ; pullʳ; extendʳ)

  field
    isComonoid : ∀ X → IsMonoid (monoidal-Op) X

  Δ : ∀ {X} → X ⇒ X ⊗₀ X
  Δ {X} = IsMonoid.μ (isComonoid X)
  δ : ∀ {X} → X ⇒ unit
  δ {X} = IsMonoid.η (isComonoid X)

  field
    inverse₁ : Δ {unit} ∘ λ⇒ ≈ id
    inverse₂ : λ⇒ ∘ Δ {unit} ≈ id
    cocommutative : ∀ {A} → σ⇒ ∘ Δ ≈ Δ {A}
    preserves : ∀ {X Y} → α⇐ ∘ (id ⊗₁ α⇒) ∘ (id ⊗₁ ((σ⇒ ⊗₁ id) ∘ α⇐)) ∘ α⇒ ∘ (Δ ⊗₁ Δ) ≈ Δ {X ⊗₀ Y}

  -- What `preserves` says: copying a tensor is copying each factor and then
  -- interchanging.  The composite above is the four middle interchange of
  -- Categories.Category.Monoidal.Interchange.Braided, with its two inner
  -- factors composed separately rather than tensored at once, which is the
  -- form a proof of the field wants.

  preserves-interchange : ∀ {X Y} → swapInner.from ∘ (Δ ⊗₁ Δ) ≈ Δ {X ⊗₀ Y}
  preserves-interchange = ∘-resp-≈ˡ swapInner-expand ○ assoc ○ ∘-resp-≈ʳ assoc
                        ○ ∘-resp-≈ʳ (∘-resp-≈ʳ assoc) ○ preserves
    where open HomReasoning

  module _ {X : Obj} where
    open IsMonoid (isComonoid X) hiding (μ; η) renaming (assoc to Δ-assoc; identityˡ to δ-identityˡ; identityʳ to δ-identityʳ) public

  -- The two naturality conditions the definition withholds, one morphism at a
  -- time.  A morphism is total when discarding its result is discarding its
  -- argument, and deterministic when copying its result is running it on both
  -- copies of its argument.  Asking `Deterministic` of every morphism is the
  -- one field of CounitalCopy; asking both of every morphism is cartesian.

  Total : ∀ {X Y} → X ⇒ Y → Set e
  Total f = δ ∘ f ≈ δ

  Deterministic : ∀ {X Y} → X ⇒ Y → Set e
  Deterministic f = Δ ∘ f ≈ (f ⊗₁ f) ∘ Δ

  -- The two counit coherence laws that most presentations take as axioms.
  -- They follow from the fields above, which is why this record has five and
  -- not seven.  A counit is unique for a given comultiplication, dual to
  -- uniqueness of a monoid unit, and each law is then a matter of exhibiting a
  -- counit.  Categories.Object.Monoid offers no such uniqueness lemma.

  counit-unique : ∀ {X} (δ′ : X ⇒ unit)
                → λ⇐ ≈ (δ′ ⊗₁ id) ∘ Δ
                → ρ⇐ ≈ (id ⊗₁ δ′) ∘ Δ
                → δ′ ≈ δ
  counit-unique {X} δ′ identityˡ′ identityʳ′ = begin
    δ′           ≈˘⟨ cancelˡ unitorˡ.isoʳ ⟩
    λ⇒ ∘ λ⇐ ∘ δ′ ≈⟨ refl⟩∘⟨ main ⟩
    λ⇒ ∘ λ⇐ ∘ δ  ≈⟨ cancelˡ unitorˡ.isoʳ ⟩
    δ            ∎
    where
      open HomReasoning
      open Equiv

      main : λ⇐ ∘ δ′ ≈ λ⇐ ∘ δ
      main = begin
        λ⇐ ∘ δ′                    ≈⟨ unitorˡ-commute-to ⟩
        (id ⊗₁ δ′) ∘ λ⇐            ≈⟨ refl⟩∘⟨ δ-identityˡ ⟩
        (id ⊗₁ δ′) ∘ (δ ⊗₁ id) ∘ Δ ≈⟨ pullˡ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identityˡ , identityʳ)) ⟩
        (δ ⊗₁ δ′) ∘ Δ              ≈˘⟨ pullˡ (sym ⊗.homomorphism ○ ⊗.F-resp-≈ (identityʳ , identityˡ)) ⟩
        (δ ⊗₁ id) ∘ (id ⊗₁ δ′) ∘ Δ ≈˘⟨ refl⟩∘⟨ identityʳ′ ⟩
        (δ ⊗₁ id) ∘ ρ⇐             ≈˘⟨ unitorʳ-commute-to ⟩
        ρ⇐ ∘ δ                     ≈˘⟨ coherence-inv₃ ⟩∘⟨refl ⟩
        λ⇐ ∘ δ                     ∎

  Δ-unit : Δ {unit} ≈ λ⇐
  Δ-unit = begin
    Δ           ≈˘⟨ cancelˡ unitorˡ.isoˡ ⟩
    λ⇐ ∘ λ⇒ ∘ Δ ≈⟨ refl⟩∘⟨ inverse₂ ⟩
    λ⇐ ∘ id     ≈⟨ identityʳ ⟩
    λ⇐          ∎
    where open HomReasoning

  δ-unit : δ {unit} ≈ id
  δ-unit = sym (counit-unique id lawˡ lawʳ)
    where
      open HomReasoning
      open Equiv

      lawˡ : λ⇐ ≈ (id ⊗₁ id) ∘ Δ {unit}
      lawˡ = begin
        λ⇐             ≈˘⟨ Δ-unit ⟩
        Δ              ≈˘⟨ identityˡ ⟩
        id ∘ Δ         ≈˘⟨ ⊗.identity ⟩∘⟨refl ⟩
        (id ⊗₁ id) ∘ Δ ∎

      lawʳ : ρ⇐ ≈ (id ⊗₁ id) ∘ Δ {unit}
      lawʳ = begin
        ρ⇐             ≈˘⟨ coherence-inv₃ ⟩
        λ⇐             ≈⟨ lawˡ ⟩
        (id ⊗₁ id) ∘ Δ ∎

  δ-⊗ : ∀ {X Y} → δ {X ⊗₀ Y} ≈ λ⇒ ∘ (δ {X} ⊗₁ δ {Y})
  δ-⊗ {X} {Y} = sym (counit-unique (λ⇒ ∘ (δ ⊗₁ δ)) lawˡ lawʳ)
    where
      open HomReasoning
      open Equiv

      δ′ = λ⇒ ∘ (δ {X} ⊗₁ δ {Y})

      step1 : δ′ ⊗₁ id ≈ (λ⇒ ⊗₁ id) ∘ ((δ ⊗₁ δ) ⊗₁ id)
      step1 = ⊗.F-resp-≈ (refl , sym identity²) ○ ⊗.homomorphism

      step2 : ((δ ⊗₁ δ) ⊗₁ id) ∘ swapInner.from
            ≈ swapInner.from ∘ ((δ ⊗₁ id) ⊗₁ (δ ⊗₁ id))
      step2 = (⊗.F-resp-≈ (refl , sym ⊗.identity) ⟩∘⟨refl) ○ sym swapInner-natural

      step3 : ((δ ⊗₁ id) ⊗₁ (δ ⊗₁ id)) ∘ (Δ ⊗₁ Δ) ≈ λ⇐ ⊗₁ λ⇐
      step3 = sym ⊗.homomorphism ○ ⊗.F-resp-≈ (sym δ-identityˡ , sym δ-identityˡ)

      lawˡ : λ⇐ ≈ (δ′ ⊗₁ id) ∘ Δ {X ⊗₀ Y}
      lawˡ = sym (begin
        (δ′ ⊗₁ id) ∘ Δ                                              ≈˘⟨ refl⟩∘⟨ preserves-interchange ⟩
        (δ′ ⊗₁ id) ∘ swapInner.from ∘ (Δ ⊗₁ Δ)                      ≈⟨ step1 ⟩∘⟨refl ⟩
        ((λ⇒ ⊗₁ id) ∘ ((δ ⊗₁ δ) ⊗₁ id)) ∘ swapInner.from ∘ (Δ ⊗₁ Δ) ≈⟨ assoc ⟩
        (λ⇒ ⊗₁ id) ∘ ((δ ⊗₁ δ) ⊗₁ id) ∘ swapInner.from ∘ (Δ ⊗₁ Δ)   ≈⟨ refl⟩∘⟨ pullˡ step2 ⟩
        (λ⇒ ⊗₁ id) ∘ (swapInner.from ∘ ((δ ⊗₁ id) ⊗₁ (δ ⊗₁ id))) ∘ (Δ ⊗₁ Δ)
                                                                    ≈⟨ refl⟩∘⟨ assoc ⟩
        (λ⇒ ⊗₁ id) ∘ swapInner.from ∘ ((δ ⊗₁ id) ⊗₁ (δ ⊗₁ id)) ∘ (Δ ⊗₁ Δ)
                                                                    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ step3 ⟩
        (λ⇒ ⊗₁ id) ∘ swapInner.from ∘ (λ⇐ ⊗₁ λ⇐)                    ≈⟨ swapInner-unitˡ⁻¹ ⟩
        λ⇐                                                          ∎)

      lawʳ : ρ⇐ ≈ (id ⊗₁ δ′) ∘ Δ {X ⊗₀ Y}
      lawʳ = sym (begin
        (id ⊗₁ δ′) ∘ Δ      ≈˘⟨ refl⟩∘⟨ cocommutative ⟩
        (id ⊗₁ δ′) ∘ σ⇒ ∘ Δ ≈˘⟨ extendʳ σ⇒-comm ⟩
        σ⇒ ∘ (δ′ ⊗₁ id) ∘ Δ ≈˘⟨ refl⟩∘⟨ lawˡ ⟩
        σ⇒ ∘ λ⇐             ≈˘⟨ braiding-selfInverse ⟩∘⟨refl ⟩
        σ⇐ ∘ λ⇐             ≈⟨ braiding-coherence-inv ⟩
        ρ⇐                  ∎)

  -- Each of the two conditions holds of the identity and is closed under
  -- composition and under the tensor, so the morphisms satisfying either form
  -- a wide subcategory closed under `⊗`.  Whether the coherence maps satisfy
  -- them is a further question, not answered here.

  Total-id : ∀ {X} → Total (id {X})
  Total-id = identityʳ

  Total-∘ : ∀ {X Y Z} {f : Y ⇒ Z} {g : X ⇒ Y} → Total f → Total g → Total (f ∘ g)
  Total-∘ total-f total-g = sym-assoc ○ (total-f ⟩∘⟨refl) ○ total-g
    where open HomReasoning

  Total-⊗ : ∀ {X Y Z W} {f : X ⇒ Y} {g : Z ⇒ W} →
            Total f → Total g → Total (f ⊗₁ g)
  Total-⊗ total-f total-g =
      (δ-⊗ ⟩∘⟨refl)
    ○ pullʳ (sym ⊗.homomorphism)
    ○ (refl⟩∘⟨ ⊗.F-resp-≈ (total-f , total-g))
    ○ sym δ-⊗
    where open HomReasoning
          open Equiv

  Deterministic-id : ∀ {X} → Deterministic (id {X})
  Deterministic-id = identityʳ ○ sym (elimˡ ⊗.identity)
    where open HomReasoning
          open Equiv

  Deterministic-∘ : ∀ {X Y Z} {f : Y ⇒ Z} {g : X ⇒ Y} →
                    Deterministic f → Deterministic g → Deterministic (f ∘ g)
  Deterministic-∘ det-f det-g =
      sym-assoc
    ○ (det-f ⟩∘⟨refl)
    ○ assoc
    ○ (refl⟩∘⟨ det-g)
    ○ sym-assoc
    ○ (sym ⊗.homomorphism ⟩∘⟨refl)
    where open HomReasoning
          open Equiv

  Deterministic-⊗ : ∀ {X Y Z W} {f : X ⇒ Y} {g : Z ⇒ W} →
                    Deterministic f → Deterministic g → Deterministic (f ⊗₁ g)
  Deterministic-⊗ det-f det-g =
      (sym preserves-interchange ⟩∘⟨refl)
    ○ pullʳ (sym ⊗.homomorphism)
    ○ (refl⟩∘⟨ ⊗.F-resp-≈ (det-f , det-g))
    ○ (refl⟩∘⟨ ⊗.homomorphism)
    ○ extendʳ swapInner-natural
    ○ (refl⟩∘⟨ preserves-interchange)
    where open HomReasoning
          open Equiv
