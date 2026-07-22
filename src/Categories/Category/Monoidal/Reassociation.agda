{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Monoidal.Core using (Monoidal)

-- Reassociation lemmas for monoidal categories.

module Categories.Category.Monoidal.Reassociation
  {o ℓ e} {𝒞 : Category o ℓ e} (M : Monoidal 𝒞) where

open Category 𝒞
open Monoidal M

open import Categories.Category.Construction.Core 𝒞 as Core using (Core)
open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Utilities M
open import Categories.Category.Monoidal.Reasoning M
import Categories.Morphism.Reasoning as MR

open Core.Shorthands
open Shorthands
open MR 𝒞

private
  variable
    A B C D E W X Y Z : Obj

------------------------------------------------------------------------
-- Unitors against the associator.

λ⇒-assoc : (λ⇒ {A} ⊗₁ id {B}) ∘ α⇐ ≈ λ⇒
λ⇒-assoc = ⟺ (switch-fromtoʳ associator coherence₁)

λ⇐-assoc : α⇒ ∘ (λ⇐ {A} ⊗₁ id {B}) ≈ λ⇐
λ⇐-assoc = begin
  α⇒ ∘ (λ⇐ ⊗₁ id)   ≈˘⟨ refl⟩∘⟨ coherence-inv₁ ⟩
  α⇒ ∘ (α⇐ ∘ λ⇐)    ≈⟨ cancelˡ associator.isoʳ ⟩
  λ⇐                ∎

ρ⇒-assoc : ρ⇒ ∘ α⇐ {X} {Y} {unit} ≈ id ⊗₁ ρ⇒
ρ⇒-assoc = ⟺ (switch-fromtoʳ associator coherence₂)

ρ⇐-assoc : id {A} ⊗₁ ρ⇐ {B} ≈ α⇒ ∘ ρ⇐
ρ⇐-assoc = begin
  id ⊗₁ ρ⇐                 ≈˘⟨ cancelˡ associator.isoʳ ⟩
  α⇒ ∘ (α⇐ ∘ (id ⊗₁ ρ⇐))   ≈⟨ refl⟩∘⟨ coherence-inv₂ ⟩
  α⇒ ∘ ρ⇐                  ∎

-- Commute the left unitor past a right counit through the associator: the
-- |coherence₁| triangle, then the right unitor's square.
λ⇒-ρ⇐-comm : λ⇒ ∘ α⇒ ∘ ρ⇐ ≈ ρ⇐ {X} ∘ λ⇒
λ⇒-ρ⇐-comm = pullˡ coherence₁ ○ ⟺ unitorʳ-commute-to

------------------------------------------------------------------------
-- Whiskered maps against the associator.  Each is `assoc-commute-from/to`
-- with one leg's `id ⊗₁ id` folded away.

α⇒-id⊗-commute : {k : X ⇒ Y} →
  α⇒ {A} {B} {Y} ∘ (id ⊗₁ k) ≈ (id ⊗₁ (id ⊗₁ k)) ∘ α⇒
α⇒-id⊗-commute {k = k} = begin
  α⇒ ∘ (id ⊗₁ k)            ≈˘⟨ refl⟩∘⟨ (⊗.identity ⟩⊗⟨refl) ⟩
  α⇒ ∘ ((id ⊗₁ id) ⊗₁ k)    ≈⟨ assoc-commute-from ⟩
  (id ⊗₁ (id ⊗₁ k)) ∘ α⇒    ∎

α⇐-id⊗-commute : {k : X ⇒ Y} →
  (id {A ⊗₀ B} ⊗₁ k) ∘ α⇐ ≈ α⇐ ∘ (id ⊗₁ (id ⊗₁ k))
α⇐-id⊗-commute {k = k} = begin
  (id ⊗₁ k) ∘ α⇐            ≈˘⟨ (⊗.identity ⟩⊗⟨refl) ⟩∘⟨refl ⟩
  ((id ⊗₁ id) ⊗₁ k) ∘ α⇐    ≈˘⟨ assoc-commute-to ⟩
  α⇐ ∘ (id ⊗₁ (id ⊗₁ k))    ∎

α⇐-⊗id-commute : {k : X ⇒ Y} →
  α⇐ {Y} {A} {B} ∘ (k ⊗₁ id) ≈ ((k ⊗₁ id) ⊗₁ id) ∘ α⇐
α⇐-⊗id-commute {k = k} = begin
  α⇐ ∘ (k ⊗₁ id)          ≈˘⟨ refl⟩∘⟨ (refl⟩⊗⟨ ⊗.identity) ⟩
  α⇐ ∘ (k ⊗₁ (id ⊗₁ id))  ≈⟨ assoc-commute-to ⟩
  ((k ⊗₁ id) ⊗₁ id) ∘ α⇐  ∎

α⇒-⊗id-commute : {k : X ⇒ Y} →
  α⇒ {Y} {A} {B} ∘ ((k ⊗₁ id) ⊗₁ id) ≈ (k ⊗₁ id) ∘ α⇒
α⇒-⊗id-commute {k = k} = begin
  α⇒ ∘ ((k ⊗₁ id) ⊗₁ id)  ≈⟨ assoc-commute-from ⟩
  (k ⊗₁ (id ⊗₁ id)) ∘ α⇒  ≈⟨ (refl⟩⊗⟨ ⊗.identity) ⟩∘⟨refl ⟩
  (k ⊗₁ id) ∘ α⇒          ∎

-- Maps whiskered into *different* factors commute past each other: both sides are
-- `f ⊗₁ g`, serialized the two ways round.
whisker-comm : {f : A ⇒ B} {g : X ⇒ Y} →
  (f ⊗₁ id {Y}) ∘ (id {A} ⊗₁ g) ≈ (id ⊗₁ g) ∘ (f ⊗₁ id {X})
whisker-comm = ⟺ serialize₁₂ ○ serialize₂₁

-- Rebracketing commutes with a map tensored on either side.
rebracket-tightenˡ : {f : B ⇒ C} {h : A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y)} →
  α⇐ ∘ ((f ⊗₁ id) ∘ h) ∘ α⇒ ≈ ((f ⊗₁ id) ⊗₁ id) ∘ (α⇐ ∘ h ∘ α⇒)
rebracket-tightenˡ {f = f} {h = h} = begin
  α⇐ ∘ ((f ⊗₁ id) ∘ h) ∘ α⇒   ≈⟨ refl⟩∘⟨ assoc ⟩
  α⇐ ∘ (f ⊗₁ id) ∘ h ∘ α⇒     ≈⟨ extendʳ α⇐-⊗id-commute ⟩
  ((f ⊗₁ id) ⊗₁ id) ∘ α⇐ ∘ h ∘ α⇒ ∎

rebracket-tightenʳ : {h : B ⊗₀ (X ⊗₀ Y) ⇒ C ⊗₀ (X ⊗₀ Y)} {g : A ⇒ B} →
  α⇐ ∘ (h ∘ (g ⊗₁ id)) ∘ α⇒ ≈ (α⇐ ∘ h ∘ α⇒) ∘ ((g ⊗₁ id) ⊗₁ id)
rebracket-tightenʳ {h = h} {g = g} = begin
  α⇐ ∘ (h ∘ (g ⊗₁ id)) ∘ α⇒        ≈⟨ refl⟩∘⟨ assoc ⟩
  α⇐ ∘ h ∘ (g ⊗₁ id) ∘ α⇒          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ α⇒-⊗id-commute ⟩
  α⇐ ∘ h ∘ α⇒ ∘ ((g ⊗₁ id) ⊗₁ id)  ≈⟨ assoc²εβ ⟩
  (α⇐ ∘ h ∘ α⇒) ∘ ((g ⊗₁ id) ⊗₁ id) ∎

------------------------------------------------------------------------
-- Pentagon corollaries.

pentagon-assoc : α⇒ {A ⊗₀ B} {C} {D} ∘ (α⇐ ⊗₁ id) ∘ α⇐ ≈ α⇐ ∘ (id ⊗₁ α⇒)
pentagon-assoc = begin
  α⇒ ∘ (α⇐ ⊗₁ id) ∘ α⇐                                 ≈⟨ refl⟩∘⟨ insertʳ (⊗-cancel identity² associator.isoˡ) ⟩
  α⇒ ∘ (((α⇐ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ α⇐)) ∘ (id ⊗₁ α⇒)   ≈⟨ refl⟩∘⟨ pentagon-inv ⟩∘⟨refl ⟩
  α⇒ ∘ (α⇐ ∘ α⇐) ∘ (id ⊗₁ α⇒)                          ≈⟨ refl⟩∘⟨ assoc ⟩
  α⇒ ∘ α⇐ ∘ α⇐ ∘ (id ⊗₁ α⇒)                            ≈⟨ cancelˡ associator.isoʳ ⟩
  α⇐ ∘ (id ⊗₁ α⇒)                                      ∎

assoc-to-coherence :
  (id {A} ⊗₁ α⇐ {B} {C} {D}) ∘ α⇒ ≈ α⇒ ∘ (α⇒ ⊗₁ id) ∘ α⇐
assoc-to-coherence = begin
  (id ⊗₁ α⇐) ∘ α⇒         ≈⟨ conjugate-from associator (idᵢ ⊗ᵢ associator) (⟺ pentagon) ⟩
  (α⇒ ∘ (α⇒ ⊗₁ id)) ∘ α⇐  ≈⟨ assoc ⟩
  α⇒ ∘ (α⇒ ⊗₁ id) ∘ α⇐    ∎

assoc-from-coherence :
  α⇒ {A ⊗₀ B} {C} {D} ∘ (α⇐ ⊗₁ id) ≈ α⇐ ∘ (id ⊗₁ α⇒) ∘ α⇒
assoc-from-coherence = begin
  α⇒ ∘ (α⇐ ⊗₁ id)         ≈⟨ switch-tofromʳ associator (assoc ○ pentagon-assoc) ⟩
  (α⇐ ∘ (id ⊗₁ α⇒)) ∘ α⇒  ≈⟨ assoc ⟩
  α⇐ ∘ (id ⊗₁ α⇒) ∘ α⇒    ∎

-- Two associators followed by `α⇐ ⊗₁ id` drop a level.
pentagon-collapse :
  (α⇒ {A} {B} {C ⊗₀ D} ∘ α⇒) ∘ (α⇐ ⊗₁ id) ≈ (id ⊗₁ α⇒) ∘ α⇒
pentagon-collapse = begin
  (α⇒ ∘ α⇒) ∘ (α⇐ ⊗₁ id)     ≈⟨ assoc ⟩
  α⇒ ∘ α⇒ ∘ (α⇐ ⊗₁ id)       ≈⟨ refl⟩∘⟨ assoc-from-coherence ⟩
  α⇒ ∘ α⇐ ∘ (id ⊗₁ α⇒) ∘ α⇒  ≈⟨ cancelˡ associator.isoʳ ⟩
  (id ⊗₁ α⇒) ∘ α⇒            ∎

pentagon-collapse-inv :
  (α⇒ {A} {B} {C} ⊗₁ id {D}) ∘ α⇐ ∘ α⇐ ≈ α⇐ ∘ (id ⊗₁ α⇐)
pentagon-collapse-inv = begin
  (α⇒ ⊗₁ id) ∘ α⇐ ∘ α⇐
    ≈˘⟨ refl⟩∘⟨ pentagon-inv ⟩
  (α⇒ ⊗₁ id) ∘ ((α⇐ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ α⇐)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  (α⇒ ⊗₁ id) ∘ (α⇐ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐)
    ≈⟨ cancelˡ (⊗-cancel associator.isoʳ identity²) ⟩
  α⇐ ∘ (id ⊗₁ α⇐)  ∎

-- Associator-conjugation slide.  Conjugating an `id ⊗₁ f` block by `α⇐ ∘ _ ∘ α⇒`
-- on the left, whiskered by `id` and wrapped in a further pair of associators,
-- equals the same `f` conjugated by `α⇒ ∘ _ ∘ α⇐` on the right, under one `α⇒`.
-- `f` is opaque — this is pure pentagon/associator gymnastics.
α-conj-slide : {f : A ⊗₀ X ⇒ B ⊗₀ X} →
  α⇒ ∘ α⇒ ∘ ((α⇐ ∘ (id {Y} ⊗₁ f) ∘ α⇒) ⊗₁ id {Z}) ∘ α⇐
  ≈ (id ⊗₁ (α⇒ ∘ (f ⊗₁ id) ∘ α⇐)) ∘ α⇒
α-conj-slide {f = f} = begin
  α⇒ ∘ α⇒ ∘ ((α⇐ ∘ (id ⊗₁ f) ∘ α⇒) ⊗₁ id) ∘ α⇐                    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₁³ ⟩∘⟨refl ⟩
  α⇒ ∘ α⇒ ∘ ((α⇐ ⊗₁ id) ∘ ((id ⊗₁ f) ⊗₁ id) ∘ (α⇒ ⊗₁ id)) ∘ α⇐    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc²βε ⟩
  α⇒ ∘ α⇒ ∘ (α⇐ ⊗₁ id) ∘ ((id ⊗₁ f) ⊗₁ id) ∘ (α⇒ ⊗₁ id) ∘ α⇐      ≈⟨ assoc²εα ⟩
  ((α⇒ ∘ α⇒) ∘ (α⇐ ⊗₁ id)) ∘ ((id ⊗₁ f) ⊗₁ id) ∘ (α⇒ ⊗₁ id) ∘ α⇐  ≈⟨ pentagon-collapse ⟩∘⟨refl ⟩
  ((id ⊗₁ α⇒) ∘ α⇒) ∘ ((id ⊗₁ f) ⊗₁ id) ∘ (α⇒ ⊗₁ id) ∘ α⇐         ≈⟨ assoc ⟩
  (id ⊗₁ α⇒) ∘ α⇒ ∘ ((id ⊗₁ f) ⊗₁ id) ∘ (α⇒ ⊗₁ id) ∘ α⇐           ≈⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟩
  (id ⊗₁ α⇒) ∘ (id ⊗₁ (f ⊗₁ id)) ∘ α⇒ ∘ (α⇒ ⊗₁ id) ∘ α⇐           ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-to-coherence ⟩
  (id ⊗₁ α⇒) ∘ (id ⊗₁ (f ⊗₁ id)) ∘ (id ⊗₁ α⇐) ∘ α⇒                ≈˘⟨ assoc²βε ⟩
  ((id ⊗₁ α⇒) ∘ (id ⊗₁ (f ⊗₁ id)) ∘ (id ⊗₁ α⇐)) ∘ α⇒              ≈˘⟨ split₂³ ⟩∘⟨refl ⟩
  (id ⊗₁ (α⇒ ∘ (f ⊗₁ id) ∘ α⇐)) ∘ α⇒                              ∎
