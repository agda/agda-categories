{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Monoidal using (SymmetricMonoidalCategory)

-- The monoidal structure of a monoidal catgeory D
-- lifted pointwise to monoidal functors F : C → D.

module Categories.Functor.Monoidal.PointwiseTensor {o o′ ℓ ℓ′ e e′}
  {C : SymmetricMonoidalCategory o ℓ e}
  {D : SymmetricMonoidalCategory o′ ℓ′ e′} where

open import Level using (_⊔_)
open import Data.Product using (_,_)

private
  module C = SymmetricMonoidalCategory C
  module D = SymmetricMonoidalCategory D

open import Categories.Category using (module Commutation)
open import Categories.Category.Product using (_⁂_)
import Categories.Category.Construction.Core as Core
import Categories.Functor as Func
open import Categories.Category.Monoidal.Properties using (module Kelly's)
open import Categories.Category.Monoidal.Braided.Properties D.braided
  as BraidedProps using (braiding-coherence)
open import Categories.Category.Monoidal.Reasoning D.monoidal
open import Categories.Category.Monoidal.Utilities D.monoidal
open import Categories.Functor.Construction.Constant using (const)
open import Categories.Functor.Monoidal.Tensor using
  (module LaxSymmetric; module StrongSymmetric)
import Categories.Functor.Monoidal.Symmetric as SF
open import Categories.Morphism.Reasoning D.U
open import Categories.NaturalTransformation
  using (NaturalTransformation; ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)
import Categories.NaturalTransformation.Monoidal.Symmetric as SMNT
import Categories.NaturalTransformation.NaturalIsomorphism as NI
import Categories.NaturalTransformation.NaturalIsomorphism.Monoidal.Symmetric as SMNI

open D hiding (U) renaming (unitorˡ to λᵢ; unitorʳ to ρᵢ; associator to αᵢ)
open Commutation D.U
open Core.Shorthands D.U
open Kelly's D.monoidal
open Shorthands              -- for λ⇒, ρ⇒, α⇒, ...
open BraidedProps.Shorthands -- for σ⇒, ...

module Underlying where
  open Func hiding (id)
  open NI

  private
    infix 4 _⇛_
    _⇛_ = NaturalTransformation

  infixr 10 _⊗̇₀_ _⊗̇₁_

  -- The pointwise tensor product of two functors.
  --
  -- NOTE: the definition of _⊗̇₀_ is a manual expansion of the functor
  -- composition
  --
  --   F ⊗̇₀ G = ⊗ ∘ (F × G) ∘ Δ
  --
  -- where Δ : D → D × D is the diagonal functor.

  _⊗̇₀_ : (F G : Functor C.U D.U) → Functor C.U D.U
  F ⊗̇₀ G = record
    { F₀           = λ X → F.₀ X ⊗₀ G.₀ X
    ; F₁           = λ f → F.₁ f ⊗₁ G.₁ f
    ; identity     = (F.identity ⟩⊗⟨ G.identity) ○ ⊗.identity
    ; homomorphism = (F.homomorphism ⟩⊗⟨ G.homomorphism) ○ ⊗.homomorphism
    ; F-resp-≈     = λ eq → F.F-resp-≈ eq ⟩⊗⟨ G.F-resp-≈ eq
    }
    where
      module F = Functor F
      module G = Functor G

  _⊗̇₁_ : {F₁ F₂ G₁ G₂ : Functor C.U D.U} →
         F₁ ⇛ F₂ → G₁ ⇛ G₂ → F₁ ⊗̇₀ G₁ ⇛ F₂ ⊗̇₀ G₂
  _⊗̇₁_ {F₁} {F₂} {G₁} {G₂} β γ = ntHelper (record
    { η       = λ X → β.η X ⊗₁ γ.η X
    ; commute = λ {X Y} f → begin
        β.η Y ⊗₁ γ.η Y ∘ F₁.₁ f ⊗₁ G₁.₁ f     ≈˘⟨ ⊗.homomorphism ⟩
        (β.η Y ∘ F₁.₁ f) ⊗₁ (γ.η Y ∘ G₁.₁ f)  ≈⟨ β.commute f ⟩⊗⟨ γ.commute f ⟩
        (F₂.₁ f ∘ β.η X) ⊗₁ (G₂.₁ f ∘ γ.η X)  ≈⟨ ⊗.homomorphism ⟩
        F₂.₁ f ⊗₁ G₂.₁ f ∘ β.η X ⊗₁ γ.η X     ∎
    })
    where
      module F₁ = Functor F₁
      module F₂ = Functor F₂
      module G₁ = Functor G₁
      module G₂ = Functor G₂
      module β = NaturalTransformation β
      module γ = NaturalTransformation γ

  -- The constant functor to the unit in D.

  unitF : Functor C.U D.U
  unitF = const D.unit

  module unitF = Functor unitF

  unitF-⊗-homo : D.⊗ ∘F (unitF ⁂ unitF) ≃ unitF ∘F C.⊗
  unitF-⊗-homo = niHelper (record
    { η            = λ _ → λ⇒
    ; η⁻¹          = λ _ → λ⇐
    ; commute      = λ _ → begin
      λ⇒ ∘ id ⊗₁ id  ≈⟨ refl⟩∘⟨ ⊗.identity ⟩
      λ⇒ ∘ id        ≈⟨ id-comm ⟩
      id ∘ λ⇒        ∎
    ; iso          = λ _ → λᵢ.iso
    })

  module unitF-⊗-homo = NaturalIsomorphism unitF-⊗-homo

  -- The pointwise tensor product and the unit functor induce a
  -- symmetric monoidal structure on symmetric monoidal functors.

  ⊗̇-unitorˡ : {F : Functor C.U D.U} → unitF ⊗̇₀ F ≃ F
  ⊗̇-unitorˡ {F} = niHelper (record
    { η       = λ _ → λ⇒
    ; η⁻¹     = λ _ → λ⇐
    ; commute = λ _ → unitorˡ-commute-from
    ; iso     = λ _ → λᵢ.iso
    })

  ⊗̇-unitorʳ : {F : Functor C.U D.U} → F ⊗̇₀ unitF ≃ F
  ⊗̇-unitorʳ {F} = niHelper (record
    { η       = λ _ → ρ⇒
    ; η⁻¹     = λ _ → ρ⇐
    ; commute = λ _ → unitorʳ-commute-from
    ; iso     = λ _ → ρᵢ.iso
    })

  ⊗̇-associator : {F G H : Functor C.U D.U} → (F ⊗̇₀ G) ⊗̇₀ H ≃ F ⊗̇₀ (G ⊗̇₀ H)
  ⊗̇-associator {F} {G} {H} = niHelper (record
    { η       = λ _ → α⇒
    ; η⁻¹     = λ _ → α⇐
    ; commute = λ _ → assoc-commute-from
    ; iso     = λ _ → αᵢ.iso
    })

  ⊗̇-braiding : {F G : Functor C.U D.U} → F ⊗̇₀ G ≃ G ⊗̇₀ F
  ⊗̇-braiding {F} {G} = niHelper (record
    { η       = λ X → braiding.⇒.η (F.₀ X , G.₀ X)
    ; η⁻¹     = λ X → braiding.⇐.η (F.₀ X , G.₀ X)
    ; commute = λ f → braiding.⇒.commute (F.₁ f , G.₁ f)
    ; iso     = λ X → braiding.iso (F.₀ X , G.₀ X)
    })
    where
      module F = Functor F
      module G = Functor G

-- Shorthands for the interchange map that makes ⊗ a strong symmetric
-- monoidal functor.

open StrongSymmetric D.symmetric using ()renaming
  ( ⊗-SymmetricMonoidalFunctor to ⊗ˢ
  ; ⊗-homo-iso                 to i-iso′
  ; ⊗-homo-selfInverse         to i-selfInverse
  )
private
  module ⊗ˢ = SF.Strong.SymmetricMonoidalFunctor ⊗ˢ
  module interchange = ⊗ˢ.⊗-homo
  i  = interchange.FX≅GX
  i⇒ = λ {W X Y Z} → interchange.⇒.η ((W , X) , (Y , Z))
  i⇐ = λ {W X Y Z} → interchange.⇐.η ((W , X) , (Y , Z))

module Lax where
  open SF.Lax
  open SMNT.Lax using (SymmetricMonoidalNaturalTransformation)
  open SMNI.Lax using (SymmetricMonoidalNaturalIsomorphism; _≃_)

  private
    infix 4 _⇛_
    _⇛_ = SymmetricMonoidalNaturalTransformation

  infixr 10 _⊗̇₀_ _⊗̇₁_

  -- The pointwise tensor product of lax symmetric monoidal functors.
  --
  -- NOTE: the definition of _⊗̇₀_ is a manual expansion of the
  -- (lax monoidal) functor composition
  --
  --   F ⊗̇₀ G = ⊗ ∘ (F × G) ∘ Δ
  --
  -- with Δ : D → D × D the diagonal functor.  We could define _⊗̇₀_ in
  -- this way but that would clutter the definition of ε and ⊗-homo
  -- with extra identities that then need to be dealt with elsewhere
  -- (e.g. in the definition of _⊗̇₁_ below.  In principle, _⊗̇₁_ should
  -- be similarly definable as a composition of (monoidal) natural
  -- transformations, but the Agda type checker seems to choke on
  -- definitions involving compositions of natural transformations.

  _⊗̇₀_ : (F G : SymmetricMonoidalFunctor C D) → SymmetricMonoidalFunctor C D
  F ⊗̇₀ G = record
    { F                 = F.F Underlying.⊗̇₀ G.F
    ; isBraidedMonoidal = record
      { isMonoidal      = record
        { ε             = F.ε ⊗₁ G.ε ∘ λ⇐
        ; ⊗-homo        = ntHelper (record
          { η           = λ _ → Fh ⊗₁ Gh ∘ i⇒
          ; commute     = λ{ (f , g) → commute f g }
          })
        ; associativity = associativity
        ; unitaryˡ      = unitaryˡ
        ; unitaryʳ      = unitaryʳ
        }
      ; braiding-compat = braiding-compat
      }
    }
    where
      module F = SymmetricMonoidalFunctor F
      module G = SymmetricMonoidalFunctor G
      Fh = λ {X Y} → F.⊗-homo.η (X , Y)
      Gh = λ {X Y} → G.⊗-homo.η (X , Y)
      Cλ⇒ = λ {X} → C.braided.unitorˡ.from {X}
      Cρ⇒ = λ {X} → C.braided.unitorʳ.from {X}
      Cα⇒ = λ {X Y Z} → C.braided.associator.from {X} {Y} {Z}
      Cσ⇒ = λ {X Y} → C.braided.braiding.⇒.η (X , Y)

      commute : ∀ {W X Y Z} (f : W C.⇒ X) (g : Y C.⇒ Z) →
                  (Fh ⊗₁ Gh ∘ i⇒) ∘ (F.₁ f ⊗₁ G.₁ f) ⊗₁ (F.₁ g ⊗₁ G.₁ g)
                ≈ F.₁ (f C.⊗₁ g) ⊗₁ G.₁ (f C.⊗₁ g) ∘ (Fh ⊗₁ Gh) ∘ i⇒
      commute f g = begin
          (Fh ⊗₁ Gh ∘ i⇒) ∘ (F.₁ f ⊗₁ G.₁ f) ⊗₁ (F.₁ g ⊗₁ G.₁ g)
        ≈⟨ pullʳ (interchange.⇒.commute ((F.₁ f , G.₁ f) , (F.₁ g , G.₁ g))) ⟩
          Fh ⊗₁ Gh ∘ (F.₁ f ⊗₁ F.₁ g) ⊗₁ (G.₁ f ⊗₁ G.₁ g) ∘ i⇒
        ≈˘⟨ pushˡ ⊗.homomorphism ⟩
          (Fh ∘ F.₁ f ⊗₁ F.₁ g) ⊗₁ (Gh ∘ G.₁ f ⊗₁ G.₁ g) ∘ i⇒
        ≈⟨ F.⊗-homo.commute (f , g) ⟩⊗⟨ G.⊗-homo.commute (f , g) ⟩∘⟨refl ⟩
          (F.₁ (f C.⊗₁ g) ∘ Fh) ⊗₁ (G.₁ (f C.⊗₁ g) ∘ Gh) ∘ i⇒
        ≈⟨ pushˡ ⊗.homomorphism ⟩
          F.₁ (f C.⊗₁ g) ⊗₁ G.₁ (f C.⊗₁ g) ∘ (Fh ⊗₁ Gh) ∘ i⇒
        ∎

      associativity : ∀ {X Y Z} →
                      [ ((F.₀ X ⊗₀ G.₀ X) ⊗₀ (F.₀ Y ⊗₀ G.₀ Y)) ⊗₀ (F.₀ Z ⊗₀ G.₀ Z)
                      ⇒ F.₀ (X C.⊗₀ (Y C.⊗₀ Z)) ⊗₀ G.₀ (X C.⊗₀ (Y C.⊗₀ Z)) ]⟨
                        F.₁ Cα⇒ ⊗₁ G.₁ Cα⇒ ∘
                        (Fh ⊗₁ Gh ∘ i⇒) ∘ (Fh ⊗₁ Gh ∘ i⇒) ⊗₁ id
                      ≈ (Fh ⊗₁ Gh ∘ i⇒) ∘ id ⊗₁ (Fh ⊗₁ Gh ∘ i⇒) ∘ α⇒
                      ⟩
      associativity = begin
          F.₁ Cα⇒ ⊗₁ G.₁ Cα⇒ ∘ (Fh ⊗₁ Gh ∘ i⇒) ∘ (Fh ⊗₁ Gh ∘ i⇒) ⊗₁ id
        ≈⟨ refl⟩∘⟨ pullʳ (refl⟩∘⟨ split₁ˡ) ⟩
          F.₁ Cα⇒ ⊗₁ G.₁ Cα⇒ ∘ Fh ⊗₁ Gh ∘ i⇒ ∘ (Fh ⊗₁ Gh) ⊗₁ id ∘ i⇒ ⊗₁ id
        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ ⊗.identity ⟩∘⟨refl ⟩
          F.₁ Cα⇒ ⊗₁ G.₁ Cα⇒ ∘ Fh ⊗₁ Gh ∘
          i⇒ ∘ (Fh ⊗₁ Gh) ⊗₁ (id ⊗₁ id) ∘ i⇒ ⊗₁ id
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (interchange.⇒.commute ((Fh , Gh) , (id , id))) ⟩
          F.₁ Cα⇒ ⊗₁ G.₁ Cα⇒ ∘ Fh ⊗₁ Gh ∘ (Fh ⊗₁ id) ⊗₁ (Gh ⊗₁ id) ∘ i⇒ ∘ i⇒ ⊗₁ id
        ≈˘⟨ refl⟩∘⟨ pushˡ ⊗.homomorphism ⟩
          F.₁ Cα⇒ ⊗₁ G.₁ Cα⇒ ∘ (Fh ∘ Fh ⊗₁ id) ⊗₁ (Gh ∘ Gh ⊗₁ id) ∘ i⇒ ∘ i⇒ ⊗₁ id
        ≈⟨ extendʳ (parallel (F.associativity ○ sym-assoc) (G.associativity ○ sym-assoc)) ⟩
          (Fh ∘ id ⊗₁ Fh) ⊗₁ (Gh ∘ id ⊗₁ Gh) ∘ α⇒ ⊗₁ α⇒ ∘ i⇒ ∘ i⇒ ⊗₁ id
        ≈⟨ ⊗.homomorphism ⟩∘⟨ ⊗ˢ.associativity ⟩
          ((Fh ⊗₁ Gh) ∘ (id ⊗₁ Fh) ⊗₁ (id ⊗₁ Gh)) ∘ i⇒ ∘ id ⊗₁ i⇒ ∘ α⇒
        ≈˘⟨ pushʳ (extendʳ (interchange.⇒.commute ((id , id) , (Fh , Gh)))) ⟩
          (Fh ⊗₁ Gh) ∘ i⇒ ∘ (id ⊗₁ id) ⊗₁ (Fh ⊗₁ Gh) ∘ id ⊗₁ i⇒ ∘ α⇒
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗.identity ⟩⊗⟨refl ⟩∘⟨refl ⟩
          (Fh ⊗₁ Gh) ∘ i⇒ ∘ id ⊗₁ (Fh ⊗₁ Gh) ∘ id ⊗₁ i⇒ ∘ α⇒
        ≈˘⟨ pullʳ (refl⟩∘⟨ pushˡ split₂ˡ) ⟩
          (Fh ⊗₁ Gh ∘ i⇒) ∘ id ⊗₁ (Fh ⊗₁ Gh ∘ i⇒) ∘ α⇒
        ∎

      unitaryˡ : ∀ {X} → [ unit ⊗₀ (F.₀ X ⊗₀ G.₀ X) ⇒ F.₀ X ⊗₀ G.₀ X ]⟨
                   F.₁ Cλ⇒ ⊗₁ G.₁ Cλ⇒ ∘ (Fh ⊗₁ Gh ∘ i⇒) ∘ (F.ε ⊗₁ G.ε ∘ λ⇐) ⊗₁ id
                 ≈ λ⇒
                 ⟩
      unitaryˡ = begin
          F.₁ Cλ⇒ ⊗₁ G.₁ Cλ⇒ ∘ (Fh ⊗₁ Gh ∘ i⇒) ∘ (F.ε ⊗₁ G.ε ∘ λ⇐) ⊗₁ id
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ˡ ⟩
          F.₁ Cλ⇒ ⊗₁ G.₁ Cλ⇒ ∘ (Fh ⊗₁ Gh ∘ i⇒) ∘ (F.ε ⊗₁ G.ε) ⊗₁ id ∘ λ⇐ ⊗₁ id
        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ ⊗.identity ⟩∘⟨refl ⟩
          F.₁ Cλ⇒ ⊗₁ G.₁ Cλ⇒ ∘ (Fh ⊗₁ Gh ∘ i⇒) ∘ (F.ε ⊗₁ G.ε) ⊗₁ (id ⊗₁ id) ∘ λ⇐ ⊗₁ id
        ≈⟨ refl⟩∘⟨ pullʳ (extendʳ (interchange.⇒.commute ((F.ε , G.ε) , (id , id)))) ⟩
          F.₁ Cλ⇒ ⊗₁ G.₁ Cλ⇒ ∘ Fh ⊗₁ Gh ∘ (F.ε ⊗₁ id) ⊗₁ (G.ε ⊗₁ id) ∘ i⇒ ∘ λ⇐ ⊗₁ id
        ≈˘⟨ refl⟩∘⟨ pushˡ ⊗.homomorphism ⟩
          F.₁ Cλ⇒ ⊗₁ G.₁ Cλ⇒ ∘ (Fh ∘ F.ε ⊗₁ id) ⊗₁ (Gh ∘ G.ε ⊗₁ id) ∘ i⇒ ∘ λ⇐ ⊗₁ id
        ≈˘⟨ pushˡ ⊗.homomorphism ⟩
          (F.₁ Cλ⇒ ∘ Fh ∘ F.ε ⊗₁ id) ⊗₁ (G.₁ Cλ⇒ ∘ Gh ∘ G.ε ⊗₁ id) ∘ i⇒ ∘ λ⇐ ⊗₁ id
        ≈⟨ F.unitaryˡ ⟩⊗⟨ G.unitaryˡ ⟩∘⟨refl ⟩
          λ⇒ ⊗₁ λ⇒ ∘ i⇒ ∘ λ⇐ ⊗₁ id
        ≈⟨ ⊗ˢ.unitaryˡ ⟩
          λ⇒
        ∎

      unitaryʳ : ∀ {X} → [ (F.₀ X ⊗₀ G.₀ X) ⊗₀ unit ⇒ F.₀ X ⊗₀ G.₀ X ]⟨
                   F.₁ Cρ⇒ ⊗₁ G.₁ Cρ⇒ ∘ (Fh ⊗₁ Gh ∘ i⇒) ∘ id ⊗₁ (F.ε ⊗₁ G.ε ∘ λ⇐)
                 ≈ ρ⇒
                 ⟩
      unitaryʳ = begin
          F.₁ Cρ⇒ ⊗₁ G.₁ Cρ⇒ ∘ (Fh ⊗₁ Gh ∘ i⇒) ∘ id ⊗₁ (F.ε ⊗₁ G.ε ∘ λ⇐)
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₂ˡ ⟩
          F.₁ Cρ⇒ ⊗₁ G.₁ Cρ⇒ ∘ (Fh ⊗₁ Gh ∘ i⇒) ∘ id ⊗₁ (F.ε ⊗₁ G.ε) ∘ id ⊗₁ λ⇐
        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗.identity ⟩⊗⟨refl ⟩∘⟨refl ⟩
          F.₁ Cρ⇒ ⊗₁ G.₁ Cρ⇒ ∘ (Fh ⊗₁ Gh ∘ i⇒) ∘ (id ⊗₁ id) ⊗₁ (F.ε ⊗₁ G.ε) ∘ id ⊗₁ λ⇐
        ≈⟨ refl⟩∘⟨ pullʳ (extendʳ (interchange.⇒.commute ((id , id) , (F.ε , G.ε)))) ⟩
          F.₁ Cρ⇒ ⊗₁ G.₁ Cρ⇒ ∘ Fh ⊗₁ Gh ∘ (id ⊗₁ F.ε) ⊗₁ (id ⊗₁ G.ε) ∘ i⇒ ∘ id ⊗₁ λ⇐
        ≈˘⟨ refl⟩∘⟨ pushˡ ⊗.homomorphism ⟩
          F.₁ Cρ⇒ ⊗₁ G.₁ Cρ⇒ ∘ (Fh ∘ id ⊗₁ F.ε) ⊗₁ (Gh ∘ id ⊗₁ G.ε) ∘ i⇒ ∘ id ⊗₁ λ⇐
        ≈˘⟨ pushˡ ⊗.homomorphism ⟩
          (F.₁ Cρ⇒ ∘ Fh ∘ id ⊗₁ F.ε) ⊗₁ (G.₁ Cρ⇒ ∘ Gh ∘ id ⊗₁ G.ε) ∘ i⇒ ∘ id ⊗₁ λ⇐
        ≈⟨ F.unitaryʳ ⟩⊗⟨ G.unitaryʳ ⟩∘⟨refl ⟩
          ρ⇒ ⊗₁ ρ⇒ ∘ i⇒ ∘ id ⊗₁ λ⇐
        ≈⟨ ⊗ˢ.unitaryʳ ⟩
          ρ⇒
        ∎

      braiding-compat = λ {X Y} → begin
          F.₁ Cσ⇒ ⊗₁ G.₁ Cσ⇒ ∘ Fh {X} {Y} ⊗₁ Gh {X} {Y} ∘ i⇒
        ≈⟨ extendʳ (parallel F.braiding-compat G.braiding-compat) ⟩
          (Fh ⊗₁ Gh) ∘ σ⇒ ⊗₁ σ⇒ ∘ i⇒
        ≈⟨ pushʳ ⊗ˢ.braiding-compat ⟩
          (Fh ⊗₁ Gh ∘ i⇒) ∘ σ⇒
        ∎

  _⊗̇₁_ : {F₁ F₂ G₁ G₂ : SymmetricMonoidalFunctor C D} →
         F₁ ⇛ F₂ → G₁ ⇛ G₂ → F₁ ⊗̇₀ G₁ ⇛ F₂ ⊗̇₀ G₂
  _⊗̇₁_ {F₁} {F₂} {G₁} {G₂} β γ = record
    { U               = β.U Underlying.⊗̇₁ γ.U
    ; isMonoidal      = record
      { ε-compat      = ε-compat
      ; ⊗-homo-compat = ⊗-homo-compat
      }
    }
    where
      module F₁ = SymmetricMonoidalFunctor F₁
      module F₂ = SymmetricMonoidalFunctor F₂
      module G₁ = SymmetricMonoidalFunctor G₁
      module G₂ = SymmetricMonoidalFunctor G₂
      module β = SymmetricMonoidalNaturalTransformation β
      module γ = SymmetricMonoidalNaturalTransformation γ

      ε-compat = begin
          β.η C.unit ⊗₁ γ.η C.unit ∘ F₁.ε ⊗₁ G₁.ε ∘ λ⇐
        ≈˘⟨ pushˡ ⊗.homomorphism ⟩
          (β.η C.unit ∘ F₁.ε) ⊗₁ (γ.η C.unit ∘ G₁.ε) ∘ λ⇐
        ≈⟨ β.ε-compat ⟩⊗⟨ γ.ε-compat ⟩∘⟨refl ⟩
          F₂.ε ⊗₁ G₂.ε ∘ λ⇐
        ∎

      ⊗-homo-compat = λ {X Y} → begin
          β.η (X C.⊗₀ Y) ⊗₁ γ.η (X C.⊗₀ Y) ∘
          F₁.⊗-homo.η (X , Y) ⊗₁ G₁.⊗-homo.η (X , Y) ∘ i⇒
        ≈˘⟨ pushˡ ⊗.homomorphism ⟩
          (β.η (X C.⊗₀ Y) ∘ F₁.⊗-homo.η (X , Y)) ⊗₁
          (γ.η (X C.⊗₀ Y) ∘ G₁.⊗-homo.η (X , Y)) ∘ i⇒
        ≈⟨ β.⊗-homo-compat ⟩⊗⟨ γ.⊗-homo-compat ⟩∘⟨refl ⟩
          (F₂.⊗-homo.η (X , Y) ∘ β.η X ⊗₁ β.η Y) ⊗₁
          (G₂.⊗-homo.η (X , Y) ∘ γ.η X ⊗₁ γ.η Y) ∘ i⇒
        ≈⟨ pushˡ ⊗.homomorphism ⟩
          F₂.⊗-homo.η (X , Y) ⊗₁ G₂.⊗-homo.η (X , Y) ∘
          (β.η X ⊗₁ β.η Y) ⊗₁ (γ.η X ⊗₁ γ.η Y) ∘ i⇒
        ≈˘⟨ pullʳ (interchange.⇒.commute ((β.η X , γ.η X) , (β.η Y , γ.η Y))) ⟩
          (F₂.⊗-homo.η (X , Y) ⊗₁ G₂.⊗-homo.η (X , Y) ∘ i⇒) ∘
          (β.η X ⊗₁ γ.η X) ⊗₁ (β.η Y ⊗₁ γ.η Y)
        ∎

  -- The constant functor to the unit in D is (lax) monoidal.

  unitF : SymmetricMonoidalFunctor C D
  unitF = record
    { F                 = Underlying.unitF
    ; isBraidedMonoidal = record
      { isMonoidal      = record
        { ε             = id
        ; ⊗-homo        = Underlying.unitF-⊗-homo.F⇒G
        ; associativity = begin
          id ∘ λ⇒ ∘ λ⇒ ⊗₁ id  ≈⟨ identityˡ ⟩
          λ⇒ ∘ λ⇒ ⊗₁ id       ≈˘⟨ refl⟩∘⟨ coherence₁ ⟩
          λ⇒ ∘ λ⇒ ∘ α⇒        ≈˘⟨ extendʳ unitorˡ-commute-from ⟩
          λ⇒ ∘ id ⊗₁ λ⇒ ∘ α⇒  ∎
        ; unitaryˡ      = begin
          id ∘ λ⇒ ∘ id ⊗₁ id  ≈⟨ identityˡ ⟩
          λ⇒ ∘ id ⊗₁ id       ≈⟨ refl⟩∘⟨ ⊗.identity ⟩
          λ⇒ ∘ id             ≈⟨ identityʳ ⟩
          λ⇒                  ∎
        ; unitaryʳ      = begin
          id ∘ λ⇒ ∘ id ⊗₁ id  ≈⟨ identityˡ ⟩
          λ⇒ ∘ id ⊗₁ id       ≈⟨ refl⟩∘⟨ ⊗.identity ⟩
          λ⇒ ∘ id             ≈⟨ identityʳ ⟩
          λ⇒                  ≈⟨ coherence₃ ⟩
          ρ⇒                  ∎

        }
      ; braiding-compat = begin
        id ∘ λ⇒               ≈⟨ identityˡ ⟩
        λ⇒                    ≈⟨ coherence₃ ⟩
        ρ⇒                    ≈˘⟨ braiding-coherence ⟩
        λ⇒ ∘ braiding.⇒.η _   ∎
      }
    }
  module unitF = SymmetricMonoidalFunctor unitF

  -- The pointwise tensor product and the unit functor induce a
  -- symmetric monoidal structure on symmetric monoidal functors.

  ⊗̇-unitorˡ : {F : SymmetricMonoidalFunctor C D} → unitF ⊗̇₀ F ≃ F
  ⊗̇-unitorˡ {F} = record
    { U               = Underlying.⊗̇-unitorˡ
    ; F⇒G-isMonoidal  = record
      { ε-compat      = ε-compat
      ; ⊗-homo-compat = ⊗-homo-compat
      }
    }
    where
      open SymmetricMonoidalFunctor F

      ε-compat = begin
        λ⇒ ∘ id ⊗₁ ε ∘ λ⇐   ≈⟨ extendʳ unitorˡ-commute-from ⟩
        ε ∘ λ⇒ ∘ λ⇐         ≈⟨ elimʳ λᵢ.isoʳ ⟩
        ε                   ∎

      ⊗-homo-compat = λ {X Y} → let h = ⊗-homo.η (X , Y) in begin
          λ⇒ ∘ λ⇒ ⊗₁ h ∘ i⇒
        ≈⟨ pullˡ (refl⟩∘⟨ serialize₂₁) ⟩
          (λ⇒ ∘ id ⊗₁ h ∘ λ⇒ ⊗₁ id) ∘ i⇒
        ≈⟨ extendʳ unitorˡ-commute-from ⟩∘⟨ i-selfInverse ⟩
          (h ∘ λ⇒ ∘ λ⇒ ⊗₁ id) ∘ i⇐
        ≈˘⟨ pushʳ (switch-fromtoʳ i (switch-tofromʳ (λᵢ ⊗ᵢ idᵢ)
                                                    (assoc ○ ⊗ˢ.unitaryˡ))) ⟩
          h ∘ λ⇒ ⊗₁ λ⇒
        ∎

  ⊗̇-unitorʳ : {F : SymmetricMonoidalFunctor C D} → F ⊗̇₀ unitF ≃ F
  ⊗̇-unitorʳ {F} = record
    { U               = Underlying.⊗̇-unitorʳ
    ; F⇒G-isMonoidal  = record
      { ε-compat      = ε-compat
      ; ⊗-homo-compat = ⊗-homo-compat
      }
    }
    where
      open SymmetricMonoidalFunctor F

      ε-compat = begin
        ρ⇒ ∘ ε ⊗₁ id ∘ λ⇐   ≈⟨ extendʳ unitorʳ-commute-from ⟩
        ε ∘ ρ⇒ ∘ λ⇐         ≈˘⟨ refl⟩∘⟨ coherence₃ ⟩∘⟨refl ⟩
        ε ∘ λ⇒ ∘ λ⇐         ≈⟨ elimʳ λᵢ.isoʳ ⟩
        ε                   ∎

      ⊗-homo-compat = λ {X Y} → let h = ⊗-homo.η (X , Y) in begin
          ρ⇒ ∘ h ⊗₁ λ⇒ ∘ i⇒
        ≈⟨ pullˡ (refl⟩∘⟨ serialize₁₂) ⟩
          (ρ⇒ ∘ h ⊗₁ id ∘ id ⊗₁ λ⇒) ∘ i⇒
        ≈⟨ extendʳ unitorʳ-commute-from ⟩∘⟨ i-selfInverse ⟩
          (h ∘ ρ⇒ ∘ id ⊗₁ λ⇒) ∘ i⇐
        ≈˘⟨ pushʳ (switch-fromtoʳ i (switch-tofromʳ (idᵢ ⊗ᵢ λᵢ)
                                                    (assoc ○ ⊗ˢ.unitaryʳ))) ⟩
          h ∘ ρ⇒ ⊗₁ ρ⇒
        ∎

  ⊗̇-associator : {F G H : SymmetricMonoidalFunctor C D} →
                 (F ⊗̇₀ G) ⊗̇₀ H ≃ F ⊗̇₀ (G ⊗̇₀ H)
  ⊗̇-associator {F} {G} {H} = record
    { U               = Underlying.⊗̇-associator
    ; F⇒G-isMonoidal  = record
      { ε-compat      = ε-compat
      ; ⊗-homo-compat = ⊗-homo-compat
      }
    }
    where
      module F = SymmetricMonoidalFunctor F
      module G = SymmetricMonoidalFunctor G
      module H = SymmetricMonoidalFunctor H
      Fh = λ {X Y} → F.⊗-homo.η (X , Y)
      Gh = λ {X Y} → G.⊗-homo.η (X , Y)
      Hh = λ {X Y} → H.⊗-homo.η (X , Y)

      ε-compat = begin
          α⇒ ∘ (F.ε ⊗₁ G.ε ∘ λ⇐) ⊗₁ H.ε ∘ λ⇐
        ≈⟨ pullˡ (pushʳ split₁ʳ) ⟩
          ((α⇒ ∘ (F.ε ⊗₁ G.ε) ⊗₁ H.ε) ∘ λ⇐ ⊗₁ id) ∘ λ⇐
        ≈⟨ pushˡ assoc-commute-from ⟩∘⟨refl ⟩
          (F.ε ⊗₁ (G.ε ⊗₁ H.ε) ∘ α⇒ ∘ λ⇐ ⊗₁ id) ∘ λ⇐
        ≈⟨ (refl⟩∘⟨ helper) ⟩∘⟨refl ⟩
          (F.ε ⊗₁ (G.ε ⊗₁ H.ε) ∘ id ⊗₁ λ⇐) ∘ λ⇐
        ≈˘⟨ split₂ʳ ⟩∘⟨refl ⟩
          F.ε ⊗₁ (G.ε ⊗₁ H.ε ∘ λ⇐) ∘ λ⇐
        ∎
        where
          helper = begin
            α⇒ ∘ λ⇐ ⊗₁ id    ≈⟨ refl⟩∘⟨ coherence-inv₃ ⟩⊗⟨refl ⟩
            α⇒ ∘ ρ⇐ ⊗₁ id    ≈˘⟨ conjugate-from (ρᵢ ⊗ᵢ idᵢ) (idᵢ ⊗ᵢ λᵢ)
                                                (identityˡ ○ ⟺ triangle) ⟩
            id ⊗₁ λ⇐ ∘ id    ≈⟨ identityʳ ⟩
            id ⊗₁ λ⇐         ∎

      ⊗-homo-compat = λ {X Y} → begin
          α⇒ ∘ (Fh {X} {Y} ⊗₁ Gh {X} {Y} ∘ i⇒) ⊗₁ Hh {X} {Y} ∘ i⇒
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ i-selfInverse) ⟩⊗⟨refl ⟩∘⟨ i-selfInverse ⟩
          α⇒ ∘ (Fh ⊗₁ Gh ∘ i⇐) ⊗₁ Hh ∘ i⇐
        ≈⟨ refl⟩∘⟨ pushˡ split₁ʳ ⟩
          α⇒ ∘ (Fh ⊗₁ Gh) ⊗₁ Hh ∘ i⇐ ⊗₁ id ∘ i⇐
        ≈⟨ extendʳ assoc-commute-from ⟩
          Fh ⊗₁ (Gh  ⊗₁ Hh) ∘ α⇒ ∘ i⇐ ⊗₁ id ∘ i⇐
        ≈˘⟨ refl⟩∘⟨ conjugate-from (i ∘ᵢ i ⊗ᵢ idᵢ) (i ∘ᵢ idᵢ ⊗ᵢ i)
                                   (⊗ˢ.associativity ○ sym-assoc) ⟩
          Fh ⊗₁ (Gh  ⊗₁ Hh) ∘ (id ⊗₁ i⇐ ∘ i⇐) ∘ α⇒ ⊗₁ α⇒
        ≈˘⟨ pushˡ (pushˡ split₂ʳ) ⟩
          (Fh ⊗₁ (Gh ⊗₁ Hh ∘ i⇐) ∘ i⇐) ∘ α⇒ ⊗₁ α⇒
        ≈˘⟨ (refl⟩⊗⟨ (refl⟩∘⟨ i-selfInverse) ⟩∘⟨
                              i-selfInverse) ⟩∘⟨refl ⟩
          (Fh ⊗₁ (Gh ⊗₁ Hh ∘ i⇒) ∘ i⇒) ∘ α⇒ ⊗₁ α⇒
        ∎

  ⊗̇-braiding : {F G : SymmetricMonoidalFunctor C D } → F ⊗̇₀ G ≃ G ⊗̇₀ F
  ⊗̇-braiding {F} {G} = record
    { U               = Underlying.⊗̇-braiding
    ; F⇒G-isMonoidal  = record
      { ε-compat      = ε-compat
      ; ⊗-homo-compat = ⊗-homo-compat
      }
    }
    where
      module F = SymmetricMonoidalFunctor F
      module G = SymmetricMonoidalFunctor G
      Fh = λ {X Y} → F.⊗-homo.η (X , Y)
      Gh = λ {X Y} → G.⊗-homo.η (X , Y)

      ε-compat = begin
        σ⇒ ∘ F.ε ⊗₁ G.ε ∘ λ⇐   ≈⟨  extendʳ (braiding.⇒.commute (F.ε , G.ε)) ⟩
        G.ε ⊗₁ F.ε ∘ σ⇒ ∘ λ⇐   ≈⟨  refl⟩∘⟨ refl⟩∘⟨ coherence-inv₃ ⟩
        G.ε ⊗₁ F.ε ∘ σ⇒ ∘ ρ⇐   ≈˘⟨ refl⟩∘⟨ conjugate-from ρᵢ λᵢ
                                     (identityˡ ○ ⟺ braiding-coherence) ⟩
        G.ε ⊗₁ F.ε ∘ λ⇐ ∘ id   ≈⟨ refl⟩∘⟨ identityʳ ⟩
        G.ε ⊗₁ F.ε ∘ λ⇐        ∎

      ⊗-homo-compat : ∀ {X Y} →
                        σ⇒ ∘ Fh {X} {Y} ⊗₁ Gh {X} {Y} ∘ i⇒
                      ≈ (Gh ⊗₁ Fh ∘ i⇒) ∘ σ⇒ ⊗₁ σ⇒
      ⊗-homo-compat {X} {Y} = begin
        σ⇒ ∘ Fh ⊗₁ Gh ∘ i⇒           ≈⟨ extendʳ (braiding.⇒.commute (Fh , Gh)) ⟩
        Gh ⊗₁ Fh ∘ σ⇒ ∘ i⇒           ≈⟨ pushʳ (conjugate-to i-iso′ i-iso′
                                          (⟺ ⊗ˢ.braiding-compat)) ⟩
        (Gh ⊗₁ Fh ∘ i⇒) ∘ σ⇒ ⊗₁ σ⇒   ∎

  module ⊗̇-unitorˡ {F} = SymmetricMonoidalNaturalIsomorphism (⊗̇-unitorˡ {F})
  module ⊗̇-unitorʳ {F} = SymmetricMonoidalNaturalIsomorphism (⊗̇-unitorʳ {F})
  module ⊗̇-associator {F} {G} {H} =
    SymmetricMonoidalNaturalIsomorphism (⊗̇-associator {F} {G} {H})
  module ⊗̇-braiding {F} {G} =
    SymmetricMonoidalNaturalIsomorphism (⊗̇-braiding {F} {G})

module Strong where
  open SF.Strong
  open SMNT.Strong using (SymmetricMonoidalNaturalTransformation)
  open SMNI.Strong using (SymmetricMonoidalNaturalIsomorphism; _≃_)
  open SymmetricMonoidalFunctor using ()
    renaming (laxSymmetricMonoidalFunctor to laxSMF)

  private
    infix 4 _⇛_
    _⇛_ = SymmetricMonoidalNaturalTransformation

  infixr 10 _⊗̇₀_ _⊗̇₁_

  -- The pointwise tensor product of strong symmetric monoidal functors.

  _⊗̇₀_ : (F G : SymmetricMonoidalFunctor C D) → SymmetricMonoidalFunctor C D
  F ⊗̇₀ G = record
    { F                  = F.F Underlying.⊗̇₀ G.F
    ; isBraidedMonoidal  = record
      { isStrongMonoidal = record
        { ε              = F.ε ⊗ᵢ G.ε ∘ᵢ ⊗ˢ.ε
        ; ⊗-homo         = niHelper (record
          { η            = ⊗-homoᵢ.from
          ; η⁻¹          = ⊗-homoᵢ.to
          ; commute      = ⊗-homo.commute
          ; iso          = ⊗-homoᵢ.iso
          })
        ; associativity  = associativity
        ; unitaryˡ       = unitaryˡ
        ; unitaryʳ       = unitaryʳ
        }
      ; braiding-compat  = braiding-compat
      }
    }
    where
      module F = SymmetricMonoidalFunctor F
      module G = SymmetricMonoidalFunctor G
      ⊗-homoᵢ = λ XY → F.⊗-homo.FX≅GX {XY} ⊗ᵢ G.⊗-homo.FX≅GX {XY} ∘ᵢ i
      module ⊗-homoᵢ XY = _≅_ (⊗-homoᵢ XY)
      open SF.Lax.SymmetricMonoidalFunctor (laxSMF F Lax.⊗̇₀ laxSMF G)

  _⊗̇₁_ : {F₁ F₂ G₁ G₂ : SymmetricMonoidalFunctor C D} →
         F₁ ⇛ F₂ → G₁ ⇛ G₂ → F₁ ⊗̇₀ G₁ ⇛ F₂ ⊗̇₀ G₂
  _⊗̇₁_ β γ = record
    { U               = β.U Underlying.⊗̇₁ γ.U
    ; isMonoidal      = record
      { ε-compat      = ε-compat
      ; ⊗-homo-compat = λ {X Y} → ⊗-homo-compat
      }
    }
    where
      module β = SymmetricMonoidalNaturalTransformation β
      module γ = SymmetricMonoidalNaturalTransformation γ
      open SMNT.Lax.SymmetricMonoidalNaturalTransformation (β.laxSNT Lax.⊗̇₁ γ.laxSNT)

  -- The constant functor to the unit in D is (strong) monoidal.

  unitF : SymmetricMonoidalFunctor C D
  unitF = record
    { F                  = Underlying.unitF
    ; isBraidedMonoidal  = record
      { isStrongMonoidal = record
        { ε              = idᵢ
        ; ⊗-homo         = Underlying.unitF-⊗-homo
        ; associativity  = λ {X Y Z} → Lax.unitF.associativity {X = X} {Y} {Z}
        ; unitaryˡ       = λ {X} → Lax.unitF.unitaryˡ {X = X}
        ; unitaryʳ       = λ {X} → Lax.unitF.unitaryʳ {X = X}
        }
      ; braiding-compat  = λ {X Y} → Lax.unitF.braiding-compat {X = X} {Y}
      }
    }
  module unitF = SymmetricMonoidalFunctor unitF

  -- The pointwise tensor product and the unit functor induce a
  -- symmetric monoidal structure on symmetric monoidal functors.

  ⊗̇-unitorˡ : {F : SymmetricMonoidalFunctor C D} → unitF ⊗̇₀ F ≃ F
  ⊗̇-unitorˡ {F} = record
    { U               = U
    ; F⇒G-isMonoidal  = record
      { ε-compat      = ε-compat
      ; ⊗-homo-compat = λ {X Y} → ⊗-homo-compat {X = X} {Y}
      }
    }
    where open SMNI.Lax.SymmetricMonoidalNaturalIsomorphism (Lax.⊗̇-unitorˡ {F = laxSMF F})

  ⊗̇-unitorʳ : {F : SymmetricMonoidalFunctor C D} → F ⊗̇₀ unitF ≃ F
  ⊗̇-unitorʳ {F} = record
    { U               = U
    ; F⇒G-isMonoidal  = record
      { ε-compat      = ε-compat
      ; ⊗-homo-compat = λ {X Y} → ⊗-homo-compat {X = X} {Y}
      }
    }
    where open SMNI.Lax.SymmetricMonoidalNaturalIsomorphism (Lax.⊗̇-unitorʳ {F = laxSMF F})

  ⊗̇-associator : {F G H : SymmetricMonoidalFunctor C D} →
                 (F ⊗̇₀ G) ⊗̇₀ H ≃ F ⊗̇₀ (G ⊗̇₀ H)
  ⊗̇-associator {F} {G} {H} = record
    { U               = U
    ; F⇒G-isMonoidal  = record
      { ε-compat      = ε-compat
      ; ⊗-homo-compat = λ {X Y} → ⊗-homo-compat {X = X} {Y}
      }
    }
    where open SMNI.Lax.SymmetricMonoidalNaturalIsomorphism (Lax.⊗̇-associator {F = laxSMF F} {laxSMF G} {laxSMF H})

  ⊗̇-braiding : {F G : SymmetricMonoidalFunctor C D } → F ⊗̇₀ G ≃ G ⊗̇₀ F
  ⊗̇-braiding {F} {G} = record
    { U               = U
    ; F⇒G-isMonoidal  = record
      { ε-compat      = ε-compat
      ; ⊗-homo-compat = λ {X Y} → ⊗-homo-compat {X = X} {Y}
      }
    }
    where open SMNI.Lax.SymmetricMonoidalNaturalIsomorphism (Lax.⊗̇-braiding {F = laxSMF F} {laxSMF G})

  module ⊗̇-unitorˡ {F} = SymmetricMonoidalNaturalIsomorphism (⊗̇-unitorˡ {F})
  module ⊗̇-unitorʳ {F} = SymmetricMonoidalNaturalIsomorphism (⊗̇-unitorʳ {F})
  module ⊗̇-associator {F} {G} {H} =
    SymmetricMonoidalNaturalIsomorphism (⊗̇-associator {F} {G} {H})
  module ⊗̇-braiding {F} {G} =
    SymmetricMonoidalNaturalIsomorphism (⊗̇-braiding {F} {G})
