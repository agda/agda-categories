{-# OPTIONS --without-K --safe #-}

open import Categories.Category using () renaming (Category to Setoid-Category)
open import Categories.Category.Monoidal

module Categories.Enriched.NaturalTransformation.NaturalIsomorphism
  {o ℓ e} {V : Setoid-Category o ℓ e} (M : Monoidal V) where

open import Level

open import Categories.Category.Construction.EnrichedFunctors M
open import Categories.Enriched.Category M
open import Categories.Enriched.Category.Underlying M
open import Categories.Enriched.Functor M renaming (id to idF)
open import Categories.Enriched.NaturalTransformation M renaming (id to idNT)
open import Categories.Functor.Properties using ([_]-resp-Iso)
open import Categories.Morphism as Morphism using (Iso)
open import Categories.Category.Monoidal.Reasoning M
open import Relation.Binary using (IsEquivalence)

open Setoid-Category V renaming (Obj to ObjV; id to idV)
module M = Monoidal M
open M hiding (unitorˡ; unitorʳ; associator)
open NaturalTransformation

module NaturalIsomorphism = Morphism._≅_
open NaturalIsomorphism

-- A natural isomorphism |α : F ≅ G : C → D| is an isomorphism of F
-- and G in the functor category [C , D] between C and D.

module _ {c d} {C : Category c} {D : Category d} where

  NaturalIsomorphism : (F G : Functor C D) → Set (ℓ ⊔ e ⊔ c)
  NaturalIsomorphism F G = F ≅ G
    where open Morphism (EnrichedFunctors C D) using (_≅_)

  -- A commonly used shorthand for NaturalIsomorphism

  infix 4 _≃_

  _≃_ = NaturalIsomorphism

  module _ {F G : Functor C D} where
    private
      module F = Functor F
      module G = Functor G
    open Morphism (Underlying D) using (_≅_)

    -- Natural isomorphisms are pointwise isomorphisms: each component
    -- |α [ X ]| is an isomorphism |F X ≅ G X|.

    infixl 16 _ᵢ[_]

    _ᵢ[_] : NaturalIsomorphism F G → ∀ X → F.₀ X ≅ G.₀ X
    α ᵢ[ X ] = record
      { from = from α [ X ]
      ; to   = to α   [ X ]
      ; iso  = record { isoˡ = isoˡ α ; isoʳ = isoʳ α }
      }

  ≃-isEquivalence : IsEquivalence _≃_
  ≃-isEquivalence = Morphism.≅-isEquivalence (EnrichedFunctors C D)

  module ≃ = IsEquivalence ≃-isEquivalence

  id : {F : Functor C D} → F ≃ F
  id = ≃.refl

  _⁻¹ : {F G : Functor C D} → F ≃ G → G ≃ F
  α ⁻¹ = ≃.sym α

  infixr 9 _ⓘᵥ_

  _ⓘᵥ_ : {F G H : Functor C D} → G ≃ H → F ≃ G → F ≃ H
  α ⓘᵥ β = ≃.trans β α

  private
    module D = Underlying D

  -- Left and right unitors

  unitorˡ : {F : Functor C D} → idF ∘F F ≃ F
  unitorˡ {F} = record
    { from = record
      { comp    = λ _ → D.id
      ; commute = (refl⟩∘⟨ refl⟩⊗⟨ identityˡ ⟩∘⟨refl) ○ comm
      }
    ; to = record
      { comp    = λ _ → D.id
      ; commute = comm ○ (refl⟩∘⟨ ⟺ identityˡ ⟩⊗⟨refl ⟩∘⟨refl)
      }
    ; iso = record { isoˡ = D.identity² ; isoʳ = D.identity² }
    }
    where comm = commute (idNT {F = F})

  unitorʳ : {F : Functor C D} → F ∘F idF ≃ F
  unitorʳ {F} = record
    { from = record
      { comp    = λ _ → D.id
      ; commute = (refl⟩∘⟨ refl⟩⊗⟨ identityʳ ⟩∘⟨refl) ○ comm
      }
    ; to = record
      { comp    = λ _ → D.id
      ; commute = comm ○ (refl⟩∘⟨ ⟺ identityʳ ⟩⊗⟨refl ⟩∘⟨refl)
      }
    ; iso = record { isoˡ = D.identity² ; isoʳ = D.identity² }
    }
    where comm = commute (idNT {F = F})

module _ {c d e} {C : Category c} {D : Category d} {E : Category e} where
  open NaturalIsomorphism

  -- Left- and right-hand composition with a functor

  infixr 9 _ⓘₕ_ _ⓘˡ_ _ⓘʳ_

  _ⓘˡ_ : {F G : Functor C D} (H : Functor D E) → F ≃ G → H ∘F F ≃ H ∘F G
  H ⓘˡ α = record
    { from = H ∘ˡ from α
    ; to   = H ∘ˡ to α
    ; iso  = record { isoˡ = iso.isoˡ ; isoʳ = iso.isoʳ }
    }
    where
      module iso {X} = Iso ([ UnderlyingFunctor H ]-resp-Iso (iso (α ᵢ[ X ])))

  _ⓘʳ_ : {G H : Functor D E} → G ≃ H → (F : Functor C D) → G ∘F F ≃ H ∘F F
  α ⓘʳ F = record
    { from = from α ∘ʳ F
    ; to   = to α   ∘ʳ F
    ; iso  = record { isoˡ = isoˡ (α ᵢ[ F.₀ _ ]) ; isoʳ = isoʳ (α ᵢ[ F.₀ _ ]) }
    }
    where module F = Functor F

  -- Horizontal composition

  _ⓘₕ_ : {H I : Functor D E} {F G : Functor C D} →
           H ≃ I → F ≃ G → (H ∘F F) ≃ (I ∘F G)
  _ⓘₕ_ {_} {I} {F} {_} α β = (I ⓘˡ β) ⓘᵥ (α ⓘʳ F)

module _ {b c d e} {B : Category b} {C : Category c}
                   {D : Category d} {E : Category e} where
  open NaturalIsomorphism
  private
    module E  = Category E
    module UE = Underlying E

  -- Associator

  associator : {F : Functor D E} {G : Functor C D} {H : Functor B C} →
               (F ∘F G) ∘F H ≃ F ∘F (G ∘F H)
  associator {F} {G} {H} = record
    { from = record
      { comp    = λ _ → E.id
      ; commute = (refl⟩∘⟨ refl⟩⊗⟨ assoc ⟩∘⟨refl) ○ comm
      }
    ; to = record
      { comp    = λ _ → E.id
      ; commute = comm ○ (refl⟩∘⟨ sym-assoc ⟩⊗⟨refl ⟩∘⟨refl)
      }
    ; iso = record { isoˡ = UE.identity² ; isoʳ = UE.identity² }
    }
    where comm = commute (idNT {F = F ∘F (G ∘F H)})
