{-# OPTIONS --without-K --safe #-}

module Categories.NaturalTransformation.NaturalIsomorphism where

open import Level
open import Data.Product using (_×_; _,_; map; zip)
open import Function using (flip)

open import Categories.Category
open import Categories.Functor as ℱ renaming (id to idF)
import Categories.NaturalTransformation as NT
open NT hiding (id)
import Categories.Morphism as Morphism
import Categories.Morphism.Properties as Morphismₚ
import Categories.Morphism.Reasoning as MR
open import Categories.Functor.Properties

open import Relation.Binary

private
  variable
    o ℓ e o′ ℓ′ e′ : Level
    B C D E : Category o ℓ e

record NaturalIsomorphism {C : Category o ℓ e}
                          {D : Category o′ ℓ′ e′}
                          (F G : Functor C D) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  field
    F⇒G : NaturalTransformation F G
    F⇐G : NaturalTransformation G F

  module ⇒ = NaturalTransformation F⇒G
  module ⇐ = NaturalTransformation F⇐G

  field
    iso : ∀ X → Morphism.Iso D (⇒.η X) (⇐.η X)

  module iso X = Morphism.Iso (iso X)

open NaturalIsomorphism

infixr 9 _ⓘᵥ_ _ⓘₕ_ _ⓘˡ_ _ⓘʳ_

_ⓘᵥ_ : ∀ {F G H : Functor C D} →
         NaturalIsomorphism G H → NaturalIsomorphism F G → NaturalIsomorphism F H
_ⓘᵥ_ {D = D} α β = record
  { F⇒G = F⇒G α ∘ᵥ F⇒G β
  ; F⇐G = F⇐G β ∘ᵥ F⇐G α
  ; iso = λ X → Iso-∘ (iso β X) (iso α X)
  }
  where open NaturalIsomorphism
        open Morphismₚ D

_ⓘₕ_ : ∀ {H I : Functor D E} {F G : Functor C D} →
         NaturalIsomorphism H I → NaturalIsomorphism F G → NaturalIsomorphism (H ∘F F) (I ∘F G)
_ⓘₕ_ {E = E} {I = I} α β = record
  { F⇒G = F⇒G α ∘ₕ F⇒G β
  ; F⇐G = F⇐G α ∘ₕ F⇐G β
  ; iso = λ X → Iso-resp-≈ (Iso-∘ (iso α _) ([ I ]-resp-Iso (iso β X)))
                           E.Equiv.refl (commute (F⇐G α) (η (F⇐G β) X))
  }
  where open NaturalIsomorphism
        open NaturalTransformation
        module E = Category E
        open E.Equiv
        open Morphismₚ E

_ⓘˡ_ : ∀ {F G : Functor C D} →
         (H : Functor D E) → (η : NaturalIsomorphism F G) → NaturalIsomorphism (H ∘F F) (H ∘F G)
_ⓘˡ_ {C = C} {E = E} H η = record
  { F⇒G = H ∘ˡ F⇒G η
  ; F⇐G = H ∘ˡ F⇐G η
  ; iso = λ X → [ H ]-resp-Iso (iso η X)
  }
  where open Functor H

_ⓘʳ_ : ∀ {F G : Functor C D} →
         (η : NaturalIsomorphism F G) → (K : Functor E C) → NaturalIsomorphism (F ∘F K) (G ∘F K)
_ⓘʳ_ η K = record
  { F⇒G = F⇒G η ∘ʳ K
  ; F⇐G = F⇐G η ∘ʳ K
  ; iso = λ X → iso η (F₀ X)
  }
  where open Functor K

refl : Reflexive (NaturalIsomorphism {C = C} {D = D})
refl {D = D} = record
  { F⇒G = NT.id
  ; F⇐G = NT.id
  ; iso = λ _ → record
    { isoˡ = Category.identityˡ D
    ; isoʳ = Category.identityʳ D
    }
  }

sym : Symmetric (NaturalIsomorphism {C = C} {D = D})
sym {D = D} F≃G = record
  { F⇒G = F⇐G F≃G
  ; F⇐G = F⇒G F≃G
  ; iso = λ X →
    let open Iso (iso F≃G X) in record
    { isoˡ = isoʳ
    ; isoʳ = isoˡ
    }
  }
  where open Morphism D

trans : Transitive (NaturalIsomorphism {C = C} {D = D})
trans {D = D} = flip _ⓘᵥ_

isEquivalence : {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → IsEquivalence (NaturalIsomorphism {C = C} {D = D})
isEquivalence = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }

Functor-setoid : (C : Category o ℓ e) (D : Category o′ ℓ′ e′) → Setoid _ _
Functor-setoid C D = record
  { Carrier       = Functor C D
  ; _≈_           = NaturalIsomorphism
  ; isEquivalence = isEquivalence
  }



-- Left and Right Unitors, Natural Isomorphisms.
module _ {F : Functor C D} where
  open Category.HomReasoning D
  open Functor F
  open LeftRightId F
  open Category D

  unitorˡ : NaturalIsomorphism (ℱ.id ∘F F) F
  unitorˡ = record { F⇒G = id∘F⇒F ; F⇐G = F⇒id∘F ; iso = iso-id-id }

  unitorʳ : NaturalIsomorphism (F ∘F ℱ.id) F
  unitorʳ = record { F⇒G = F∘id⇒F ; F⇐G = F⇒F∘id ; iso = iso-id-id }

-- associator
module _ (F : Functor B C) (G : Functor C D) (H : Functor D E) where
  open Category.HomReasoning E
  open Category E
  open Functor
  open LeftRightId (H ∘F (G ∘F F))

  private
    -- components of α
    assocʳ : NaturalTransformation ((H ∘F G) ∘F F) (H ∘F (G ∘F F))
    assocʳ = record { η = λ _ → id ; commute = comm }

    assocˡ : NaturalTransformation (H ∘F (G ∘F F)) ((H ∘F G) ∘F F)
    assocˡ = record { η = λ _ → id ; commute = comm }

  associator : NaturalIsomorphism ((H ∘F G) ∘F F) (H ∘F (G ∘F F))
  associator = record { F⇒G = assocʳ ; F⇐G = assocˡ ; iso = iso-id-id }
