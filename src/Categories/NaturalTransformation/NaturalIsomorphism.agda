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
                          (F G : Functor C D) : Set (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) where

  private
    module F = Functor F
    module G = Functor G

  field
    F⇒G : NaturalTransformation F G
    F⇐G : NaturalTransformation G F

  module ⇒ = NaturalTransformation F⇒G
  module ⇐ = NaturalTransformation F⇐G

  field
    iso : ∀ X → Morphism.Iso D (⇒.η X) (⇐.η X)

  module iso X = Morphism.Iso (iso X)

  open Morphism D

  FX≅GX : ∀ {X} → F.F₀ X ≅ G.F₀ X
  FX≅GX {X} = record
    { from = _
    ; to   = _
    ; iso  = iso X
    }

  op : NaturalIsomorphism G.op F.op
  op = record
    { F⇒G = ⇒.op
    ; F⇐G = ⇐.op
    ; iso = λ X → record
      { isoˡ = iso.isoʳ X
      ; isoʳ = iso.isoˡ X
      }
    }

  op′ : NaturalIsomorphism F.op G.op
  op′ = record
    { F⇒G = ⇐.op
    ; F⇐G = ⇒.op
    ; iso = λ X → record
      { isoˡ = iso.isoˡ X
      ; isoʳ = iso.isoʳ X
      }
    }

-- This helper definition lets us specify only one of the commuting
-- squares and have the other one derived.

record NIHelper {C : Category o ℓ e}
                {D : Category o′ ℓ′ e′}
                (F G : Functor C D) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  open Functor F using (F₀; F₁)
  open Functor G using () renaming (F₀ to G₀; F₁ to G₁)
  open Category D
  field
    η           : ∀ X → D [ F₀ X , G₀ X ]
    η⁻¹         : ∀ X → D [ G₀ X , F₀ X ]
    commute     : ∀ {X Y} (f : C [ X , Y ]) → η Y ∘ F₁ f ≈ G₁ f ∘ η X
    iso         : ∀ X → Morphism.Iso D (η X) (η⁻¹ X)

niHelper : ∀ {F G : Functor C D} → NIHelper F G → NaturalIsomorphism F G
niHelper {D = D} {F = F} {G = G} α = record
  { F⇒G = ntHelper record { η = η ; commute = commute }
  ; F⇐G = ntHelper record
    { η = η⁻¹
    ; commute = λ {X Y} f → begin
        η⁻¹ Y ∘ F₁ G f                     ≈˘⟨ cancelʳ (isoʳ (iso X)) ⟩
        ((η⁻¹ Y ∘ F₁ G f) ∘ η X) ∘ η⁻¹ X   ≈˘⟨ pushʳ (commute f) ⟩∘⟨refl ⟩
        (η⁻¹ Y ∘ (η Y ∘ F₁ F f)) ∘ η⁻¹ X   ≈⟨ cancelˡ (isoˡ (iso Y)) ⟩∘⟨refl ⟩
        F₁ F f ∘ η⁻¹ X                     ∎
    }
  ; iso = iso
  }
  where
    open Morphism.Iso
    open NIHelper α
    open Functor
    open Category D
    open HomReasoning
    open MR D

open NaturalIsomorphism

infixr 9 _ⓘᵥ_ _ⓘₕ_ _ⓘˡ_ _ⓘʳ_
infix 4 _≃_

-- commonly used short-hand in CT for NaturalIsomorphism
_≃_ : (F G : Functor C D) → Set _
_≃_ = NaturalIsomorphism

_ⓘᵥ_ : {F G H : Functor C D} → G ≃ H → F ≃ G → F ≃ H
_ⓘᵥ_ {D = D} α β = record
  { F⇒G = F⇒G α ∘ᵥ F⇒G β
  ; F⇐G = F⇐G β ∘ᵥ F⇐G α
  ; iso = λ X → Iso-∘ (iso β X) (iso α X)
  }
  where open NaturalIsomorphism
        open Morphismₚ D

_ⓘₕ_ : {H I : Functor D E} {F G : Functor C D} → H ≃ I → F ≃ G → (H ∘F F) ≃ (I ∘F G)
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

_ⓘˡ_ : {F G : Functor C D} → (H : Functor D E) → (η : F ≃ G) → H ∘F F ≃ H ∘F G
H ⓘˡ η = record
  { F⇒G = H ∘ˡ F⇒G η
  ; F⇐G = H ∘ˡ F⇐G η
  ; iso = λ X → [ H ]-resp-Iso (iso η X)
  }
  where open Functor H

_ⓘʳ_ : {F G : Functor C D} → (η : F ≃ G) → (K : Functor E C) → F ∘F K ≃ G ∘F K
η ⓘʳ K = record
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
trans = flip _ⓘᵥ_

isEquivalence : {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → IsEquivalence (NaturalIsomorphism {C = C} {D = D})
isEquivalence = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }

module ≃ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} = IsEquivalence (isEquivalence {C = C} {D = D})

Functor-NI-setoid : (C : Category o ℓ e) (D : Category o′ ℓ′ e′) → Setoid _ _
Functor-NI-setoid C D = record
  { Carrier       = Functor C D
  ; _≈_           = NaturalIsomorphism
  ; isEquivalence = isEquivalence
  }

module LeftRightId (F : Functor C D) where
  module D = Category D

  iso-id-id : (X : Category.Obj C) → Morphism.Iso D {A = Functor.F₀ F X} D.id D.id
  iso-id-id X = record { isoˡ = D.identityˡ ; isoʳ = D.identityʳ }

-- Left and Right and 'Central' Unitors, Natural Isomorphisms.
module _ {F : Functor C D} where
  open Category.HomReasoning D
  open Functor F
  open LeftRightId F
  open Category D

  unitorˡ : ℱ.id ∘F F ≃ F
  unitorˡ = record { F⇒G = id∘F⇒F ; F⇐G = F⇒id∘F ; iso = iso-id-id }

  unitorʳ : F ∘F ℱ.id ≃ F
  unitorʳ = record { F⇒G = F∘id⇒F ; F⇐G = F⇒F∘id ; iso = iso-id-id }

unitor² : {C : Category o ℓ e} → ℱ.id ∘F ℱ.id ≃ ℱ.id {C = C}
unitor² = record { F⇒G = id∘id⇒id ; F⇐G = id⇒id∘id ; iso = LeftRightId.iso-id-id ℱ.id }

-- associator
module _ (F : Functor B C) (G : Functor C D) (H : Functor D E) where
  open Category.HomReasoning E
  open Category E
  open Functor
  open LeftRightId (H ∘F (G ∘F F))

  private
    -- components of α
    assocʳ : NaturalTransformation ((H ∘F G) ∘F F) (H ∘F (G ∘F F))
    assocʳ = ntHelper record { η = λ _ → id ; commute = λ _ → MR.id-comm-sym E  }

    assocˡ : NaturalTransformation (H ∘F (G ∘F F)) ((H ∘F G) ∘F F)
    assocˡ = ntHelper record { η = λ _ → id ; commute = λ _ → MR.id-comm-sym E }

  associator : (H ∘F G) ∘F F ≃ H ∘F (G ∘F F)
  associator = record { F⇒G = assocʳ ; F⇐G = assocˡ ; iso = iso-id-id }

  -- useful when building functor categories
  sym-associator : H ∘F (G ∘F F) ≃ (H ∘F G) ∘F F
  sym-associator = record { F⇒G = assocˡ ; F⇐G = assocʳ ; iso = iso-id-id }
