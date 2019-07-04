{-# OPTIONS --without-K --safe #-}

module Categories.NaturalTransformation.NaturalIsomorphism where

open import Level
open import Data.Product using (_×_; _,_)
open import Relation.Binary using (IsEquivalence)

open import Categories.Category
open import Categories.Functor as ℱ renaming (id to idF)
open import Categories.NaturalTransformation.Core as α hiding (id)
import Categories.NaturalTransformation as NT
import Categories.Morphism as Morphism
import Categories.Morphism.Properties as Morphismₚ
import Categories.Square as Square
open import Categories.Functor.Properties

open import Relation.Binary

private
  variable
    o ℓ e o′ ℓ′ e′ : Level
    B C D E : Category o ℓ e

record NaturalIsomorphism {C : Category o ℓ e}
                          {D : Category o′ ℓ′ e′}
                          (F G : Functor C D) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private module C = Category C
  private module D = Category D
  private module F = Functor F
  private module G = Functor G
  open F
  open G renaming (F₀ to G₀; F₁ to G₁)

  field
    F⇒G : NaturalTransformation F G
    F⇐G : NaturalTransformation G F

  module ⇒ = NaturalTransformation F⇒G
  module ⇐ = NaturalTransformation F⇐G

  open Morphism D

  field
    iso : ∀ X → Iso (⇒.η X) (⇐.η X)

refl : Reflexive (NaturalIsomorphism {C = C} {D = D})
refl {C = C} {D = D} {x = F} = record
  { F⇒G = α.id
  ; F⇐G = α.id
  ; iso = λ A → record
    { isoˡ = Category.identityˡ D
    ; isoʳ = Category.identityʳ D
    }
  }

sym : Symmetric (NaturalIsomorphism {C = C} {D = D})
sym {C = C} {D = D} F≃G = record
  { F⇒G = F⇐G
  ; F⇐G = F⇒G
  ; iso = λ X →
    let open Iso (iso X) in record
    { isoˡ = isoʳ
    ; isoʳ = isoˡ
    }
  }
  where open NaturalIsomorphism F≃G
        open Morphism D

trans : Transitive (NaturalIsomorphism {C = C} {D = D})
trans {C = C} {D = D} F≃G G≃H = record
  { F⇒G = F⇒G G≃H ∘ᵥ F⇒G F≃G
  ; F⇐G = F⇐G F≃G ∘ᵥ F⇐G G≃H
  ; iso = λ X → record
    { isoˡ = begin
      D [ η (F⇐G F≃G ∘ᵥ F⇐G G≃H) X ∘ η (F⇒G G≃H ∘ᵥ F⇒G F≃G) X ] ≈⟨ cancelInner (isoˡ (iso G≃H X)) ⟩
      η (F⇐G F≃G ∘ᵥ F⇒G F≃G) X                                  ≈⟨ isoˡ (iso F≃G X) ⟩
      D.id                                                      ∎
    ; isoʳ = begin
      D [ η (F⇒G G≃H ∘ᵥ F⇒G F≃G) X ∘ η (F⇐G F≃G ∘ᵥ F⇐G G≃H) X ] ≈⟨ cancelInner (isoʳ (iso F≃G X)) ⟩
      η (F⇒G G≃H ∘ᵥ F⇐G G≃H) X                                  ≈⟨ isoʳ (iso G≃H X) ⟩
      D.id                                                      ∎
    }
  }
  where module D = Category D
        open NaturalIsomorphism
        open NaturalTransformation
        open Morphism D
        open Iso
        open Category.HomReasoning D
        open Square D

isEquivalence : (C : Category o ℓ e) (D : Category o′ ℓ′ e′) → IsEquivalence (NaturalIsomorphism {C = C} {D = D})
isEquivalence C D = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }

setoid : (C : Category o ℓ e) (D : Category o′ ℓ′ e′) → Setoid _ _
setoid C D = record
  { Carrier       = Functor C D
  ; _≈_           = NaturalIsomorphism
  ; isEquivalence = isEquivalence C D
  }

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
  { F⇒G = H ∘ˡ F⇒G
  ; F⇐G = H ∘ˡ F⇐G
  ; iso = λ X → [ H ]-resp-Iso (iso X)
  }
  where open NaturalIsomorphism η
        open Functor H

_ⓘʳ_ : ∀ {F G : Functor C D} →
         (η : NaturalIsomorphism F G) → (K : Functor E C) → NaturalIsomorphism (F ∘F K) (G ∘F K)
_ⓘʳ_ η K = record
  { F⇒G = F⇒G ∘ʳ K
  ; F⇐G = F⇐G ∘ʳ K
  ; iso = λ X → iso (F₀ X)
  }
  where open NaturalIsomorphism η
        open Functor K

infix 4 _≅_
_≅_ : ∀ {F G : Functor C D} →
         (α β : NaturalIsomorphism F G) → Set _
α ≅ β = F⇒G ≃ β.F⇒G × F⇐G ≃ β.F⇐G
  where open NaturalIsomorphism α
        module β = NaturalIsomorphism β

≅-isEquivalence : ∀ {F G : Functor C D} → IsEquivalence (_≅_ {F = F} {G = G})
≅-isEquivalence {D = D} {F = F} {G = G} = record
  { refl  = H.refl , H.refl
  ; sym   = λ where
    (eq₁ , eq₂) → (H.sym eq₁) , (H.sym eq₂)
  ; trans = λ where
    (eq⇒₁ , eq⇐₁) (eq⇒₂ , eq⇐₂) →
      (H.trans eq⇒₁ eq⇒₂) , (H.trans eq⇐₁ eq⇐₂)
  }
  where module H = Category.HomReasoning D

module LeftRightId (F : Functor C D) where
  open Category D
  open HomReasoning
  open Functor F

  -- the component proofs are all the same, factor out
  comm : {X Y : Category.Obj C} (f : C [ X , Y ]) → id ∘ F₁ f ≈ F₁ f ∘ id
  comm _ = Equiv.sym id-comm
  iso-id-id : (X : Category.Obj C) → Morphism.Iso D {A = F₀ X} id id
  iso-id-id X = record { isoˡ = identityˡ {f = id} ; isoʳ = identityʳ {f = id} }

-- Left and Right Unitors, Natural Isomorphisms.
module _ {F : Functor C D} where
  open Category.HomReasoning D
  open Functor F
  open LeftRightId F
  open Category D

  private
    F⇒F∘id : NaturalTransformation F (F ∘F idF)
    F⇒F∘id = record { η = λ _ → id ; commute = comm }

    F⇒id∘F : NaturalTransformation F (idF ∘F F)
    F⇒id∘F = record { η = λ _ → id ; commute = comm }

    F∘id⇒F : NaturalTransformation (F ∘F idF) F
    F∘id⇒F = record { η = λ _ → id ; commute = comm }

    id∘F⇒F : NaturalTransformation (idF ∘F F) F
    id∘F⇒F = record { η = λ _ → id ; commute = comm }

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

infixr 9 _∘ₕᵢ_

-- "Horizontal composition" of Natural Isomorphisms
_∘ₕᵢ_ : ∀ {F G : Functor C D} {H I : Functor D E} →
         NaturalIsomorphism H I → NaturalIsomorphism F G → NaturalIsomorphism (H ∘F F) (I ∘F G)
_∘ₕᵢ_ {C = C} {D = D} {E = E} {F} {G} {H} {I} Y X = record
  { F⇒G = F⇒G Y ∘ₕ F⇒G X
  ; F⇐G = F⇐G Y ∘ₕ F⇐G X
  ; iso = λ Z → record { isoˡ = isol Z ; isoʳ = isor Z }
  }
  where
    module D = Category D
    open NaturalIsomorphism
    open Category E
    open Morphism.Iso
    open NaturalTransformation
    open Functor
    open HomReasoning
    isol : (Z : Category.Obj C) → η (F⇐G Y ∘ₕ F⇐G X) Z ∘ η (F⇒G Y ∘ₕ F⇒G X) Z ≈ id
    isol Z = begin
       (F₁ H (η (F⇐G X) Z) ∘ η (F⇐G Y) (F₀ G Z)) ∘ (F₁ I (η (F⇒G X) Z) ∘ η (F⇒G Y) (F₀ F Z))
           ≈˘⟨ commute (F⇐G Y) (η (F⇐G X) Z) ⟩∘⟨refl ⟩
       (η (F⇐G Y) (F₀ F Z) ∘ F₁ I (η (F⇐G X) Z)) ∘ (F₁ I (η (F⇒G X) Z) ∘ η (F⇒G Y) (F₀ F Z))
           ≈˘⟨ assoc ⟩
       ((η (F⇐G Y) (F₀ F Z) ∘ F₁ I (η (F⇐G X) Z)) ∘ F₁ I (η (F⇒G X) Z)) ∘ η (F⇒G Y) (F₀ F Z)
           ≈⟨ assoc ⟩∘⟨refl ⟩
       (η (F⇐G Y) (F₀ F Z) ∘ (F₁ I (η (F⇐G X) Z) ∘ F₁ I (η (F⇒G X) Z))) ∘ η (F⇒G Y) (F₀ F Z)
           ≈˘⟨  ( refl⟩∘⟨ homomorphism I {f = η (F⇒G X) Z} {g = η (F⇐G X) Z} ) ⟩∘⟨refl  ⟩
       (η (F⇐G Y) (F₀ F Z) ∘ (F₁ I (η (F⇐G X) Z D.∘ η (F⇒G X) Z))) ∘ η (F⇒G Y) (F₀ F Z)
           ≈⟨  ( refl⟩∘⟨ F-resp-≈ I (isoˡ (iso X Z)) ) ⟩∘⟨refl ⟩
       (η (F⇐G Y) (F₀ F Z) ∘ (F₁ I D.id)) ∘ η (F⇒G Y) (F₀ F Z)
           ≈⟨ ( refl⟩∘⟨ identity I ) ⟩∘⟨refl ⟩
       (η (F⇐G Y) (F₀ F Z) ∘ id) ∘ η (F⇒G Y) (F₀ F Z)
           ≈⟨ identityʳ ⟩∘⟨refl ⟩
       η (F⇐G Y) (F₀ F Z) ∘ η (F⇒G Y) (F₀ F Z)
           ≈⟨ isoˡ (iso Y (F₀ F Z)) ⟩
       id ∎
    isor : (Z : Category.Obj C) →  η (F⇒G Y ∘ₕ F⇒G X) Z ∘ η (F⇐G Y ∘ₕ F⇐G X) Z ≈ id
    isor Z = begin
       (F₁ I (η (F⇒G X) Z) ∘ η (F⇒G Y) (F₀ F Z)) ∘ (F₁ H (η (F⇐G X) Z) ∘ η (F⇐G Y) (F₀ G Z))
           ≈˘⟨ commute (F⇒G Y) (η (F⇒G X) Z) ⟩∘⟨refl ⟩
       (η (F⇒G Y) (F₀ G Z) ∘ F₁ H (η (F⇒G X) Z)) ∘ (F₁ H (η (F⇐G X) Z) ∘ η (F⇐G Y) (F₀ G Z))
           ≈˘⟨ assoc ⟩
       ((η (F⇒G Y) (F₀ G Z) ∘ F₁ H (η (F⇒G X) Z)) ∘ F₁ H (η (F⇐G X) Z)) ∘ η (F⇐G Y) (F₀ G Z)
           ≈⟨ assoc ⟩∘⟨refl ⟩
       (η (F⇒G Y) (F₀ G Z) ∘ (F₁ H (η (F⇒G X) Z) ∘ F₁ H (η (F⇐G X) Z))) ∘ η (F⇐G Y) (F₀ G Z)
           ≈˘⟨ ( refl⟩∘⟨ homomorphism H ) ⟩∘⟨refl ⟩
       (η (F⇒G Y) (F₀ G Z) ∘ (F₁ H (η (F⇒G X) Z D.∘ η (F⇐G X) Z))) ∘ η (F⇐G Y) (F₀ G Z)
           ≈⟨  ( refl⟩∘⟨ F-resp-≈ H (isoʳ (iso X Z)) ) ⟩∘⟨refl ⟩
       (η (F⇒G Y) (F₀ G Z) ∘ (F₁ H D.id)) ∘ η (F⇐G Y) (F₀ G Z)
           ≈⟨ ( refl⟩∘⟨ identity H ) ⟩∘⟨refl ⟩
       (η (F⇒G Y) (F₀ G Z) ∘ id) ∘ η (F⇐G Y) (F₀ G Z)
           ≈⟨ identityʳ ⟩∘⟨refl ⟩
       η (F⇒G Y) (F₀ G Z) ∘ η (F⇐G Y) (F₀ G Z)
           ≈⟨ isoʳ (iso Y (F₀ G Z)) ⟩
       id ∎
