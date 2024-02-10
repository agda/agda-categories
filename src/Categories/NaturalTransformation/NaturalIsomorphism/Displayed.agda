{-# OPTIONS --safe --without-K #-}

module Categories.NaturalTransformation.NaturalIsomorphism.Displayed where

open import Level
open import Relation.Binary.Displayed

open import Categories.Category
open import Categories.Category.Displayed
open import Categories.Functor
open import Categories.Functor.Displayed renaming (id′ to idF′)
open import Categories.Functor.Displayed.Properties
import Categories.Morphism.Displayed as DMorphism
import Categories.Morphism.Displayed.Properties as DMorphismₚ
import Categories.Morphism.Displayed.Reasoning as DMR
open import Categories.NaturalTransformation.Displayed as DNT hiding (id′)
open import Categories.NaturalTransformation.NaturalIsomorphism

private
  variable
    bo bℓ be bo′ bℓ′ be′ bo″ bℓ″ be″ o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ o‴ ℓ‴ e‴ : Level
    B C D E : Category o ℓ e
    F G H I : Functor C D
    C′ : Displayed C o ℓ e
    D′ : Displayed D o ℓ e
    E′ : Displayed E o ℓ e

record DisplayedNaturalIsomorphism
  {C′ : Displayed C o ℓ e} {D′ : Displayed D o′ ℓ′ e′}
  (F′ : DisplayedFunctor C′ D′ F) (G′ : DisplayedFunctor C′ D′ G)
  (F≃G : NaturalIsomorphism F G)
  : Set (Category.o-level C ⊔ Category.ℓ-level C ⊔ o ⊔ ℓ ⊔ ℓ′ ⊔ e′) where
  open Displayed C′
  open NaturalIsomorphism F≃G
  field
    F′⇒G′ : DisplayedNaturalTransformation F′ G′ F⇒G
    F′⇐G′ : DisplayedNaturalTransformation G′ F′ F⇐G

  module ⇒′ = DisplayedNaturalTransformation F′⇒G′
  module ⇐′ = DisplayedNaturalTransformation F′⇐G′

  field
    iso′ : ∀ {X} (X′ : Obj[ X ])  → DMorphism.DisplayedIso D′ (⇒′.η′ X′) (⇐′.η′ X′) (iso X)

  module iso′ {X} (X′ : Obj[ X ]) = DMorphism.DisplayedIso (iso′ X′)

open DisplayedNaturalIsomorphism

infix 4 _≃[_]_

_≃[_]_ : ∀ (F′ : DisplayedFunctor C′ D′ F) (F≃G : NaturalIsomorphism F G) (G′ : DisplayedFunctor C′ D′ G) → Set _
F′ ≃[ F≃G ] G′ = DisplayedNaturalIsomorphism F′ G′ F≃G

_ⓘᵥ′_ : ∀ {F′ : DisplayedFunctor C′ D′ F} {G′ : DisplayedFunctor C′ D′ G} {H′ : DisplayedFunctor C′ D′ H} {G≃H} {F≃G}
        → G′ ≃[ G≃H ] H′ → F′ ≃[ F≃G ] G′ → F′ ≃[ G≃H ⓘᵥ F≃G ] H′
_ⓘᵥ′_ {D′ = D′} G′≃H′ F′≃G′ = record
  { F′⇒G′ = F′⇒G′ G′≃H′ ∘′ᵥ F′⇒G′ F′≃G′
  ; F′⇐G′ = F′⇐G′ F′≃G′ ∘′ᵥ F′⇐G′ G′≃H′
  ; iso′ = λ X → DisplayedIso-∘′ (iso′ F′≃G′ X) (iso′ G′≃H′ X)
  }
  where
    open DMorphismₚ D′

_ⓘₕ′_ : ∀ {C : Category bo bℓ be} {D : Category bo′ bℓ′ be′} {E : Category bo″ bℓ″ be″}
          {H I : Functor D E} {F G : Functor C D}
          {C′ : Displayed C o ℓ e} {D′ : Displayed D o′ ℓ′ e′} {E′ : Displayed E o″ ℓ″ e″}
          {H′ : DisplayedFunctor D′ E′ H} {I′ : DisplayedFunctor D′ E′ I}
          {F′ : DisplayedFunctor C′ D′ F} {G′ : DisplayedFunctor C′ D′ G}
          {H≃I} {F≃G}
      → H′ ≃[ H≃I ] I′ → F′ ≃[ F≃G ] G′ → (H′ ∘F′ F′) ≃[ H≃I ⓘₕ F≃G ] (I′ ∘F′ G′)
_ⓘₕ′_ {E′ = E′} {I′ = I′} H′≃I′ F′≃G′ = record
  { F′⇒G′ = F′⇒G′ H′≃I′ ∘′ₕ F′⇒G′ F′≃G′
  ; F′⇐G′ = F′⇐G′ H′≃I′ ∘′ₕ F′⇐G′ F′≃G′
  ; iso′ = λ X′ → DisplayedIso-resp-≈[] (DisplayedIso-∘′ (iso′ H′≃I′ _) ([ I′ ]-resp-DisplayedIso (iso′ F′≃G′ X′))) Equiv′.refl′ (⇐′.commute′ H′≃I′ (⇐′.η′ F′≃G′ X′))
  }
  where
    open Displayed E′
    open DMorphismₚ E′

refl′ : ∀ {F′ : DisplayedFunctor C′ D′ F} → F′ ≃[ refl ] F′
refl′ {D′ = D′} = record
  { F′⇒G′ = DNT.id′
  ; F′⇐G′ = DNT.id′
  ; iso′ = λ X′ → record
    { isoˡ′ = Displayed.identityˡ′ D′
    ; isoʳ′ = Displayed.identityʳ′ D′
    }
  }

sym′ : ∀ {F′ : DisplayedFunctor C′ D′ F} {G′ : DisplayedFunctor C′ D′ G} {F≃G}
       → F′ ≃[ F≃G ] G′ → G′ ≃[ sym F≃G ] F′
sym′ F′≃G′ = record
  { F′⇒G′ = F′⇐G′ F′≃G′
  ; F′⇐G′ = F′⇒G′ F′≃G′
  ; iso′ = λ X′ →
    let open DMorphism.DisplayedIso (iso′ F′≃G′ X′) in record
    { isoˡ′ = isoʳ′
    ; isoʳ′ = isoˡ′
    }
  }

trans′ : ∀ {F′ : DisplayedFunctor C′ D′ F} {G′ : DisplayedFunctor C′ D′ G} {H′ : DisplayedFunctor C′ D′ H} {F≃G} {G≃H}
         → F′ ≃[ F≃G ] G′ → G′ ≃[ G≃H ] H′ → F′ ≃[ trans F≃G G≃H ] H′
trans′ F′≃G′ G′≃H′ = G′≃H′ ⓘᵥ′ F′≃G′

isDisplayedEquivalence : {C′ : Displayed C o ℓ e} {D′ : Displayed D o′ ℓ′ e′}
                       → IsDisplayedEquivalence isEquivalence (_≃[_]_ {C′ = C′} {D′ = D′})
isDisplayedEquivalence = record { refl′ = refl′ ; sym′ = sym′ ; trans′ = trans′ }

module LeftRightId′ (F′ : DisplayedFunctor C′ D′ F) where
  open LeftRightId F
  module D′ = Displayed D′

  iso-id′-id′ : ∀ {X} (X′ : Displayed.Obj[_] C′ X) → DMorphism.DisplayedIso D′ {X′ = DisplayedFunctor.F₀′ F′ X′} D′.id′ D′.id′ (iso-id-id X)
  iso-id′-id′ X′ = record { isoˡ′ = D′.identityˡ′ ; isoʳ′ = D′.identityʳ′ }

-- unitors
module _ {F : Functor C D} {F′ : DisplayedFunctor C′ D′ F} where
  open LeftRightId′ F′
  
  unitorˡ′ : idF′ ∘F′ F′ ≃[ unitorˡ ] F′
  unitorˡ′ = record { F′⇒G′ = id′∘F′⇒F′ ; F′⇐G′ = F′⇒id′∘F′ ; iso′ = iso-id′-id′ }

  unitorʳ′ : F′ ∘F′ idF′ ≃[ unitorʳ ] F′
  unitorʳ′ = record { F′⇒G′ = F′∘id′⇒F′ ; F′⇐G′ = F′⇒F′∘id′ ; iso′ = iso-id′-id′ }

unitor²′ : ∀ {C′ : Displayed C o ℓ e} → idF′ ∘F′ idF′ ≃[ unitor² ] idF′ {C = C′}
unitor²′ = record { F′⇒G′ = id′∘id′⇒id′ ; F′⇐G′ = id′⇒id′∘id′ ; iso′ = LeftRightId′.iso-id′-id′ idF′ }

-- associator
module _
  {F : Functor B C} {G : Functor C D} {H : Functor D E}
  {B′ : Displayed B o ℓ e} {C′ : Displayed C o′ ℓ′ e′} {D′ : Displayed D o″ ℓ″ e″} {E′ : Displayed E o‴ ℓ‴ e‴}
  (F′ : DisplayedFunctor B′ C′ F) (G′ : DisplayedFunctor C′ D′ G) (H′ : DisplayedFunctor D′ E′ H)
  where

  open Displayed E′
  open LeftRightId′ (H′ ∘F′ (G′ ∘F′ F′))

  private
    assocʳ′ : DisplayedNaturalTransformation ((H′ ∘F′ G′) ∘F′ F′) (H′ ∘F′ (G′ ∘F′ F′)) _
    assocʳ′ = record
      { η′ = λ _ → id′
      ; commute′ = λ _ → DMR.id′-comm-sym E′
      ; sym-commute′ = λ _ → DMR.id′-comm E′
      }

    assocˡ′ : DisplayedNaturalTransformation (H′ ∘F′ (G′ ∘F′ F′)) ((H′ ∘F′ G′) ∘F′ F′) _
    assocˡ′ = record
      { η′ = λ _ → id′
      ; commute′ = λ _ → DMR.id′-comm-sym E′
      ; sym-commute′ = λ _ → DMR.id′-comm E′
      }

  associator′ : (H′ ∘F′ G′) ∘F′ F′ ≃[ associator F G H ] H′ ∘F′ (G′ ∘F′ F′)
  associator′ = record { F′⇒G′ = assocʳ′ ; F′⇐G′ = assocˡ′ ; iso′ = iso-id′-id′ }

  sym-associator′ : H′ ∘F′ (G′ ∘F′ F′) ≃[ sym-associator F G H ] (H′ ∘F′ G′) ∘F′ F′
  sym-associator′ = record { F′⇒G′ = assocˡ′ ; F′⇐G′ = assocʳ′ ; iso′ = iso-id′-id′ }
