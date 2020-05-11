{-# OPTIONS --without-K --safe #-}
module Categories.Adjoint.Equivalents where

-- Theorems about equivalent formulations to Adjoint
-- (though some have caveats)

open import Level

open import Data.Product using (_,_; _×_)
open import Function using (_$_) renaming (_∘_ to _∙_)
open import Function.Equality using (Π; _⟶_)
import Function.Inverse as FI
open import Relation.Binary using (Rel; IsEquivalence; Setoid)

-- be explicit in imports to 'see' where the information comes from
open import Categories.Adjoint using (Adjoint; _⊣_)
open import Categories.Category.Core using (Category)
open import Categories.Category.Product using (Product; _⁂_)
open import Categories.Category.Instance.Setoids
open import Categories.Morphism
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Functor.Hom using (Hom[_][-,-])
open import Categories.Functor.Construction.LiftSetoids
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper; _∘ₕ_; _∘ᵥ_; _∘ˡ_; _∘ʳ_)
  renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (NaturalIsomorphism; unitorˡ; unitorʳ; associator; _≃_)
import Categories.Morphism.Reasoning as MR

private
  variable
    o o′ o″ ℓ ℓ′ ℓ″ e e′ e″ : Level
    C D E : Category o ℓ e

-- a special case of the natural isomorphism in which homsets in C and D have the same
-- universe level. therefore there is no need to lift Setoids to the same level.
-- this is helpful when combining with Yoneda lemma.
module _ {C : Category o ℓ e} {D : Category o′ ℓ e} {L : Functor C D} {R : Functor D C} where
  private
    module C = Category C
    module D = Category D
    module L = Functor L
    module R = Functor R

  module _ (adjoint : L ⊣ R) where
    open Adjoint adjoint

    -- in this case, the hom functors are naturally isomorphism directly
    Hom-NI′ : NaturalIsomorphism Hom[L-,-] Hom[-,R-]
    Hom-NI′ = record
      { F⇒G = ntHelper record
        { η       = λ _ → Hom-inverse.to
        ; commute = λ _ eq → Ladjunct-comm eq
        }
      ; F⇐G = ntHelper record
        { η       = λ _ → Hom-inverse.from
        ; commute = λ _ eq → Radjunct-comm eq
        }
      ; iso = λ _ → record
        { isoˡ = λ eq → let open D.HomReasoning in RLadjunct≈id ○ eq
        ; isoʳ = λ eq → let open C.HomReasoning in LRadjunct≈id ○ eq
        }
      }

  -- now goes from natural isomorphism back to adjoint.
  -- for simplicity, just construct the case in which homsetoids of C and D
  -- are compatible.

  private
    Hom[L-,-] : Bifunctor C.op D (Setoids _ _)
    Hom[L-,-] = Hom[ D ][-,-] ∘F (L.op ⁂ idF)

    Hom[-,R-] : Bifunctor C.op D (Setoids _ _)
    Hom[-,R-] = Hom[ C ][-,-] ∘F (idF ⁂ R)

  module _ (Hni : NaturalIsomorphism Hom[L-,-] Hom[-,R-]) where
    open NaturalIsomorphism Hni
    open NaturalTransformation
    open Functor
    open Π

    private
      unitη : ∀ X → F₀ Hom[L-,-] (X , L.F₀ X) ⟶ F₀ Hom[-,R-] (X , L.F₀ X)
      unitη X = ⇒.η (X , L.F₀ X)

      unit : NaturalTransformation idF (R ∘F L)
      unit = ntHelper record
        { η       = λ X → unitη X ⟨$⟩ D.id
        ; commute = λ {X} {Y} f → begin
          (unitη Y ⟨$⟩ D.id) ∘ f                             ≈⟨ introˡ R.identity ⟩
          R.F₁ D.id ∘ (unitη Y  ⟨$⟩ D.id) ∘ f                ≈˘⟨ ⇒.commute (f , D.id) D.Equiv.refl ⟩
          ⇒.η (X , L.F₀ Y) ⟨$⟩ (D.id D.∘ D.id D.∘ L.F₁ f)    ≈⟨ cong (⇒.η (X , L.F₀ Y)) (D.Equiv.trans D.identityˡ D.identityˡ) ⟩
          ⇒.η (X , L.F₀ Y) ⟨$⟩ L.F₁ f                        ≈⟨ cong (⇒.η (X , L.F₀ Y)) (MR.introʳ D (MR.elimʳ D L.identity)) ⟩
          ⇒.η (X , L.F₀ Y) ⟨$⟩ (L.F₁ f D.∘ D.id D.∘ L.F₁ id) ≈⟨ ⇒.commute (C.id , L.F₁ f) D.Equiv.refl ⟩
          R.F₁ (L.F₁ f) ∘ (unitη X ⟨$⟩ D.id) ∘ id            ≈⟨ refl⟩∘⟨ identityʳ ⟩
          R.F₁ (L.F₁ f) ∘ (unitη X ⟨$⟩ D.id)                 ∎
        }
        where open C
              open HomReasoning
              open MR C

      counitη : ∀ X → F₀ Hom[-,R-] (R.F₀ X , X) ⟶ F₀ Hom[L-,-] (R.F₀ X , X)
      counitη X = ⇐.η (R.F₀ X , X)

      counit : NaturalTransformation (L ∘F R) idF
      counit = ntHelper record
        { η       = λ X → counitη X ⟨$⟩ C.id
        ; commute = λ {X} {Y} f → begin
          (counitη Y ⟨$⟩ C.id) ∘ L.F₁ (R.F₁ f)               ≈˘⟨ identityˡ ⟩
          id ∘ (counitη Y ⟨$⟩ C.id) ∘ L.F₁ (R.F₁ f)          ≈˘⟨ ⇐.commute (R.F₁ f , D.id) C.Equiv.refl ⟩
          ⇐.η (R.F₀ X , Y) ⟨$⟩ (R.F₁ id C.∘ C.id C.∘ R.F₁ f) ≈⟨ cong (⇐.η (R.F₀ X , Y)) (C.Equiv.trans (MR.elimˡ C R.identity) C.identityˡ) ⟩
          ⇐.η (R.F₀ X , Y) ⟨$⟩ R.F₁ f                        ≈⟨ cong (⇐.η (R.F₀ X , Y)) (MR.introʳ C C.identityˡ) ⟩
          ⇐.η (R.F₀ X , Y) ⟨$⟩ (R.F₁ f C.∘ C.id C.∘ C.id)    ≈⟨ ⇐.commute (C.id , f) C.Equiv.refl ⟩
          f ∘ (counitη X ⟨$⟩ C.id) ∘ L.F₁ C.id               ≈⟨ refl⟩∘⟨ elimʳ L.identity ⟩
          f ∘ (counitη X ⟨$⟩ C.id)                           ∎
        }
        where open D
              open HomReasoning
              open MR D

    Hom-NI⇒Adjoint : L ⊣ R
    Hom-NI⇒Adjoint = record
      { unit   = unit
      ; counit = counit
      ; zig    = λ {A} →
        let open D
            open HomReasoning
            open Equiv
            open MR D
        in begin
          η counit (L.F₀ A) ∘ L.F₁ (η unit A)      ≈˘⟨ identityˡ ⟩
          id ∘ η counit (L.F₀ A) ∘ L.F₁ (η unit A) ≈˘⟨ ⇐.commute (η unit A , id) C.Equiv.refl ⟩
          ⇐.η (A , L.F₀ A) ⟨$⟩ (R.F₁ id C.∘ C.id C.∘ η unit A)
                                                   ≈⟨ cong (⇐.η (A , L.F₀ A)) (C.Equiv.trans (MR.elimˡ C R.identity) C.identityˡ) ⟩
          ⇐.η (A , L.F₀ A) ⟨$⟩ η unit A            ≈⟨ isoˡ refl ⟩
          id
                                                   ∎
      ; zag    = λ {B} →
        let open C
            open HomReasoning
            open Equiv
            open MR C
        in begin
          R.F₁ (η counit B) ∘ η unit (R.F₀ B)      ≈˘⟨ refl⟩∘⟨ identityʳ ⟩
          R.F₁ (η counit B) ∘ η unit (R.F₀ B) ∘ id ≈˘⟨ ⇒.commute (id , η counit B) D.Equiv.refl ⟩
          ⇒.η (R.F₀ B , B) ⟨$⟩ (η counit B D.∘ D.id D.∘ L.F₁ id)
                                                   ≈⟨ cong (⇒.η (R.F₀ B , B)) (MR.elimʳ D (MR.elimʳ D L.identity)) ⟩
          ⇒.η (R.F₀ B , B) ⟨$⟩ η counit B          ≈⟨ isoʳ refl ⟩
          id                                       ∎
      }
      where module i {X} = Iso (iso X)
            open i

-- the general case from isomorphic Hom setoids to adjoint functors
module _ {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {L : Functor C D} {R : Functor D C} where
  private
    module C = Category C
    module D = Category D
    module L = Functor L
    module R = Functor R
    open Functor
    open Π

    Hom[L-,-] : Bifunctor C.op D (Setoids _ _)
    Hom[L-,-] = LiftSetoids ℓ e ∘F Hom[ D ][-,-] ∘F (L.op ⁂ idF)

    Hom[-,R-] : Bifunctor C.op D (Setoids _ _)
    Hom[-,R-] = LiftSetoids ℓ′ e′ ∘F Hom[ C ][-,-] ∘F (idF ⁂ R)

  module _ (Hni : Hom[L-,-] ≃ Hom[-,R-]) where
    open NaturalIsomorphism Hni using (module ⇒; module ⇐; iso)
    private
      unitη : ∀ X → F₀ Hom[L-,-] (X , L.F₀ X) ⟶ F₀ Hom[-,R-] (X , L.F₀ X)
      unitη X = ⇒.η (X , L.F₀ X)

      unit : NaturalTransformation idF (R ∘F L)
      unit = ntHelper record
        { η       = λ X → lower (unitη X ⟨$⟩ lift D.id)
        ; commute = λ {X Y} f → begin
          lower (unitη Y ⟨$⟩ lift D.id) ∘ f
            ≈⟨ introˡ R.identity ⟩
          R.F₁ D.id ∘ lower (unitη Y ⟨$⟩ lift D.id) ∘ f
            ≈˘⟨ lower (⇒.commute (f , D.id) (lift D.Equiv.refl)) ⟩
          lower (⇒.η (X , L.F₀ Y) ⟨$⟩ lift (D.id D.∘ D.id D.∘ L.F₁ f))
            ≈⟨ lower (cong (⇒.η (X , L.F₀ Y)) (lift (D.Equiv.trans D.identityˡ D.identityˡ))) ⟩
          lower (⇒.η (X , L.F₀ Y) ⟨$⟩ lift (L.F₁ f))
            ≈⟨ lower (cong (⇒.η (X , L.F₀ Y)) (lift (MR.introʳ D (MR.elimʳ D L.identity)))) ⟩
          lower (⇒.η (X , L.F₀ Y) ⟨$⟩ lift (L.F₁ f D.∘ D.id D.∘ L.F₁ id))
            ≈⟨ lower (⇒.commute (C.id , L.F₁ f) (lift D.Equiv.refl)) ⟩
          R.F₁ (L.F₁ f) ∘ lower (⇒.η (X , L.F₀ X) ⟨$⟩ lift D.id) ∘ id
            ≈⟨ refl⟩∘⟨ identityʳ ⟩
          F₁ (R ∘F L) f ∘ lower (unitη X ⟨$⟩ lift D.id)                ∎
        }
        where open C
              open HomReasoning
              open MR C

      counitη : ∀ X → F₀ Hom[-,R-] (R.F₀ X , X) ⟶ F₀ Hom[L-,-] (R.F₀ X , X)
      counitη X = ⇐.η (R.F₀ X , X)

      counit : NaturalTransformation (L ∘F R) idF
      counit = ntHelper record
        { η       = λ X → lower (counitη X ⟨$⟩ lift C.id)
        ; commute = λ {X} {Y} f → begin
          lower (⇐.η (R.F₀ Y , Y) ⟨$⟩ lift C.id) ∘ L.F₁ (R.F₁ f)
            ≈˘⟨ identityˡ ⟩
          id ∘ lower (⇐.η (R.F₀ Y , Y) ⟨$⟩ lift C.id) ∘ L.F₁ (R.F₁ f)
            ≈˘⟨ lower (⇐.commute (R.F₁ f , D.id) (lift C.Equiv.refl)) ⟩
          lower (⇐.η (R.F₀ X , Y) ⟨$⟩ lift (R.F₁ id C.∘ C.id C.∘ R.F₁ f))
            ≈⟨ lower (cong (⇐.η (R.F₀ X , Y)) (lift (C.Equiv.trans (MR.elimˡ C R.identity) C.identityˡ))) ⟩
          lower (⇐.η (R.F₀ X , Y) ⟨$⟩ lift (R.F₁ f))
            ≈⟨ lower (cong (⇐.η (R.F₀ X , Y)) (lift (MR.introʳ C C.identityˡ))) ⟩
          lower (⇐.η (R.F₀ X , Y) ⟨$⟩ lift (R.F₁ f C.∘ C.id C.∘ C.id))
            ≈⟨ lower (⇐.commute (C.id , f) (lift C.Equiv.refl)) ⟩
          f ∘ lower (⇐.η (R.F₀ X , X) ⟨$⟩ lift C.id) ∘ L.F₁ C.id
            ≈⟨ refl⟩∘⟨ elimʳ L.identity ⟩
          f ∘ lower (⇐.η (R.F₀ X , X) ⟨$⟩ lift C.id)
            ∎
        }
        where open D
              open HomReasoning
              open MR D

    Hom-NI′⇒Adjoint : L ⊣ R
    Hom-NI′⇒Adjoint = record
      { unit   = unit
      ; counit = counit
      ; zig    = λ {A} →
        let open D
            open HomReasoning
            open Equiv
            open MR D
        in begin
          lower (counitη (L.F₀ A) ⟨$⟩ lift C.id) ∘ L.F₁ (η unit A)
            ≈˘⟨ identityˡ ⟩
          id ∘ lower (counitη (L.F₀ A) ⟨$⟩ lift C.id) ∘ L.F₁ (η unit A)
            ≈˘⟨ lower (⇐.commute (η unit A , id) (lift C.Equiv.refl)) ⟩
          lower (⇐.η (A , L.F₀ A) ⟨$⟩ lift (R.F₁ id C.∘ C.id C.∘ lower (⇒.η (A , L.F₀ A) ⟨$⟩ lift id)))
            ≈⟨ lower (cong (⇐.η (A , L.F₀ A)) (lift (C.Equiv.trans (MR.elimˡ C R.identity) C.identityˡ))) ⟩
          lower (⇐.η (A , L.F₀ A) ⟨$⟩ (⇒.η (A , L.F₀ A) ⟨$⟩ lift id))
            ≈⟨ lower (isoˡ (lift refl)) ⟩
          id ∎
      ; zag    = λ {B} →
        let open C
            open HomReasoning
            open Equiv
            open MR C
        in begin
          R.F₁ (lower (⇐.η (R.F₀ B , B) ⟨$⟩ lift id)) ∘ lower (⇒.η (R.F₀ B , L.F₀ (R.F₀ B)) ⟨$⟩ lift D.id)
            ≈˘⟨ refl⟩∘⟨ identityʳ ⟩
          R.F₁ (lower (⇐.η (R.F₀ B , B) ⟨$⟩ lift id)) ∘ lower (⇒.η (R.F₀ B , L.F₀ (R.F₀ B)) ⟨$⟩ lift D.id) ∘ id
            ≈˘⟨ lower (⇒.commute (id , η counit B) (lift D.Equiv.refl)) ⟩
          lower (⇒.η (R.F₀ B , B) ⟨$⟩ lift (lower (⇐.η (R.F₀ B , B) ⟨$⟩ lift id) D.∘ D.id D.∘ L.F₁ id))
            ≈⟨ lower (cong (⇒.η (R.F₀ B , B)) (lift (MR.elimʳ D (MR.elimʳ D L.identity)))) ⟩
          lower (⇒.η (R.F₀ B , B) ⟨$⟩ lift (lower (⇐.η (R.F₀ B , B) ⟨$⟩ lift id)))
            ≈⟨ lower (isoʳ (lift refl)) ⟩
          id ∎
      }
      where open NaturalTransformation
            module _ {X} where
              open Iso (iso X) public
