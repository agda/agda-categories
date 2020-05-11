{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category using (Category; _[_,_])

-- Various conclusions that can be drawn from Yoneda
-- over a particular Category C
module Categories.Yoneda.Properties {o ℓ e : Level} (C : Category o ℓ e) where

open import Function.Base using (_$_)
open import Function.Bundles using (Inverse)
open import Function.Equality using (Π; _⟨$⟩_; cong)
open import Relation.Binary.Bundles using (module Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidR
open import Data.Product using (_,_; Σ)

open import Categories.Category.Product
open import Categories.Category.Construction.Presheaves
open import Categories.Category.Construction.Functors
open import Categories.Category.Instance.Setoids
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Properties using (Full; Faithful; FullyFaithful)
open import Categories.Functor.Hom using (module Hom; Hom[_][-,_]; Hom[_][-,-])
open import Categories.Functor.Bifunctor
open import Categories.Functor.Presheaf
open import Categories.Functor.Construction.LiftSetoids
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper) renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)
open import Categories.Yoneda

import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR
import Categories.NaturalTransformation.Hom as NT-Hom

open Category C using (module HomReasoning; id; _∘_; identityˡ; identityʳ; Obj; ∘-resp-≈ˡ; ∘-resp-≈ʳ)
open HomReasoning
open NaturalTransformation using (η; commute)
open Yoneda C using (embed; yoneda-inverse; module yoneda)
private
  module CE = Category.Equiv C using (refl)
  module C = Category C using (op; id)

YoFull : Full embed
YoFull {X} {Y} = record
  { from             = record { _⟨$⟩_ = λ ε → η ε X ⟨$⟩ id ; cong = λ i≈j → i≈j CE.refl }
  ; right-inverse-of = λ ε {x} {z} {y} z≈y →
    begin
      (η ε X ⟨$⟩ id) ∘ z      ≈˘⟨ identityˡ ⟩
      id ∘ (η ε X ⟨$⟩ id) ∘ z ≈˘⟨ commute ε z CE.refl ⟩
      η ε x ⟨$⟩ id ∘ id ∘ z   ≈⟨ cong (η ε x) (identityˡ ○ identityˡ ○ z≈y) ⟩
      η ε x ⟨$⟩ y             ∎
  }

YoFaithful : Faithful embed
YoFaithful f g pres-≈ = begin
  f      ≈˘⟨ identityʳ ⟩
  f ∘ id ≈⟨ pres-≈ CE.refl ⟩
  g ∘ id ≈⟨ identityʳ ⟩
  g      ∎

YoFullyFaithful : FullyFaithful embed
YoFullyFaithful = YoFull , YoFaithful

open Mor C using (_≅_)

yoneda-iso : ∀ {A B : Obj} → NaturalIsomorphism Hom[ C ][-, A ] Hom[ C ][-, B ] → A ≅ B
yoneda-iso {A} {B} niso = record
  { from = ⇒.η A ⟨$⟩ id
  ; to   = ⇐.η B ⟨$⟩ id
  ; iso  = record
    { isoˡ = begin
      (⇐.η B ⟨$⟩ id) ∘ (⇒.η A ⟨$⟩ id)      ≈˘⟨ identityˡ ⟩
      id ∘ (⇐.η B ⟨$⟩ id) ∘ (⇒.η A ⟨$⟩ id) ≈⟨  B⇒A.inverseʳ F⇐G CE.refl  ⟩
      ⇐.η A ⟨$⟩ (⇒.η A ⟨$⟩ id)             ≈⟨ isoX.isoˡ CE.refl ⟩
      id                                   ∎
    ; isoʳ = begin
      (⇒.η A ⟨$⟩ id) ∘ (⇐.η B ⟨$⟩ id)      ≈˘⟨ identityˡ ⟩
      id ∘ (⇒.η A ⟨$⟩ id) ∘ (⇐.η B ⟨$⟩ id) ≈⟨  A⇒B.inverseʳ F⇒G CE.refl ⟩
      ⇒.η B ⟨$⟩ (⇐.η B ⟨$⟩ id)             ≈⟨ isoX.isoʳ CE.refl ⟩
      id                                   ∎
    }
  }
  where
  open NaturalIsomorphism niso
  A⇒B = yoneda-inverse A (Functor.F₀ embed B)
  B⇒A = yoneda-inverse B (Functor.F₀ embed A)
  module A⇒B = Inverse A⇒B using (inverseʳ)
  module B⇒A = Inverse B⇒A using (inverseʳ)
  module isoX {X} = Mor.Iso (iso X) using (isoʳ; isoˡ)

module _ {o′ ℓ′ e′} {D : Category o′ ℓ′ e′} where
  private
    module D = Category D using (id)

    module _ {F G : Functor D C} where
      private
        module F = Functor F using (₀; ₁; identity)
        module G = Functor G using (₀; ₁; identity)
        Hom[-,F-] : Bifunctor C.op D (Setoids ℓ e)
        Hom[-,F-] = Hom[ C ][-,-] ∘F (idF ⁂ F)

        Hom[-,G-] : Bifunctor C.op D (Setoids ℓ e)
        Hom[-,G-] = Hom[ C ][-,-] ∘F (idF ⁂ G)

      nat-appʳ : ∀ X → NaturalTransformation Hom[-,F-] Hom[-,G-] →
                       NaturalTransformation Hom[ C ][-, F.₀ X ] Hom[ C ][-, G.₀ X ]
      nat-appʳ X α = ntHelper record
        { η       = λ Y → η α (Y , X)
        ; commute = λ {_ Y} f eq → cong (η α (Y , X)) (∘-resp-≈ˡ (⟺ F.identity)) ○ commute α (f , D.id) eq ○ ∘-resp-≈ˡ G.identity
        }

      transform : NaturalTransformation Hom[-,F-] Hom[-,G-] → NaturalTransformation F G
      transform α = ntHelper record
        { η       = λ X → η α (F.₀ X , X) ⟨$⟩ id
        ; commute = λ {X Y} f → begin
          (η α (F.₀ Y , Y) ⟨$⟩ id) ∘ F.₁ f       ≈˘⟨ identityˡ ⟩
          id ∘ (η α (F.₀ Y , Y) ⟨$⟩ id) ∘ F.₁ f  ≈˘⟨ lower (yoneda.⇒.commute {Y = Hom[ C ][-, G.₀ Y ] , _} (idN , F.₁ f) {nat-appʳ Y α} {nat-appʳ Y α} (cong (η α _))) ⟩
          η α (F.₀ X , Y) ⟨$⟩ F.₁ f ∘ id         ≈⟨ cong (η α (F.₀ X , Y)) (∘-resp-≈ʳ (⟺ identityˡ)) ⟩
          η α (F.₀ X , Y) ⟨$⟩ F.₁ f ∘ id ∘ id    ≈⟨ commute α (id , f) CE.refl ⟩
          G.₁ f ∘ (η α (F.₀ X , X) ⟨$⟩ id) ∘ id  ≈⟨ refl⟩∘⟨ identityʳ ⟩
          G.₁ f ∘ (η α (F.₀ X , X) ⟨$⟩ id)      ∎
        }

  module _ (F G : Functor D C) where
    private
      module F = Functor F using (₀)
      module G = Functor G using (₀)
      Hom[-,F-] : Bifunctor C.op D (Setoids ℓ e)
      Hom[-,F-] = Hom[ C ][-,-] ∘F (idF ⁂ F)

      Hom[-,G-] : Bifunctor C.op D (Setoids ℓ e)
      Hom[-,G-] = Hom[ C ][-,-] ∘F (idF ⁂ G)

    -- The implicits given below are sometimes needed (yellow), sometimes make an enormous difference in
    -- typechecking time. For example, in yoneda.⇒.commute, "nat-appʳ X F⇐G" is needed, while
    -- nat-appʳ {F = G} {F} X F⇐G makes a huge difference in checking time.
    yoneda-NI : NaturalIsomorphism Hom[-,F-] Hom[-,G-] → NaturalIsomorphism F G
    yoneda-NI ni = record
      { F⇒G = transform F⇒G
      ; F⇐G = transform F⇐G
      ; iso = λ X → record
        { isoˡ = begin
          (⇐.η (G.₀ X , X) ⟨$⟩ id) ∘ (⇒.η (F.₀ X , X) ⟨$⟩ id)      ≈⟨ introˡ CE.refl ⟩
          id ∘ (⇐.η (G.₀ X , X) ⟨$⟩ id) ∘ (⇒.η (F.₀ X , X) ⟨$⟩ id) ≈˘⟨ lower {e} (yoneda.⇒.commute {Y = Hom[ C ][-, F.₀ X ] , _}
                                                                                  (idN , (⇒.η (F.₀ X , X) ⟨$⟩ id))
                                                                                  {nat-appʳ {F = G} {F} X F⇐G}
                                                                                  {nat-appʳ {F = G} {F} X F⇐G}
                                                                                  (cong (⇐.η (_ , X) ))) ⟩
          ⇐.η (F.₀ X , X) ⟨$⟩ (⇒.η (F.₀ X , X) ⟨$⟩ id) ∘ id        ≈⟨ cong (⇐.η _) identityʳ ⟩
          ⇐.η (F.₀ X , X) ⟨$⟩ (⇒.η (F.₀ X , X) ⟨$⟩ id)             ≈⟨ iso.isoˡ _ CE.refl ⟩
          id                                                  ∎
        ; isoʳ = begin
          (⇒.η (F.₀ X , X) ⟨$⟩ id) ∘ (⇐.η (G.₀ X , X) ⟨$⟩ id)      ≈⟨ introˡ CE.refl ⟩
          id ∘ (⇒.η (F.₀ X , X) ⟨$⟩ id) ∘ (⇐.η (G.₀ X , X) ⟨$⟩ id) ≈˘⟨ lower {e} (yoneda.⇒.commute {Y = Hom[ C ][-, G.₀ X ] , _}
                                                                                   (idN , (⇐.η (G.₀ X , X) ⟨$⟩ C.id))
                                                                                   {nat-appʳ {F = F} {G} X F⇒G}
                                                                                   {nat-appʳ {F = F} {G} X F⇒G}
                                                                                   (cong (⇒.η _))) ⟩
          ⇒.η (G.₀ X , X) ⟨$⟩ (⇐.η (G.₀ X , X) ⟨$⟩ id) ∘ id        ≈⟨ cong (⇒.η _) identityʳ ⟩
          ⇒.η (G.₀ X , X) ⟨$⟩ (⇐.η (G.₀ X , X) ⟨$⟩ id)             ≈⟨ iso.isoʳ _ CE.refl ⟩
          id                                                      ∎
        }
      }
      where
      open NaturalIsomorphism ni using (F⇒G; F⇐G; module ⇐; module ⇒; module iso)
      open MR C using (introˡ)
