{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category using (Category; _[_,_])

-- Various conclusions that can be drawn from Yoneda
-- over a particular Category C
module Categories.Yoneda.Properties {o ℓ e : Level} (C : Category o ℓ e) where

open import Function using (_$_; Inverse) -- else there's a conflict with the import below
open import Function.Equality using (Π; _⟨$⟩_; cong)
open import Relation.Binary using (module Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidR
open import Data.Product using (_,_; Σ)

open import Categories.Category.Product
open import Categories.Category.Construction.Presheaves
open import Categories.Category.Construction.Functors
open import Categories.Category.Instance.Setoids
open import Categories.Functor renaming (id to idF)
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

open Category C
open HomReasoning
open NaturalTransformation
open Yoneda C
private
  module CE = Category.Equiv C
  module C = Category C

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
YoFaithful _ _ pres-≈ = ⟺ identityʳ ○ pres-≈ {_} {id} CE.refl ○ identityʳ

YoFullyFaithful : FullyFaithful embed
YoFullyFaithful = YoFull , YoFaithful

open Mor C

yoneda-iso : ∀ {A B : Obj} → NaturalIsomorphism Hom[ C ][-, A ] Hom[ C ][-, B ] → A ≅ B
yoneda-iso {A} {B} niso = record
  { from = ⇒.η A ⟨$⟩ id
  ; to   = ⇐.η B ⟨$⟩ id
  ; iso  = record
    { isoˡ = begin
      (⇐.η B ⟨$⟩ id) ∘ (⇒.η A ⟨$⟩ id)      ≈˘⟨ identityˡ ⟩
      id ∘ (⇐.η B ⟨$⟩ id) ∘ (⇒.η A ⟨$⟩ id) ≈⟨  B⇒A.inverseʳ F⇐G refl  ⟩
      ⇐.η A ⟨$⟩ (⇒.η A ⟨$⟩ id)             ≈⟨ isoX.isoˡ refl ⟩
      id                                   ∎
    ; isoʳ = begin
      (⇒.η A ⟨$⟩ id) ∘ (⇐.η B ⟨$⟩ id)      ≈˘⟨ identityˡ ⟩
      id ∘ (⇒.η A ⟨$⟩ id) ∘ (⇐.η B ⟨$⟩ id) ≈⟨  A⇒B.inverseʳ F⇒G refl  ⟩
      ⇒.η B ⟨$⟩ (⇐.η B ⟨$⟩ id)             ≈⟨ isoX.isoʳ refl ⟩
      id                                   ∎
    }
  }
  where open NaturalIsomorphism niso
        A⇒B = yoneda-inverse A (Functor.F₀ embed B)
        B⇒A = yoneda-inverse B (Functor.F₀ embed A)
        module A⇒B = Inverse A⇒B
        module B⇒A = Inverse B⇒A
        module isoX {X} = Mor.Iso (iso X)

module _ {o′ ℓ′ e′} {D : Category o′ ℓ′ e′} where
  private
    module D = Category D

    module _ {F G : Functor D C} where
      private
        module F = Functor F
        module G = Functor G
        Hom[-,F-] : Bifunctor C.op D (Setoids ℓ e)
        Hom[-,F-] = Hom[ C ][-,-] ∘F (idF ⁂ F)

        Hom[-,G-] : Bifunctor C.op D (Setoids ℓ e)
        Hom[-,G-] = Hom[ C ][-,-] ∘F (idF ⁂ G)

      nat-appʳ : ∀ X → NaturalTransformation Hom[-,F-] Hom[-,G-] →
                       NaturalTransformation Hom[ C ][-, F.F₀ X ] Hom[ C ][-, G.F₀ X ]
      nat-appʳ X α = ntHelper record
        { η       = λ Y → η α (Y , X)
        ; commute = λ {_ Y} f eq → cong (η α (Y , X)) (∘-resp-≈ˡ (⟺ F.identity)) ○ commute α (f , D.id) eq ○ ∘-resp-≈ˡ G.identity
        }

      transform : NaturalTransformation Hom[-,F-] Hom[-,G-] → NaturalTransformation F G
      transform α = ntHelper record
        { η       = λ X → η α (F.F₀ X , X) ⟨$⟩ id
        ; commute = λ {X Y} f → begin
          (η α (F.F₀ Y , Y) ⟨$⟩ id) ∘ F.F₁ f      ≈˘⟨ identityˡ ⟩
          id ∘ (η α (F.F₀ Y , Y) ⟨$⟩ id) ∘ F.F₁ f ≈˘⟨ lower (yoneda.⇒.commute {Y = Hom[ C ][-, G.F₀ Y ] , _} (idN , F.F₁ f) {nat-appʳ Y α} {nat-appʳ Y α} (cong (η α _))) ⟩
          η α (F.F₀ X , Y) ⟨$⟩ F.F₁ f ∘ id        ≈⟨ cong (η α (F.F₀ X , Y)) (∘-resp-≈ʳ (⟺ identityˡ)) ⟩
          η α (F.F₀ X , Y) ⟨$⟩ F.F₁ f ∘ id ∘ id   ≈⟨ commute α (id , f) refl ⟩
          G.F₁ f ∘ (η α (F.F₀ X , X) ⟨$⟩ id) ∘ id ≈⟨ refl⟩∘⟨ identityʳ ⟩
          G.F₁ f ∘ (η α (F.F₀ X , X) ⟨$⟩ id)      ∎
        }

  module _ (F G : Functor D C) where
    private
      module F = Functor F
      module G = Functor G
      Hom[-,F-] : Bifunctor C.op D (Setoids ℓ e)
      Hom[-,F-] = Hom[ C ][-,-] ∘F (idF ⁂ F)

      Hom[-,G-] : Bifunctor C.op D (Setoids ℓ e)
      Hom[-,G-] = Hom[ C ][-,-] ∘F (idF ⁂ G)

    yoneda-NI : NaturalIsomorphism Hom[-,F-] Hom[-,G-] → NaturalIsomorphism F G
    yoneda-NI ni = record
      { F⇒G = transform F⇒G
      ; F⇐G = transform F⇐G
      ; iso = λ X → record
        { isoˡ = begin
          (⇐.η (G.F₀ X , X) ⟨$⟩ id) ∘ (⇒.η (F.F₀ X , X) ⟨$⟩ id)      ≈˘⟨ identityˡ ⟩
          id ∘ (⇐.η (G.F₀ X , X) ⟨$⟩ id) ∘ (⇒.η (F.F₀ X , X) ⟨$⟩ id) ≈˘⟨ lower (yoneda.⇒.commute {Y = Hom[ C ][-, F.F₀ X ] , _} (idN , (⇒.η (F.F₀ X , X) ⟨$⟩ C.id))
                                                                                                 {nat-appʳ X F⇐G} {nat-appʳ X F⇐G} (cong (⇐.η _))) ⟩
          ⇐.η (F.F₀ X , X) ⟨$⟩ (⇒.η (F.F₀ X , X) ⟨$⟩ id) ∘ id        ≈⟨ cong (⇐.η _) identityʳ ⟩
          ⇐.η (F.F₀ X , X) ⟨$⟩ (⇒.η (F.F₀ X , X) ⟨$⟩ id)             ≈⟨ iso.isoˡ _ refl ⟩
          id                                                         ∎
        ; isoʳ = begin
          (⇒.η (F.F₀ X , X) ⟨$⟩ id) ∘ (⇐.η (G.F₀ X , X) ⟨$⟩ id)      ≈˘⟨ identityˡ ⟩
          id ∘ (⇒.η (F.F₀ X , X) ⟨$⟩ id) ∘ (⇐.η (G.F₀ X , X) ⟨$⟩ id) ≈˘⟨ lower (yoneda.⇒.commute {Y = Hom[ C ][-, G.F₀ X ] , _} (idN , (⇐.η (G.F₀ X , X) ⟨$⟩ C.id))
                                                                                                 {nat-appʳ X F⇒G} {nat-appʳ X F⇒G} (cong (⇒.η _))) ⟩
          ⇒.η (G.F₀ X , X) ⟨$⟩ (⇐.η (G.F₀ X , X) ⟨$⟩ id) ∘ id        ≈⟨ cong (⇒.η _) identityʳ ⟩
          ⇒.η (G.F₀ X , X) ⟨$⟩ (⇐.η (G.F₀ X , X) ⟨$⟩ id)             ≈⟨ iso.isoʳ _ refl ⟩
          id                                                         ∎
        }
      }
      where open NaturalIsomorphism ni
