{-# OPTIONS --without-K --safe #-}
module Categories.CoYoneda where

-- CoYoneda Lemma.  See Yoneda for more documentation

open import Level using (Level; _⊔_; lift; lower)
open import Function.Base using (_$_)
open import Function.Bundles using (Inverse; Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (module Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidR
open import Data.Product using (_,_; Σ)

open import Categories.Category using (Category; _[_,_])
open import Categories.Category.Product using (πʳ; πˡ; _※_)
open import Categories.Category.Construction.Presheaves using (CoPresheaves)
open import Categories.Category.Construction.Functors using (eval)
open import Categories.Category.Construction.Functors using (Functors)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Hom using (module Hom; Hom[_][_,-]; Hom[_][-,-])
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Functor.Construction.LiftSetoids using (LiftSetoids)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper) renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)

import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR
import Categories.NaturalTransformation.Hom as NT-Hom

open Func

private
  variable
    o ℓ e : Level

module Yoneda (C : Category o ℓ e) where
  open Category C hiding (op) -- uses lots
  open HomReasoning using (_○_; ⟺; refl⟩∘⟨_)
  open MR C using (id-comm)
  open NaturalTransformation using (η; commute; sym-commute)
  open NT-Hom C using (Hom[C,A]⇒Hom[C,B])
  private
    module CE = Category.Equiv C using (refl)
    module C = Category C using (op)

  -- The CoYoneda embedding functor
  embed : Functor C.op (CoPresheaves C)
  embed = record
    { F₀           = Hom[ C ][_,-]
    ; F₁           = Hom[C,A]⇒Hom[C,B] -- B⇒A induces a NatTrans on the Homs.
    ; identity     = identityʳ
    ; homomorphism = sym-assoc
    ; F-resp-≈     = λ f≈g → refl⟩∘⟨ f≈g
    }

  -- Using the adjunction between product and product, we get a kind of contravariant Bifunctor
  yoneda-inverse : (a : Obj) (F : Functor C (Setoids ℓ e)) →
    Inverse (Category.hom-setoid (CoPresheaves C) {Functor.F₀ embed a} {F}) (Functor.F₀ F a)
  yoneda-inverse a F = record
    { to = λ nat → η nat a ⟨$⟩ id
    ; from = λ x → ntHelper record
        { η       = λ X → record
          { to = λ X⇒a → F.₁ X⇒a ⟨$⟩ x
          ; cong  = λ i≈j → F.F-resp-≈ i≈j
          }
        ; commute = λ {X} {Y} X⇒Y {f} →
          let module SR = SetoidR (F.₀ Y) in
          SR.begin
             F.₁ (X⇒Y ∘ f ∘ id) ⟨$⟩ x   SR.≈⟨ F.F-resp-≈ (∘-resp-≈ʳ identityʳ) ⟩
             F.₁ (X⇒Y ∘ f) ⟨$⟩ x        SR.≈⟨ F.homomorphism ⟩
             F.₁ X⇒Y ⟨$⟩ (F.₁ f ⟨$⟩ x)
           SR.∎
        }
    ; to-cong = λ i≈j → i≈j
    ; from-cong = λ i≈j → cong (F.₁ _) i≈j
    ; inverse =
       ( λ {b} {nat} eq →
          let module SR = SetoidR (F.₀ a) in
          let open SR in begin
          to (η nat a) id ≈⟨ eq ⟩
          to (F.₁ id) b    ≈⟨ F.identity ⟩
           b                    ∎)
       , λ {nat} {y} eq {b} {f} →
          let open Setoid (F.₀ b) in
          let module SR = SetoidR (F.₀ b) in
          let open SR in
          begin
            to (F.₁ f) y                 ≈⟨ cong (F.₁ f) eq ⟩
            to (F.₁ f) (to (η nat a) id) ≈⟨ sym-commute nat f  ⟩
            to (η nat b) (f ∘ id ∘ id)   ≈⟨ cong (η nat b) (refl⟩∘⟨ identity² ○ identityʳ) ⟩
            to (η nat b) f               ∎
    }
    where
    module F = Functor F using (₀; ₁; F-resp-≈; homomorphism; identity)
    module SE = Setoid (F.₀ a)

  private
    Nat[Hom[C][c,-],F] : Bifunctor (CoPresheaves C) C (Setoids (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e))
    Nat[Hom[C][c,-],F] = Hom[ CoPresheaves C ][-,-] ∘F (Functor.op embed ∘F πʳ ※ πˡ)

    FC : Bifunctor (CoPresheaves C) C (Setoids _ _)
    FC = LiftSetoids (o ⊔ ℓ ⊔ e) (o ⊔ ℓ) ∘F eval {C = C} {D = Setoids ℓ e}

    module yoneda-inverse {a} {F} = Inverse (yoneda-inverse a F)

  -- the two bifunctors above are naturally isomorphic.
  -- it is easy to show yoneda-inverse first then to yoneda.
  yoneda : NaturalIsomorphism Nat[Hom[C][c,-],F] FC
  yoneda = record
    { F⇒G = ntHelper record
      { η       = λ where
        (F , A) → record
          { to = λ α → lift (yoneda-inverse.to α)
          ; cong  = λ i≈j → lift i≈j
          }
      ; commute = λ where
        {_} {G , B} (α , f) {β} → lift $ cong (η α B) (helper f β)
      }
    ; F⇐G = ntHelper record
      { η       = λ { (F , A) → record
          { to = λ x → yoneda-inverse.from (lower x)
          ; cong  = λ i≈j → cong (Functor.F₁ F _) (lower i≈j)
          } }
      ; commute = λ { {F , A} {G , B} (α , f) {X} {Z} {h} → helper′ α f}
      }
    ; iso = λ { (F , A) → record
        { isoˡ = λ {α} → yoneda-inverse.strictlyInverseʳ α
        ; isoʳ = lift (Functor.identity F)
        } }
    }
    where helper : {F : Functor C (Setoids ℓ e)}
                   {A B : Obj} (f : A ⇒ B)
                   (β : NaturalTransformation Hom[ C ][ A ,-] F) →
                   Setoid._≈_ (Functor.F₀ F B) (η β B ⟨$⟩ id ∘ f) (Functor.F₁ F f ⟨$⟩ (η β A ⟨$⟩ id))
          helper {F} {A} {B} f β = S.begin
            η β B ⟨$⟩ id ∘ f        S.≈⟨ cong (η β B) (MR.id-comm-sym C ○ ∘-resp-≈ʳ (⟺ identity²)) ⟩
            η β B ⟨$⟩ f ∘ id ∘ id   S.≈⟨ commute β f ⟩
            F.₁ f ⟨$⟩ (η β A ⟨$⟩ id) S.∎
            where
            module F = Functor F using (₀;₁)
            module S = SetoidR (F.₀ B)

          helper′ : ∀ {F G : Functor C (Setoids ℓ e)}
                      {A B Z : Obj}
                      {h : B ⇒ Z}
                      {X : Setoid.Carrier (Functor.F₀ F A)}
                      (α : NaturalTransformation F G)
                      (f : A ⇒ B) →
                      Setoid._≈_ (Functor.F₀ G Z) (Functor.F₁ G h ⟨$⟩ (η α B ⟨$⟩ (Functor.F₁ F f ⟨$⟩ X)))
                                          (η α Z ⟨$⟩ (Functor.F₁ F (h ∘ f) ⟨$⟩ X))
          helper′ {F} {G} {A} {B} {Z} {h} {X} α f = S.begin
            G.₁ h ⟨$⟩ (η α B ⟨$⟩ (F.₁ f ⟨$⟩ X))  S.≈˘⟨ commute α h ⟩
            η α Z ⟨$⟩ (F.₁ h ⟨$⟩ (F.₁ f ⟨$⟩ X))  S.≈˘⟨ cong (η α Z) F.homomorphism ⟩
            η α Z ⟨$⟩ (F.₁ (h ∘ f) ⟨$⟩ X)       S.∎
            where
              module F = Functor F using (₀; ₁; homomorphism; F-resp-≈)
              module G = Functor G using (₀; ₁)
              module S = SetoidR (G.₀ Z)

  module yoneda = NaturalIsomorphism yoneda
