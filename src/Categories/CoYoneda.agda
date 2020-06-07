{-# OPTIONS --without-K --safe #-}
module Categories.CoYoneda where

-- CoYoneda Lemma.  See Yoneda for more documentation

open import Level
open import Function.Base using (_$_)
open import Function.Bundles using (Inverse)
open import Function.Equality using (Π; _⟨$⟩_; cong)
open import Relation.Binary.Bundles using (module Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidR
open import Data.Product using (_,_; Σ)

open import Categories.Category using (Category; _[_,_])
open import Categories.Category.Product using (πʳ; πˡ; _※_)
open import Categories.Category.Construction.Presheaves using (CoPresheaves)
open import Categories.Category.Construction.Functors using (eval)
open import Categories.Category.Construction.Functors
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Hom using (module Hom; Hom[_][_,-]; Hom[_][-,-])
open import Categories.Functor.Bifunctor using (Bifunctor)
-- open import Categories.Functor.Presheaf using (Presheaf)
open import Categories.Functor.Construction.LiftSetoids using (LiftSetoids)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper) renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)

import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR
import Categories.NaturalTransformation.Hom as NT-Hom

private
  variable
    o ℓ e : Level

module Yoneda (C : Category o ℓ e) where
  open Category C hiding (op) -- uses lots
  open HomReasoning using (_○_; ⟺)
  open MR C using (id-comm)
  open NaturalTransformation using (η; commute)
  open NT-Hom C using (Hom[C,A]⇒Hom[C,B])
  private
    module CE = Category.Equiv C using (refl)
    module C = Category C using (op)

  -- The CoYoneda embedding functor
  embed : Functor C.op (CoPresheaves C)
  embed = record
    { F₀           = Hom[ C ][_,-]
    ; F₁           = Hom[C,A]⇒Hom[C,B] -- B⇒A induces a NatTrans on the Homs.
    ; identity     = identityʳ ○_
    ; homomorphism = λ h₁≈h₂ → ∘-resp-≈ˡ h₁≈h₂ ○ sym-assoc
    ; F-resp-≈     = λ f≈g h≈i → ∘-resp-≈ h≈i f≈g
    }

  -- Using the adjunction between product and product, we get a kind of contravariant Bifunctor
  yoneda-inverse : (a : Obj) (F : Functor C (Setoids ℓ e)) →
    Inverse (Category.hom-setoid (CoPresheaves C) {Functor.F₀ embed a} {F}) (Functor.F₀ F a)
  yoneda-inverse a F = record
    { f = λ nat → η nat a ⟨$⟩ id
    ; f⁻¹ = λ x → ntHelper record
        { η       = λ X → record
          { _⟨$⟩_ = λ X⇒a → F.₁ X⇒a ⟨$⟩ x
          ; cong  = λ i≈j → F.F-resp-≈ i≈j SE.refl
          }
        ; commute = λ {X} {Y} X⇒Y {f} {g} f≈g →
          let module SR = SetoidR (F.₀ Y) in
          SR.begin
             F.₁ (X⇒Y ∘ f ∘ id) ⟨$⟩ x   SR.≈⟨ F.F-resp-≈ (∘-resp-≈ʳ (identityʳ ○ f≈g)) SE.refl ⟩
             F.₁ (X⇒Y ∘ g) ⟨$⟩ x        SR.≈⟨ F.homomorphism SE.refl ⟩
             F.₁ X⇒Y ⟨$⟩ (F.₁ g ⟨$⟩ x)
           SR.∎
        }
    ; cong₁ = λ i≈j → i≈j CE.refl
    ; cong₂ = λ i≈j y≈z → F.F-resp-≈ y≈z i≈j
    ; inverse = (λ Fa → F.identity SE.refl) , λ nat {x} {z} {y} z≈y →
        let module SR     = SetoidR (F.₀ x) in
        SR.begin
          F.₁ z ⟨$⟩ (η nat a ⟨$⟩ id) SR.≈˘⟨ commute nat z (CE.refl {a}) ⟩
          η nat x ⟨$⟩ z ∘ id ∘ id SR.≈⟨ cong (η nat x) (∘-resp-≈ʳ identity² ○ identityʳ ○ z≈y ) ⟩
          η nat x ⟨$⟩ y
        SR.∎
    }
    where
    module F = Functor F using (₀; ₁; F-resp-≈; homomorphism; identity)
    module SE = Setoid (F.₀ a) using (refl)

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
          { _⟨$⟩_ = λ α → lift (yoneda-inverse.f α)
          ; cong  = λ i≈j → lift (i≈j CE.refl)
          }
      ; commute = λ where
        {_} {G , B} (α , f) {β} {γ} β≈γ → lift $ cong (η α B) (helper f β γ β≈γ)
      }
    ; F⇐G = ntHelper record
      { η       = λ (F , A) → record
          { _⟨$⟩_ = λ x → yoneda-inverse.f⁻¹ (lower x)
          ; cong  = λ i≈j y≈z → Functor.F-resp-≈ F y≈z (lower i≈j)
          }
      ; commute = λ { {F , A} {G , B} (α , f) {X} {Y} eq {Z} {h} {i} eq′ → helper′ α f (lower eq) eq′}
      }
    ; iso = λ (F , A) → record
        { isoˡ = λ {α β} i≈j {X} y≈z →
          Setoid.trans (Functor.F₀ F X) ( yoneda-inverse.inverseʳ α {x = X} y≈z) (i≈j CE.refl)
        ; isoʳ = λ eq → lift (Setoid.trans (Functor.F₀ F A) ( yoneda-inverse.inverseˡ {F = F} _) (lower eq))
        }
    }
    where helper : {F : Functor C (Setoids ℓ e)}
                   {A B : Obj} (f : A ⇒ B)
                   (β γ : NaturalTransformation Hom[ C ][ A ,-] F) →
                   Setoid._≈_ (Functor.F₀ Nat[Hom[C][c,-],F] (F , A)) β γ →
                   Setoid._≈_ (Functor.F₀ F B) (η β B ⟨$⟩ id ∘ f) (Functor.F₁ F f ⟨$⟩ (η γ A ⟨$⟩ id))
          helper {F} {A} {B} f β γ β≈γ = S.begin
            η β B ⟨$⟩ id ∘ f        S.≈⟨ cong (η β B) (MR.id-comm-sym C ○ ∘-resp-≈ʳ (⟺ identity²)) ⟩
            η β B ⟨$⟩ f ∘ id ∘ id   S.≈⟨ commute β f CE.refl ⟩
            F.₁ f ⟨$⟩ (η β A ⟨$⟩ id) S.≈⟨ cong (F.₁ f) (β≈γ CE.refl) ⟩
            F.₁ f ⟨$⟩ (η γ A ⟨$⟩ id) S.∎
            where
            module F = Functor F using (₀;₁)
            module S = SetoidR (F.₀ B)

          helper′ : ∀ {F G : Functor C (Setoids ℓ e)}
                      {A B Z : Obj}
                      {h i : B ⇒ Z}
                      {X Y : Setoid.Carrier (Functor.F₀ F A)}
                      (α : NaturalTransformation F G)
                      (f : A ⇒ B) →
                      Setoid._≈_ (Functor.F₀ F A) X Y →
                      h ≈ i →
                      Setoid._≈_ (Functor.F₀ G Z) (Functor.F₁ G h ⟨$⟩ (η α B ⟨$⟩ (Functor.F₁ F f ⟨$⟩ X)))
                                          (η α Z ⟨$⟩ (Functor.F₁ F (i ∘ f) ⟨$⟩ Y))
          helper′ {F} {G} {A} {B} {Z} {h} {i} {X} {Y} α f eq eq′ = S.begin
            G.₁ h ⟨$⟩ (η α B ⟨$⟩ (F.₁ f ⟨$⟩ X))  S.≈˘⟨ commute α h ((S′.sym (cong (F.₁ f) eq))) ⟩
            η α Z ⟨$⟩ (F.₁ h ⟨$⟩ (F.₁ f ⟨$⟩ Y))  S.≈⟨ cong (η α Z) ((F.F-resp-≈ eq′ S′.refl)) ⟩
            η α Z ⟨$⟩ (F.₁ i ⟨$⟩ (F.₁ f ⟨$⟩ Y))  S.≈˘⟨ cong (η α Z) ((F.homomorphism (Setoid.refl (F.₀ A)))) ⟩
            η α Z ⟨$⟩ (F.₁ (i ∘ f) ⟨$⟩ Y)        S.∎
            where
              module F = Functor F using (₀; ₁; homomorphism; F-resp-≈)
              module G = Functor G using (₀; ₁)
              module S = SetoidR (G.₀ Z)
              module S′ = Setoid (F.₀ B) using (refl; sym)

  module yoneda = NaturalIsomorphism yoneda
