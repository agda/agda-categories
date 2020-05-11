{-# OPTIONS --without-K --safe #-}
module Categories.Yoneda where

-- Yoneda Lemma.  In total, provides:
-- * the Yoneda Embedding (called embed here) from any Category C into Presheaves C
--   Worth noticing that there is no 'locally small' condition here; however, if one looks at
--   the levels involved, there is indeed a raise from that of C to that of Presheaves C.
-- * The traditional Yoneda lemma (yoneda-inverse) which says that for any object a of C, and
--   any Presheaf F over C (where our presheaves are over Setoids), then
--   Hom[ Presheaves C] (Functor.F₀ embed a , F) ≅ Functor.F₀ F a
--   as Setoids. In addition, Yoneda (yoneda) also says that this isomorphism is natural in a and F.
open import Level
open import Function.Base using (_$_)
open import Function.Bundles using (Inverse)
open import Function.Equality using (Π; _⟨$⟩_; cong)
open import Relation.Binary.Bundles using (module Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidR
open import Data.Product using (_,_; Σ)

open import Categories.Category using (Category; _[_,_])
open import Categories.Category.Product using (πʳ; πˡ; _※_)
open import Categories.Category.Construction.Presheaves using (Presheaves)
open import Categories.Category.Construction.Functors using (eval)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Hom using (module Hom; Hom[_][-,_]; Hom[_][-,-])
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Functor.Presheaf using (Presheaf)
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
  open NT-Hom C using (Hom[A,C]⇒Hom[B,C])
  private
    module CE = Category.Equiv C using (refl)
    module C = Category C using (op)

  -- The Yoneda embedding functor
  embed : Functor C (Presheaves C)
  embed = record
    { F₀           = Hom[ C ][-,_]
    ; F₁           = Hom[A,C]⇒Hom[B,C] -- A⇒B induces a NatTrans on the Homs.
    ; identity     = identityˡ ○_
    ; homomorphism = λ h₁≈h₂ → ∘-resp-≈ʳ h₁≈h₂ ○ assoc
    ; F-resp-≈     = λ f≈g h≈i → ∘-resp-≈ f≈g h≈i
    }

  -- Using the adjunction between product and product, we get a kind of contravariant Bifunctor
  yoneda-inverse : (a : Obj) (F : Presheaf C (Setoids ℓ e)) →
    Inverse (Category.hom-setoid (Presheaves C) {Functor.F₀ embed a} {F}) (Functor.F₀ F a)
  yoneda-inverse a F = record
    { f = λ nat → η nat a ⟨$⟩ id
    ; f⁻¹ = λ x → ntHelper record
        { η       = λ X → record
          { _⟨$⟩_ = λ X⇒a → F.₁ X⇒a ⟨$⟩ x
          ; cong  = λ i≈j → F.F-resp-≈ i≈j SE.refl
          }
        ; commute = λ {X} {Y} Y⇒X {f} {g} f≈g →
          let module SR = SetoidR (F.₀ Y) in
          SR.begin
             F.₁ (id ∘ f ∘ Y⇒X) ⟨$⟩ x   SR.≈⟨ F.F-resp-≈ (identityˡ ○ ∘-resp-≈ˡ f≈g) (SE.refl {x}) ⟩
             F.₁ (g ∘ Y⇒X) ⟨$⟩ x        SR.≈⟨ F.homomorphism SE.refl ⟩
             F.₁ Y⇒X ⟨$⟩ (F.₁ g ⟨$⟩ x)
           SR.∎
        }
    ; cong₁ = λ i≈j → i≈j CE.refl
    ; cong₂ = λ i≈j y≈z → F.F-resp-≈ y≈z i≈j
    ; inverse = (λ Fa → F.identity SE.refl) , λ nat {x} {z} z≈y →
        let module S     = Setoid (F.₀ x) in
        S.trans (S.sym (commute nat z CE.refl))
                (cong (η nat x) (identityˡ ○ identityˡ ○ z≈y))
    }
    where
    module F = Functor F using (₀; ₁; F-resp-≈; homomorphism; identity)
    module SE = Setoid (F.₀ a) using (refl)

  private
    -- in this bifunctor, a presheaf from Presheaves C goes from C to Setoids ℓ e,
    -- but the over Setoids has higher level than the hom setoids.
    Nat[Hom[C][-,c],F] : Bifunctor (Presheaves C) (Category.op C) (Setoids _ _)
    Nat[Hom[C][-,c],F] = Hom[ Presheaves C ][-,-] ∘F (Functor.op embed ∘F πʳ ※ πˡ)

    -- in this bifunctor, it needs to go from Presheaves which maps C to Setoids ℓ e,
    -- so the universe level needs to be lifted.
    FC : Bifunctor (Presheaves C) (Category.op C) (Setoids _ _)
    FC = LiftSetoids (o ⊔ ℓ ⊔ e) (o ⊔ ℓ) ∘F eval {C = Category.op C} {D = Setoids ℓ e}

    module yoneda-inverse {a} {F} = Inverse (yoneda-inverse a F)

  -- the two bifunctors above are naturally isomorphic.
  -- it is easy to show yoneda-inverse first then to yoneda.
  yoneda : NaturalIsomorphism Nat[Hom[C][-,c],F] FC
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
      ; commute = λ (α , f) eq eq′ → helper′ α f (lower eq) eq′
      }
    ; iso = λ (F , A) → record
        { isoˡ = λ {α β} i≈j {X} y≈z →
          Setoid.trans (Functor.F₀ F X) ( yoneda-inverse.inverseʳ α {x = X} y≈z) (i≈j CE.refl)
        ; isoʳ = λ eq → lift (Setoid.trans (Functor.F₀ F A) ( yoneda-inverse.inverseˡ {F = F} _) (lower eq))
        }
    }
    where helper : {F : Functor C.op (Setoids ℓ e)}
                   {A B : Obj} (f : B ⇒ A)
                   (β γ : NaturalTransformation Hom[ C ][-, A ] F) →
                   Setoid._≈_ (Functor.F₀ Nat[Hom[C][-,c],F] (F , A)) β γ →
                   Setoid._≈_ (Functor.F₀ F B) (η β B ⟨$⟩ f ∘ id) (Functor.F₁ F f ⟨$⟩ (η γ A ⟨$⟩ id))
          helper {F} {A} {B} f β γ β≈γ = S.begin
            η β B ⟨$⟩ f ∘ id          S.≈⟨ cong (η β B) (id-comm ○ (⟺ identityˡ)) ⟩
            η β B ⟨$⟩ id ∘ id ∘ f     S.≈⟨ commute β f CE.refl ⟩
            F.₁ f ⟨$⟩ (η β A ⟨$⟩ id) S.≈⟨ cong (F.₁ f) (β≈γ CE.refl) ⟩
            F.₁ f ⟨$⟩ (η γ A ⟨$⟩ id) S.∎
            where
            module F = Functor F using (₀;₁)
            module S = SetoidR (F.₀ B)

          helper′ : ∀ {F G : Functor (Category.op C) (Setoids ℓ e)}
                      {A B Z : Obj}
                      {h i : Z ⇒ B}
                      {X Y : Setoid.Carrier (Functor.F₀ F A)}
                      (α : NaturalTransformation F G)
                      (f : B ⇒ A) →
                      Setoid._≈_ (Functor.F₀ F A) X Y →
                      h ≈ i →
                      Setoid._≈_ (Functor.F₀ G Z) (Functor.F₁ G h ⟨$⟩ (η α B ⟨$⟩ (Functor.F₁ F f ⟨$⟩ X)))
                                          (η α Z ⟨$⟩ (Functor.F₁ F (f ∘ i) ⟨$⟩ Y))
          helper′ {F} {G} {A} {B} {Z} {h} {i} {X} {Y} α f eq eq′ = S.begin
            G.₁ h ⟨$⟩ (η α B ⟨$⟩ (F.₁ f ⟨$⟩ X)) S.≈˘⟨ commute α h (S′.sym (cong (F.₁ f) eq)) ⟩
            η α Z ⟨$⟩ (F.₁ h ⟨$⟩ (F.₁ f ⟨$⟩ Y)) S.≈⟨ cong (η α Z) (F.F-resp-≈ eq′ S′.refl) ⟩
            η α Z ⟨$⟩ (F.₁ i ⟨$⟩ (F.₁ f ⟨$⟩ Y)) S.≈˘⟨ cong (η α Z) (F.homomorphism (Setoid.refl (F.₀ A))) ⟩
            η α Z ⟨$⟩ (F.₁ (f ∘ i) ⟨$⟩ Y)        S.∎
            where
              module F = Functor F using (₀; ₁; homomorphism; F-resp-≈)
              module G = Functor G using (₀; ₁)
              module S = SetoidR (G.₀ Z)
              module S′ = Setoid (F.₀ B) using (refl; sym)

  module yoneda = NaturalIsomorphism yoneda
