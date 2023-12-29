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
open import Function.Base using (_$_) renaming (id to id→)
open import Function.Bundles using (Func; Inverse; _⟨$⟩_)
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

open Func

private
  variable
    o ℓ e : Level

module Yoneda (C : Category o ℓ e) where
  open Category C hiding (op) -- uses lots
  open HomReasoning using (_○_; ⟺)
  open MR C using (id-comm)
  open NaturalTransformation using (η; commute; sym-commute)
  open NT-Hom C using (Hom[A,C]⇒Hom[B,C])
  private
    module CE = Category.Equiv C using (refl)
    module C = Category C using (op)

  -- The Yoneda embedding functor
  embed : Functor C (Presheaves C)
  embed = record
    { F₀           = Hom[ C ][-,_]
    ; F₁           = Hom[A,C]⇒Hom[B,C] -- A⇒B induces a NatTrans on the Homs.
    ; identity     = identityˡ
    ; homomorphism = assoc
    ; F-resp-≈     = λ f≈g → ∘-resp-≈ˡ f≈g
    }

  -- Using the adjunction between product and product, we get a kind of contravariant Bifunctor
  yoneda-inverse : (a : Obj) (F : Presheaf C (Setoids ℓ e)) →
    Inverse (Category.hom-setoid (Presheaves C) {Functor.F₀ embed a} {F}) (Functor.F₀ F a)
  yoneda-inverse a F = record
    { to = λ nat → η nat a ⟨$⟩ id
    ; from = λ x → ntHelper record
        { η       = λ X → record
          { to = λ X⇒a → F.₁ X⇒a ⟨$⟩ x
          ; cong  = λ i≈j → F.F-resp-≈ i≈j
          }
        ; commute = λ {X} {Y} Y⇒X {f} →
          let module SR = SetoidR (F.₀ Y) in
          SR.begin
             F.₁ (id ∘ f ∘ Y⇒X) ⟨$⟩ x   SR.≈⟨ F.F-resp-≈ identityˡ ⟩
             F.₁ (f ∘ Y⇒X) ⟨$⟩ x        SR.≈⟨ F.homomorphism ⟩
             F.₁ Y⇒X ⟨$⟩ (F.₁ f ⟨$⟩ x)
           SR.∎
        }
    ; to-cong = λ i≈j → i≈j
    ; from-cong = λ x≈y → cong (F.₁ _) x≈y
    ; inverse = record
      { fst = λ p → Setoid.trans (F.₀ a) p F.identity
      ; snd = λ {nat} p {x} {f} →
        let module S = Setoid (F.₀ x) in
        S.trans
          (S.trans
            (cong (F.₁ f) p)
            (sym-commute nat f))
          (cong (η nat x) (identityˡ ○ identityˡ))
      }
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
          { to = λ α → lift (yoneda-inverse.to α)
          ; cong  = λ i≈j → lift i≈j
          }
      ; commute = λ where
        {_} {G , B} (α , f) {β} → lift $ cong (η α B) (helper f β)
      }
    ; F⇐G = ntHelper record
      { η       = λ { (F , A) → record
          { to = λ x → yoneda-inverse.from (lower x)
          ; cong  = λ x≈y → cong (Functor.F₁ F _) (lower x≈y)
          } }
      ; commute = λ { {F , X} (α , f) → helper′ α f (Setoid.refl (Functor.F₀ F X)) }
      }
    ; iso = λ { (F , A) → record
        { isoˡ = λ {α} → yoneda-inverse.strictlyInverseʳ α
        ; isoʳ = lift (Functor.identity F)
        } }
    }
    where helper : {F : Functor C.op (Setoids ℓ e)}
                   {A B : Obj} (f : B ⇒ A)
                   (β : NaturalTransformation Hom[ C ][-, A ] F) →
                   Setoid._≈_ (Functor.F₀ F B) (η β B ⟨$⟩ f ∘ id) (Functor.F₁ F f ⟨$⟩ (η β A ⟨$⟩ id))
          helper {F} {A} {B} f β = S.begin
            η β B ⟨$⟩ f ∘ id         S.≈⟨ cong (η β B) (id-comm ○ (⟺ identityˡ)) ⟩
            η β B ⟨$⟩ id ∘ id ∘ f    S.≈⟨ commute β f ⟩
            F.₁ f ⟨$⟩ (η β A ⟨$⟩ id) S.∎
            where
            module F = Functor F using (₀;₁)
            module S = SetoidR (F.₀ B)

          helper′ : ∀ {F G : Functor (Category.op C) (Setoids ℓ e)}
                      {A B Z : Obj}
                      {h : Z ⇒ B}
                      {X Y : Setoid.Carrier (Functor.F₀ F A)}
                      (α : NaturalTransformation F G)
                      (f : B ⇒ A) →
                      Setoid._≈_ (Functor.F₀ F A) X Y →
                      Setoid._≈_ (Functor.F₀ G Z) (Functor.F₁ G h ⟨$⟩ (η α B ⟨$⟩ (Functor.F₁ F f ⟨$⟩ X)))
                                          (η α Z ⟨$⟩ (Functor.F₁ F (f ∘ h) ⟨$⟩ Y))
          helper′ {F} {G} {A} {B} {Z} {h} {X} {Y} α f eq = S.begin
            G.₁ h ⟨$⟩ (η α B ⟨$⟩ (F.₁ f ⟨$⟩ X)) S.≈˘⟨ commute α h ⟩
            η α Z ⟨$⟩ (F.₁ h ⟨$⟩ (F.₁ f ⟨$⟩ X)) S.≈⟨ cong (η α Z) (cong (F.₁ h) (cong (F.₁ f) eq)) ⟩
            η α Z ⟨$⟩ (F.₁ h ⟨$⟩ (F.₁ f ⟨$⟩ Y)) S.≈˘⟨ cong (η α Z) F.homomorphism ⟩
            η α Z ⟨$⟩ (F.₁ (f ∘ h) ⟨$⟩ Y)       S.∎
            where
              module F = Functor F using (₀; ₁; homomorphism; F-resp-≈)
              module G = Functor G using (₀; ₁)
              module S = SetoidR (G.₀ Z)
              module S′ = Setoid (F.₀ B) using (refl; sym)

  module yoneda = NaturalIsomorphism yoneda
