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
open import Function using (_$_; Inverse) -- else there's a conflict with the import below
open import Function.Equality using (Π; _⟨$⟩_; cong)
open import Relation.Binary using (module Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidR
open import Data.Product using (_,_; Σ)

open import Categories.Category using (Category; _[_,_])
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

import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR
import Categories.NaturalTransformation.Hom as NT-Hom

private
  variable
    o ℓ e : Level

module Yoneda (C : Category o ℓ e) where
  open Category C
  open HomReasoning
  open MR C
  open Functor
  open NaturalTransformation
  open NT-Hom C
  private
    module CE = Category.Equiv C
    module C = Category C

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
          { _⟨$⟩_ = λ X⇒a → F₁ F X⇒a ⟨$⟩ x
          ; cong  = λ i≈j → F-resp-≈ F i≈j SE.refl
          }
        ; commute = λ {X} {Y} Y⇒X {f} {g} f≈g →
          let module SFY = Setoid (F₀ F Y) in
          let module SR = SetoidR (F₀ F Y) in
          SR.begin
             F₁ F (id ∘ f ∘ Y⇒X) ⟨$⟩ x   SR.≈⟨ F-resp-≈ F (identityˡ ○ ∘-resp-≈ˡ f≈g) (SE.refl {x}) ⟩
             F₁ F (g ∘ Y⇒X) ⟨$⟩ x        SR.≈⟨ homomorphism F SE.refl ⟩
             F₁ F Y⇒X ⟨$⟩ (F₁ F g ⟨$⟩ x)
           SR.∎
        }
    ; cong₁ = λ i≈j → i≈j CE.refl
    ; cong₂ = λ i≈j y≈z → F-resp-≈ F y≈z i≈j
    ; inverse = (λ Fa → identity F SE.refl) , λ nat {x} {z} z≈y →
        let module S     = Setoid (F₀ F x) in
        S.trans (S.sym (commute nat z CE.refl))
                (cong (η nat x) (identityˡ ○ identityˡ ○ z≈y))
    }
    where module SE = Setoid (F₀ F a)

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
      { η       = λ where
        (F , A) → record
          { _⟨$⟩_ = λ where
            (lift x) → yoneda-inverse.f⁻¹ x
          ; cong  = λ where
            (lift i≈j) y≈z → F-resp-≈ F y≈z i≈j
          }
      ; commute = λ where
        (α , f) (lift eq) eq′ → helper′ α f eq eq′
      }
    ; iso = λ where
      (F , A) → record
        { isoˡ = λ {α β} i≈j {X} y≈z →
          let module S = Setoid (F₀ F X)
          in S.trans ( yoneda-inverse.inverseʳ α {x = X} y≈z) (i≈j CE.refl)
        ; isoʳ = λ where
          (lift eq) →
            let module S = Setoid (F₀ F A)
            in lift (S.trans ( yoneda-inverse.inverseˡ {F = F} _) eq)
        }
    }
    where helper : ∀ {F : Functor (Category.op C) (Setoids ℓ e)}
                     {A B : Obj} (f : B ⇒ A)
                     (β γ : NaturalTransformation Hom[ C ][-, A ] F) →
                   Setoid._≈_ (F₀ Nat[Hom[C][-,c],F] (F , A)) β γ →
                   Setoid._≈_ (F₀ F B) (η β B ⟨$⟩ f ∘ id) (F₁ F f ⟨$⟩ (η γ A ⟨$⟩ id))
          helper {F} {A} {B} f β γ β≈γ = S.begin
            η β B ⟨$⟩ f ∘ id          S.≈⟨ cong (η β B) (id-comm ○ (⟺ identityˡ)) ⟩
            η β B ⟨$⟩ id ∘ id ∘ f     S.≈⟨ commute β f CE.refl ⟩
            F₁ F f ⟨$⟩ (η β A ⟨$⟩ id) S.≈⟨ cong (F₁ F f) (β≈γ CE.refl) ⟩
            F₁ F f ⟨$⟩ (η γ A ⟨$⟩ id) S.∎
            where module S where
                    open Setoid (F₀ F B) public
                    open SetoidR (F₀ F B) public

          helper′ : ∀ {F G : Functor (Category.op C) (Setoids ℓ e)}
                      {A B Z : Obj}
                      {h i : Z ⇒ B}
                      {X Y : Setoid.Carrier (F₀ F A)}
                      (α : NaturalTransformation F G)
                      (f : B ⇒ A) →
                      Setoid._≈_ (F₀ F A) X Y →
                      h ≈ i →
                      Setoid._≈_ (F₀ G Z) (F₁ G h ⟨$⟩ (η α B ⟨$⟩ (F₁ F f ⟨$⟩ X)))
                                          (η α Z ⟨$⟩ (F₁ F (f ∘ i) ⟨$⟩ Y))
          helper′ {F} {G} {A} {B} {Z} {h} {i} {X} {Y} α f eq eq′ = S.begin
            F₁ G h ⟨$⟩ (η α B ⟨$⟩ (F₁ F f ⟨$⟩ X)) S.≈˘⟨ commute α h (S′.sym (cong (F₁ F f) eq)) ⟩
            η α Z ⟨$⟩ (F₁ F h ⟨$⟩ (F₁ F f ⟨$⟩ Y)) S.≈⟨ cong (η α Z) (F-resp-≈ F eq′ S′.refl) ⟩
            η α Z ⟨$⟩ (F₁ F i ⟨$⟩ (F₁ F f ⟨$⟩ Y)) S.≈˘⟨ cong (η α Z) (homomorphism F (Setoid.refl (F₀ F A))) ⟩
            η α Z ⟨$⟩ (F₁ F (f ∘ i) ⟨$⟩ Y)        S.∎
            where module S where
                    open Setoid (F₀ G Z) public
                    open SetoidR (F₀ G Z) public
                  module S′ = Setoid (F₀ F B)

  module yoneda = NaturalIsomorphism yoneda
