{-# OPTIONS --without-K --safe #-}
module Categories.Yoneda where

-- Yoneda Lemma.  In total, provides:
-- * the Yoneda Embedding (called embed here) from any Category C into Presheaves C
--   Worth noticing that there is no 'locally small' condition here; however, if one looks at
--   the levels involved, there is indeed a raise from that of C to that of Presheaves C.
-- * The traditional Yoneda lemma (yoneda) which says that for any object a of C, and
--   any Presheaf F over C (where our presheaves are over Setoids), then
--   Hom[ Presheaves C] (Functor.F₀ embed a , F) ≅ Functor.F₀ F a
--   as Setoids.
--    Note that the original Categories.Yoneda proves something that looks more general,
--    but is merely are rephrasing: the NaturalIsomorphism is 'over' Setoids, where it
--    specializes to Inverse.
open import Level
open import Function.Inverse using (Inverse)
open import Function.Equality using (_⟨$⟩_)
open import Relation.Binary using (module Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidR
open import Data.Product using (_,_; Σ)

open import Categories.Category using (Category; _[_,_])
open import Categories.Functor using (Functor; Full; Faithful; FullyFaithful)
open import Categories.Functor.Hom using (module Hom; Hom[_][-,_])
open import Categories.Category.Construction.Presheaves
open import Categories.Category.Instance.Setoids
open import Categories.Functor.Presheaf
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.NaturalTransformation.NaturalIsomorphism
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level

module _ (C : Category o ℓ e) where
  open Category C
  open HomReasoning
  open Functor
  open NaturalTransformation
  module CE = Category.Equiv C
  open Function.Equality using (cong)

  -- This NaturalTransformation should probably got into NaturalTransformation.Hom,
  -- in analogy with Functor.Hom above.
  Hom[A,C]⇒Hom[B,C] : {A B : Obj} → (A ⇒ B) → NaturalTransformation (Hom.Hom[-, C ] A) (Hom.Hom[-, C ] B)
  Hom[A,C]⇒Hom[B,C] {A} A⇒B = record
    { η = λ X → record { _⟨$⟩_ = λ X⇒A → A⇒B ∘ X⇒A ; cong = ∘-resp-≈ʳ }
    ; commute = λ {X} {Y} f {g} {h} g≈h → begin
        A⇒B ∘ id ∘ g ∘ f   ≈˘⟨ assoc ⟩
        (A⇒B ∘ id) ∘ g ∘ f ≈⟨ ∘-resp-≈ id-comm (∘-resp-≈ˡ g≈h) ⟩
        (id ∘ A⇒B) ∘ h ∘ f ≈⟨ assoc ○ ⟺ (∘-resp-≈ʳ assoc) ⟩ -- TODO: MR.Reassociate
        id ∘ (A⇒B ∘ h) ∘ f ∎
    }

  -- The Yoneda embedding functor
  embed : Functor C (Presheaves C)
  embed = record
    { F₀ = Hom[ C ][-,_]
    ; F₁ = Hom[A,C]⇒Hom[B,C] -- A⇒B induces a NatTrans on the Homs.
    ; identity = identityˡ ○_
    ; homomorphism = λ h₁≈h₂ → ∘-resp-≈ʳ h₁≈h₂ ○ assoc
    ; F-resp-≈ = λ f≈g h≈i → ∘-resp-≈ f≈g h≈i
    }

  -- Using the adjunction between product and product, we get a kind of contravariant Bifunctor
  yoneda : (a : Obj) (F : Presheaf C (Setoids ℓ e)) →
    Inverse (Category.hom-setoid (Presheaves C) {Functor.F₀ embed a} {F}) (Functor.F₀ F a)
  yoneda a F = record
    { to = record
      { _⟨$⟩_ = λ nat → η nat a ⟨$⟩ id
      ; cong = λ i≈j → i≈j CE.refl
      }
    ; from = record
      { _⟨$⟩_ = λ x → record
        { η = λ X → record
          { _⟨$⟩_ = λ X⇒a → F₁ F X⇒a ⟨$⟩ x
          ; cong = λ i≈j → F-resp-≈ F i≈j SE.refl
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
      ; cong = λ i≈j y≈z → F-resp-≈ F y≈z i≈j
      }
    ; inverse-of = record
      { left-inverse-of = λ nat {x} {z} z≈y →
        let module S = Setoid (F₀ F x) in
        S.trans (S.sym (commute nat z CE.refl))
                (cong (η nat x) (identityˡ ○ identityˡ ○ z≈y))
      ; right-inverse-of = λ Fa → identity F SE.refl
      }
    }
    where module SE = Setoid (F₀ F a)

  YoFull : Full embed
  YoFull {X} {Y} = record
      { to = record
        { _⟨$⟩_ = Hom[A,C]⇒Hom[B,C]
        ; cong = λ i≈j f≈g → ∘-resp-≈ i≈j f≈g
        }
      ; surjective = record
        { from = record { _⟨$⟩_ = λ ε → η ε X ⟨$⟩ id ; cong = λ i≈j → i≈j CE.refl }
        ; right-inverse-of = λ ε {x} {z} {y} z≈y →
          begin
            (η ε X ⟨$⟩ id) ∘ z       ≈˘⟨ identityˡ ⟩
            id ∘ (η ε X ⟨$⟩ id) ∘ z  ≈˘⟨ commute ε z CE.refl ⟩
            η ε x ⟨$⟩ id ∘ id ∘ z    ≈⟨ cong (η ε x) (identityˡ ○ identityˡ ○ z≈y) ⟩
            η ε x ⟨$⟩ y ∎
        }
      }

  YoFaithful : Faithful embed
  YoFaithful _ _ pres-≈ = ⟺ identityʳ ○ pres-≈ {_} {id} CE.refl ○ identityʳ

  YoFullyFaithful : FullyFaithful embed
  YoFullyFaithful = YoFull , YoFaithful
