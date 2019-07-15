{-# OPTIONS --without-K --safe #-}
module Categories.Yoneda where

open import Level
open import Function.Inverse using (Inverse)
open import Function.Equality using (_⟨$⟩_)
open import Relation.Binary using (module Setoid)

open import Categories.Category using (Category; _[_,_])
open import Categories.Functor using (Functor)
open import Categories.Functor.Hom using (module Hom; Hom[_][-,_])
open import Categories.Category.Construction.Presheaves
open import Categories.Category.Instance.Setoids
open import Categories.Functor.Presheaf
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.NaturalTransformation.NaturalIsomorphism

private
  variable
    o ℓ e : Level

module _ (C : Category o ℓ e) where
  open Category C

  -- The Yoneda embedding functor
  embed : Functor C (Presheaves C)
  embed = record
    { F₀ = Hom[ C ][-,_]
    ; F₁ = Hom[A,C]⇒Hom[B,C] -- A⇒B induces a NatTrans on the Homs.
    ; identity = identityˡ ○_
    ; homomorphism = λ h₁≈h₂ → ∘-resp-≈ʳ h₁≈h₂ ○ assoc
    ; F-resp-≈ = λ f≈g h≈i → ∘-resp-≈ f≈g h≈i
    }
    where
      open HomReasoning
      -- This NaturalTransformation should probably got into NaturalTransformation.Hom,
      -- in analogy with Functor.Hom above
      Hom[A,C]⇒Hom[B,C] : {A B : Obj} → (A ⇒ B) → NaturalTransformation (Hom.Hom[-, C ] A) (Hom.Hom[-, C ] B)
      Hom[A,C]⇒Hom[B,C] {A} A⇒B = record
        { η = λ X → record { _⟨$⟩_ = λ X⇒A → A⇒B ∘ X⇒A ; cong = ∘-resp-≈ʳ }
        ; commute = λ {X} {Y} f {g} {h} g≈h → begin
            A⇒B ∘ id ∘ g ∘ f ≈˘⟨ assoc ⟩
            (A⇒B ∘ id) ∘ g ∘ f ≈⟨ ∘-resp-≈ id-comm (∘-resp-≈ˡ g≈h) ⟩
            (id ∘ A⇒B) ∘ h ∘ f ≈⟨ assoc ○ ⟺ (∘-resp-≈ʳ assoc) ⟩ -- TODO: MR.Reassociate
            id ∘ (A⇒B ∘ h) ∘ f ∎
        }

  -- Using the adjunction between product and product, we get a kind of contravariant Bifunctor
  yoneda : (a : Obj) (F : Presheaf C (Setoids ℓ e)) →
    Inverse (Category.hom-setoid (Presheaves C) {Functor.F₀ embed a} {F}) (Functor.F₀ F a)
  yoneda a F = record
    { to = record
      { _⟨$⟩_ = λ nat → η nat a ⟨$⟩ id
      ; cong = λ i≈j → i≈j (Category.Equiv.refl C)
      }
    ; from = record
      { _⟨$⟩_ = λ x → record
        { η = λ X → record
          { _⟨$⟩_ = λ X⇒a → F₁ F X⇒a ⟨$⟩ x
          ; cong = λ i≈j → F-resp-≈ F i≈j (Setoid.refl (F₀ F a))
          }
        ; commute = λ Y⇒X y≈z → {!!}
        }
      ; cong = λ i≈j y≈z → F-resp-≈ F y≈z i≈j
      }
    ; inverse-of = record
      { left-inverse-of = λ nat {x} {z} z≈y →
        let module S = Setoid (F₀ F x) in
        S.trans (S.sym (commute nat z (Category.Equiv.refl C)))
                (cong (η nat x) (identityˡ ○ identityˡ ○ z≈y))
      ; right-inverse-of = λ Fa → identity F _
      }
    }
    where
      open HomReasoning
      open Functor
      open NaturalTransformation
      open Function.Equality using (Π; cong)
