{-# OPTIONS --without-K --safe #-}
open import Level
open import Categories.Category using (Category)

module Categories.NaturalTransformation.Hom {o ℓ e : Level} (C : Category o ℓ e) where

open import Categories.Category.Instance.Setoids
open import Categories.Functor.Hom using (module Hom; Hom[_][-,_]; Hom[_][_,-]; Hom[_][-,-])
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper) renaming (id to idN)

import Categories.Morphism.Reasoning as MR

open Category C
open HomReasoning
open MR C
open NaturalTransformation
private
  module CE = Category.Equiv C
  module C = Category C

Hom[A,C]⇒Hom[B,C] : {A B : Obj} → (A ⇒ B) → NaturalTransformation Hom[ C ][-, A ] Hom[ C ][-, B ]
Hom[A,C]⇒Hom[B,C] {A} A⇒B = ntHelper record
  { η       = λ X → record { to = λ X⇒A → A⇒B ∘ X⇒A ; cong = ∘-resp-≈ʳ }
  ; commute = λ f {g} → begin
      A⇒B ∘ id ∘ g ∘ f   ≈⟨ pullˡ id-comm ⟩
      (id ∘ A⇒B) ∘ g ∘ f ≈⟨ pullʳ sym-assoc ⟩
      id ∘ (A⇒B ∘ g) ∘ f ∎
  }

Hom[C,A]⇒Hom[C,B] : {A B : Obj} → (B ⇒ A) → NaturalTransformation Hom[ C ][ A ,-] Hom[ C ][ B ,-]
Hom[C,A]⇒Hom[C,B] {A} B⇒A = ntHelper record
  { η = λ X → record { to = λ A⇒X → A⇒X ∘ B⇒A ; cong = ∘-resp-≈ˡ }
  ; commute = λ f {g} → begin
      (f ∘ g ∘ id) ∘ B⇒A ≈⟨ pullʳ (pullʳ id-comm-sym) ⟩
      f ∘ g ∘ B⇒A ∘ id   ≈⟨ (refl⟩∘⟨ sym-assoc) ⟩
      f ∘ (g ∘ B⇒A) ∘ id ∎
  }
