{-# OPTIONS --without-K --safe #-}
open import Level
open import Categories.Category using (Category)

module Categories.NaturalTransformation.Hom {o ℓ e : Level} (C : Category o ℓ e) where

-- open import Function using (_$_; Inverse) -- else there's a conflict with the import below
-- open import Function.Equality using (Π; _⟨$⟩_; cong)
-- open import Relation.Binary using (module Setoid)
-- import Relation.Binary.Reasoning.Setoid as SetoidR
-- open import Data.Product using (_,_; Σ)

-- open import Categories.Category.Product
-- open import Categories.Category.Construction.Presheaves
-- open import Categories.Category.Construction.Functors
open import Categories.Category.Instance.Setoids
-- open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Hom using (module Hom; Hom[_][-,_]; Hom[_][-,-])
-- open import Categories.Functor.Bifunctor
-- open import Categories.Functor.Presheaf
-- open import Categories.Functor.Construction.LiftSetoids
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper) renaming (id to idN)
-- open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)

-- import Categories.Morphism as Mor
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
  { η       = λ X → record { _⟨$⟩_ = λ X⇒A → A⇒B ∘ X⇒A ; cong = ∘-resp-≈ʳ }
  ; commute = λ f {g} {h} g≈h → begin
      A⇒B ∘ id ∘ g ∘ f   ≈⟨ sym-assoc ⟩
      (A⇒B ∘ id) ∘ g ∘ f ≈⟨ id-comm ⟩∘⟨ g≈h ⟩∘⟨refl ⟩
      (id ∘ A⇒B) ∘ h ∘ f ≈⟨ assoc ○ ⟺ (∘-resp-≈ʳ assoc) ⟩ -- TODO: MR.Reassociate
      id ∘ (A⇒B ∘ h) ∘ f ∎
  }
