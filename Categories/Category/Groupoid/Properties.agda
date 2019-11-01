{-# OPTIONS --without-K --safe #-}
open import Categories.Category.Groupoid

module Categories.Category.Groupoid.Properties {o ℓ e} (G : Groupoid o ℓ e) where

import Categories.Morphism as Morphism
import Categories.Morphism.Properties as MorphismProps
import Categories.Morphism.Reasoning as MR

open Groupoid G
open Morphism category
open MorphismProps category
open HomReasoning
open MR category

private
  variable
    A B C : Obj

mono : {f : A ⇒ B} → Mono f
mono = Iso⇒Mono iso

epi : {f : A ⇒ B} → Epi f
epi = Iso⇒Epi iso

id-inverse : id {A = A} ⁻¹ ≈ id
id-inverse = ⟺ identityˡ ○ iso.isoʳ

⁻¹-involutive : {f : A ⇒ B} → f ⁻¹ ⁻¹ ≈ f
⁻¹-involutive {f = f} = begin
  f ⁻¹ ⁻¹            ≈⟨ introʳ iso.isoˡ ⟩
  f ⁻¹ ⁻¹ ∘ f ⁻¹ ∘ f ≈⟨ sym-assoc ○ elimˡ iso.isoˡ ⟩
                   f ∎

⁻¹-commute : {f : A ⇒ B} {g : C ⇒ A} → (f ∘ g) ⁻¹ ≈ g ⁻¹ ∘ f ⁻¹
⁻¹-commute {f = f} {g} = epi _ _ ( begin
  (f ∘ g) ⁻¹ ∘ f ∘ g    ≈⟨ iso.isoˡ ⟩
  id                    ≈˘⟨ iso.isoˡ ⟩
  g ⁻¹ ∘ g              ≈˘⟨ cancelInner iso.isoˡ ⟩
  (g ⁻¹ ∘ f ⁻¹) ∘ f ∘ g ∎ )
