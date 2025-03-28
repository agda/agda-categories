{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Functor

open import Level

module Categories.Diagram.End.Instance.NaturalTransformations
  {o ℓ e o′ ℓ′ e′}
  {C : Category o ℓ e}
  {D : Category o′ (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) (o ⊔ e′)}
  (F G : Functor C D)
  where

open import Categories.Category.Construction.Functors
open import Categories.Diagram.End
open import Categories.Diagram.Wedge
open import Categories.Functor.Bifunctor
open import Categories.Functor.Hom
open import Categories.Morphism.Reasoning D
open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.Dinatural

open import Function.Bundles

private
  module C = Category C
  module D = Category D
  module F = Functor F
  module G = Functor G

open Category D
open HomReasoning
open NaturalTransformation
open Wedge

-- For appropriately sized categories, the set of natural
-- transformations from F to G forms the end ∫ₓ F x ⇒ G x
-- This is Theorem 1.4.1 of Coend calculus

naturalTransformations : End (reduce-× Hom[ D ][-,-] F.op G)
naturalTransformations = record
  { wedge = record
    { E = Hom[ Functors C D ][ F , G ]
    ; dinatural = dtHelper record
      { α = λ X → record
        { to = λ nt → η nt X
        ; cong = λ eq → eq
        }
      ; commute = λ {X Y} f {nt} → begin
        G.₁ f ∘ η nt X ∘ F.₁ C.id ≈⟨ refl⟩∘⟨ elimʳ F.identity ⟩
        G.₁ f ∘ η nt X            ≈⟨ sym-commute nt f ⟩
        η nt Y ∘ F.₁ f            ≈⟨ pushˡ (introˡ G.identity) ⟩
        G.₁ C.id ∘ η nt Y ∘ F.₁ f ∎
      }
    }
  ; factor = λ W → record
    { to = λ e → ntHelper record
      { η = λ X → dinatural.α W X ⟨$⟩ e
      ; commute = λ {X Y} f → begin
        (dinatural.α W Y ⟨$⟩ e) ∘ F.₁ f            ≈⟨ pushˡ (introˡ G.identity) ⟩
        G.₁ C.id ∘ (dinatural.α W Y ⟨$⟩ e) ∘ F.₁ f ≈⟨ dinatural.commute W f ⟨
        G.₁ f ∘ (dinatural.α W X ⟨$⟩ e) ∘ F.₁ C.id ≈⟨ refl⟩∘⟨ elimʳ F.identity ⟩
        G.₁ f ∘ (dinatural.α W X ⟨$⟩ e)            ∎
      }
    ; cong = λ eq → Func.cong (dinatural.α W _) eq
    }
  ; universal = Equiv.refl
  ; unique = λ eq → Equiv.sym eq
  }
