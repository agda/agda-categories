{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Functor using (Functor)

open import Level

module Categories.Diagram.End.Instance.NaturalTransformations
  {o ℓ e o′ ℓ′ e′}
  {C : Category o ℓ e}
  {D : Category o′ (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) (o ⊔ e′)}
  (F G : Functor C D)
  where

open import Categories.Category.Construction.Functors using (Functors)
open import Categories.Diagram.End using (End)
open import Categories.Diagram.Wedge using (Wedge)
open import Categories.Functor.Bifunctor using (reduce-×)
open import Categories.Functor.Hom using (Hom[_][-,-]; Hom[_][_,_])
open import Categories.Morphism.Reasoning D
open import Categories.NaturalTransformation using (NaturalTransformation)

open import Function.Bundles using (Func; _⟨$⟩_)

private
  module F = Functor F
  module G = Functor G

open Category C using (id)
open Category D hiding (id)
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
    ; dinatural = record
      { α = λ X → record
        { to = λ nt → η nt X
        ; cong = λ eq → eq
        }
      ; commute = λ {X Y} f {nt} → begin
        G.₁ f ∘ η nt X ∘ F.₁ id ≈⟨ refl⟩∘⟨ elimʳ F.identity ⟩
        G.₁ f ∘ η nt X          ≈⟨ sym-commute nt f ⟩
        η nt Y ∘ F.₁ f          ≈⟨ pushˡ (introˡ G.identity) ⟩
        G.₁ id ∘ η nt Y ∘ F.₁ f ∎
      ; op-commute = λ {X Y} f {nt} → begin
        G.₁ id ∘ η nt Y ∘ F.₁ f ≈⟨ pullˡ (elimˡ G.identity) ⟩
        η nt Y ∘ F.₁ f          ≈⟨ commute nt f ⟩
        G.₁ f ∘ η nt X          ≈⟨ refl⟩∘⟨ introʳ F.identity ⟩
        G.₁ f ∘ η nt X ∘ F.₁ id ∎
      }
    }
  ; factor = λ W → record
    { to = λ e → record
      { η = λ X → dinatural.α W X ⟨$⟩ e
      ; commute = λ {X Y} f → begin
        (dinatural.α W Y ⟨$⟩ e) ∘ F.₁ f          ≈⟨ pushˡ (introˡ G.identity) ⟩
        G.₁ id ∘ (dinatural.α W Y ⟨$⟩ e) ∘ F.₁ f ≈⟨ dinatural.op-commute W f ⟩
        G.₁ f ∘ (dinatural.α W X ⟨$⟩ e) ∘ F.₁ id ≈⟨ refl⟩∘⟨ elimʳ F.identity ⟩
        G.₁ f ∘ (dinatural.α W X ⟨$⟩ e)          ∎
      ; sym-commute = λ {X Y} f → begin
        G.₁ f ∘ (dinatural.α W X ⟨$⟩ e)          ≈⟨ refl⟩∘⟨ introʳ F.identity ⟩
        G.₁ f ∘ (dinatural.α W X ⟨$⟩ e) ∘ F.₁ id ≈⟨ dinatural.commute W f ⟩
        G.₁ id ∘ (dinatural.α W Y ⟨$⟩ e) ∘ F.₁ f ≈⟨ pullˡ (elimˡ G.identity) ⟩
        (dinatural.α W Y ⟨$⟩ e) ∘ F.₁ f          ∎
      }
    ; cong = λ eq → Func.cong (dinatural.α W _) eq
    }
  ; universal = Equiv.refl
  ; unique = λ eq → Equiv.sym eq
  }
