{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Diagram.Colimit.Properties
  {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {J : Category o′ ℓ′ e′}  where

private
    module C = Category C
    open C
    open HomReasoning

open import Categories.Category.Construction.Arrow J using (Morphism; mor)
open import Categories.Diagram.Coequalizer C using (Coequalizer)
open import Categories.Diagram.Cocone using (Coapex; Cocone; Cocone⇒)
open import Categories.Diagram.Colimit using (Colimit)
open import Categories.Diagram.Duality C using (Coapex⇒coApex; Colimit⇒coLimit)
open import Categories.Diagram.Limit using (Limit; ψ-≈⇒rep-≈)
open import Categories.Functor using (Functor)
open import Categories.Morphism.Reasoning C using (pullˡ; pullʳ; pushˡ; pushʳ)
open import Categories.Object.Coproduct.Indexed C using (IndexedCoproductOf)

module _ (F : Functor J C) (X : Obj) (coapex₁ : Coapex F X) (coapex₂ : Coapex F X) (L : Colimit F) where
  private
    module F = Functor F
    module coapex₁ = Coapex coapex₁
    module coapex₂ = Coapex coapex₂
    module L = Colimit L

    K₁ : Cocone F
    K₁ = record { coapex = coapex₁ }
    module K₁ = Cocone K₁

    K₂ : Cocone F
    K₂ = record { coapex = coapex₂ }
    module K₂ = Cocone K₂

  coψ-≈⇒rep-≈ : (∀ A → coapex₁.ψ A ≈ coapex₂.ψ A) → L.rep K₁ ≈ L.rep K₂
  coψ-≈⇒rep-≈ = ψ-≈⇒rep-≈ F.op X (Coapex⇒coApex X coapex₁) (Coapex⇒coApex X coapex₂) (Colimit⇒coLimit L)

-- existence theorem
module _ {F : Functor J C} {OP : IndexedCoproductOf (Functor.₀ F)} {MP : IndexedCoproductOf λ f → Functor.₀ F (Morphism.dom f)} where

  private
    module F = Functor F
    module OP = IndexedCoproductOf OP
    module MP = IndexedCoproductOf MP

    s t : MP.X ⇒ OP.X
    s = MP.[ (λ f → OP.ι (Morphism.cod f) ∘ F.₁ (Morphism.arr f)) ]
    t = MP.[ (λ f → OP.ι (Morphism.dom f)) ]

  build-colim : Coequalizer s t → Colimit F
  build-colim eq = record
    { initial = record
      { ⊥ = record
        { N = obj
        ; coapex = record
          { ψ = λ X → arr ∘ OP.ι X
          ; commute = λ {X} {Y} f → begin
            (arr ∘ OP.ι Y) ∘ F.₁ f   ≈⟨ pushʳ MP.commute ⟨
            arr ∘ (s ∘ MP.ι (mor f)) ≈⟨ pullˡ equality ⟩
            (arr ∘ t) ∘ MP.ι (mor f) ≈⟨ pullʳ MP.commute ⟩
            arr ∘ OP.ι X             ∎
          }
        }
      ; ⊥-is-initial = record
        { ! = λ {A} → record
          { arr = coequalize (bang-lemma A)
          ; commute = ⟺ (pushˡ universal) ○ OP.commute
          }
        ; !-unique = λ f → Equiv.sym (unique (OP.unique (assoc ○ Cocone⇒.commute f)))
        }
      }
    }
    where
      open Coequalizer eq
      abstract
        bang-lemma : (A : Cocone F) → OP.[ Cocone.ψ A ] ∘ s ≈ OP.[ Cocone.ψ A ] ∘ t
        bang-lemma A = begin
          OP.[ Cocone.ψ A ] ∘ s                                                             ≈⟨ MP.∘[] (λ f → OP.ι (Morphism.cod f) ∘ F.₁ (Morphism.arr f)) OP.[ Cocone.ψ A ] ⟩
          MP.[ (λ f → OP.[ Cocone.ψ A ] ∘ (OP.ι (Morphism.cod f) ∘ F.₁ (Morphism.arr f))) ] ≈⟨ MP.[]-cong (pullˡ OP.commute) ⟩
          MP.[ (λ f → Cocone.ψ A (Morphism.cod f) ∘ F.₁ (Morphism.arr f)) ]                 ≈⟨ MP.[]-cong (Cocone.commute A _) ⟩
          MP.[ (λ f → Cocone.ψ A (Morphism.dom f)) ]                                        ≈⟨ MP.[]-cong OP.commute ⟨
          MP.[ (λ f → OP.[ Cocone.ψ A ] ∘ OP.ι (Morphism.dom f)) ]                          ≈⟨ MP.∘[] (λ f → OP.ι (Morphism.dom f)) OP.[ Cocone.ψ A ] ⟨
          OP.[ Cocone.ψ A ] ∘ t                                                             ∎
