{-# OPTIONS --without-K --safe #-}

module Categories.Diagram.Coend.Properties where

open import Categories.Category.Core using (Category)
open import Categories.Category.Product
import Categories.Category.Construction.Cowedges as Cowedges
open import Categories.Category.Construction.Functors
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Diagram.Coend
open import Categories.Diagram.Cowedge
open import Categories.NaturalTransformation hiding (id)
open import Categories.NaturalTransformation.Dinatural
open import Categories.Object.Initial

import Categories.Morphism.Reasoning as MR

open import Level
open import Data.Product using (Σ; _,_)
open import Function using (_$_)

module _ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′}
  (F : Bifunctor (Category.op C) C D) where
  open Cowedges F

  -- Being a Coend is the same as being an Initial object in the category of Cowedges
  Coend⇒Initial : Coend F → Initial Cowedges
  Coend⇒Initial c = record
    { ⊥ = cowedge
    ; ⊥-is-initial = record
      { ! = λ {A} → record { u = factor A ; commute = universal }
      ; !-unique = λ {A} f → unique {A} (Cowedge-Morphism.commute f)
      }
    }
    where
    open Coend c

  Initial⇒Coend : Initial Cowedges → Coend F
  Initial⇒Coend i = record
    { cowedge = ⊥
    ; factor = λ W → u {W₂ = W} !
    ; universal = commute !
    ; unique = λ {_} {g} x → !-unique (record { u = g ; commute = x })
    }
    where
    open Initial i
    open Cowedge-Morphism

private
  variable
    o ℓ e : Level
    C D E : Category o ℓ e

module _ (F : Functor E (Functors (Product (Category.op C) C) D)) where
  private
    module C = Category C
    module D = Category D
    module E = Category E
    module NT = NaturalTransformation
  open D
  open HomReasoning

  open MR D
  open Functor F
  open Coend hiding (E)
  open NT using (η)

  CoendF : (∀ X → Coend (F₀ X)) → Functor E D
  CoendF coend = record
    { F₀           = λ X → Coend.E (coend X)
    ; F₁           = F₁′
    ; identity     = λ {A} → unique (coend A) (id-comm-sym ○ ∘-resp-≈ʳ (⟺ identity))
    ; homomorphism = λ {A B C} {f g} → unique (coend A) $ λ {Z} → begin
      (F₁′ g ∘ F₁′ f) ∘ dinatural.α (coend A) Z                         ≈⟨  pullʳ (universal (coend A)) ⟩
      (F₁′ g ∘ (dinatural.α (coend B) Z ∘ η (F₁ f) (Z , Z) )  )         ≈⟨ pullˡ (universal (coend B))  ⟩
      ((dinatural.α (coend C) Z ∘ η (F₁ g) (Z , Z)) ∘ η (F₁ f) (Z , Z)) ≈˘⟨ pushʳ homomorphism ⟩
      dinatural.α (coend C) Z ∘ η (F₁ (g E.∘ f)) (Z , Z)                ∎
    ; F-resp-≈     = λ {A B f g} eq → unique (coend A) $ λ {Z} → begin
      F₁′ g ∘ dinatural.α (coend A) Z                               ≈⟨ universal (coend A) ⟩
      dinatural.α (coend B) Z ∘ η (F₁ g) (Z , Z)                   ≈˘⟨ refl⟩∘⟨ F-resp-≈ eq ⟩
      dinatural.α (coend B) Z ∘ η (F₁ f) (Z , Z)                   ∎
    }
    where F₁′ : ∀ {X Y} → X E.⇒ Y → Coend.E (coend X) ⇒ Coend.E (coend Y)
          F₁′ {X} {Y} f = factor (coend X) $ record
            { E         = Coend.E (coend Y)
            ; dinatural = dinatural (coend Y) ∘> F₁ f
            }

-- A Natural Transformation between two functors induces an arrow between the
-- (object part of) the respective coends.
module _ {P Q : Functor (Product (Category.op C) C) D} (P⇒Q : NaturalTransformation P Q) where
  open Coend renaming (E to coend)
  open Category D

  coend-η : {cp : Coend P} {cq : Coend Q} → coend cp ⇒ coend cq
  coend-η {cp} {cq} = factor cp ((record
    { E = Coend.E cq
    ; dinatural = dtHelper record
      { α = λ c →  dinatural.α cq c ∘ η (c , c)
      ; commute = λ {C} {C′} f → begin
        id ∘ (αq C ∘ η (C , C)) ∘ P.₁ (f , C.id)    ≈⟨ pushʳ assoc ⟩
        (id ∘ αq C) ∘ (η (C , C) ∘ P.₁ (f , C.id))  ≈⟨ refl⟩∘⟨ nt.commute (f , C.id) ⟩
        (id ∘ αq C) ∘ (Q.₁ (f , C.id) ∘ η (C′ , C)) ≈⟨ pullˡ assoc ⟩
        (id ∘ αq C ∘ Q.₁ (f , C.id)) ∘ η (C′ , C)   ≈⟨ αq-comm f ⟩∘⟨refl ⟩
        (id ∘ αq C′ ∘ Q.₁ (C.id , f)) ∘ η (C′ , C)  ≈⟨ pushˡ sym-assoc ⟩
        (id ∘ αq C′) ∘ Q.₁ (C.id , f) ∘ η (C′ , C)  ≈⟨ refl⟩∘⟨ nt.sym-commute (C.id , f) ⟩
        (id ∘ αq C′) ∘ η (C′ , C′) ∘ P.₁ (C.id , f) ≈⟨ pullʳ sym-assoc ⟩
        id ∘ (αq C′ ∘ η (C′ , C′)) ∘ P.₁ (C.id , f) ∎
      }
    }))
    where
    module nt = NaturalTransformation P⇒Q
    open nt using (η)
    open HomReasoning
    module C = Category C
    module P = Functor P
    module Q = Functor Q
    open DinaturalTransformation (dinatural cp) renaming (α to αp; commute to αp-comm)
    open DinaturalTransformation (dinatural cq) renaming (α to αq; commute to αq-comm)
    open Cowedge
    open MR D
