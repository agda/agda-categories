{-# OPTIONS --without-K --safe #-}

module Categories.Diagram.End.Properties where

open import Level
open import Data.Product using (Σ; _,_)
open import Function using (_$_)

open import Categories.Category
open import Categories.Category.Product
open import Categories.Category.Construction.Functors
open import Categories.Functor
open import Categories.Functor.Bifunctor
open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.Dinatural
open import Categories.Diagram.End as ∫

import Categories.Category.Construction.Wedges as Wedges
open import Categories.Object.Terminal

import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level
    C D E : Category o ℓ e

module _ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′}
  (F : Bifunctor (Category.op C) C D) where
  open Wedges F

  -- Being an End is the same as being a Terminal object in the category of Wedges
  End⇒Terminal : End F → Terminal Wedges
  End⇒Terminal c =  record
    { ⊤ = wedge
    ; ⊤-is-terminal = record
      { ! = λ {A} → record { u = factor A ; commute = universal }
      ; !-unique = λ {A} f → unique {A} (Wedge-Morphism.commute f)
      }
    }
    where
    open End c

  Terminal⇒Coend : Terminal Wedges → End F
  Terminal⇒Coend i = record
    { wedge = ⊤
    ; factor = λ W → u {W₁ = W} !
    ; universal = commute !
    ; unique = λ {_} {g} x → !-unique (record { u = g ; commute = x })
    }
    where
    open Terminal i
    open Wedge-Morphism

module _ {C : Category o ℓ e}
         (F : Functor E (Functors (Product (Category.op C) C) D)) where
  private
    module C = Category C
    module D = Category D
    module E = Category E
    module NT = NaturalTransformation
  open D
  open HomReasoning

  open MR D
  open Functor F
  open End hiding (E)
  open NT using (η)

  EndF : (∀ X → End (F₀ X)) → Functor E D
  EndF end = record
    { F₀           = λ X → End.E (end X)
    ; F₁           = F₁′
    ; identity     = λ {A} → unique (end A) (id-comm ○ ∘-resp-≈ˡ (⟺ identity))
    ; homomorphism = λ {A B C} {f g} → unique (end C) $ λ {Z} → begin
      dinatural.α (end C) Z ∘ F₁′ g ∘ F₁′ f                       ≈⟨ pullˡ (universal (end C)) ⟩
      (η (F₁ g) (Z , Z) ∘ dinatural.α (end B) Z) ∘ F₁′ f          ≈⟨ pullʳ (universal (end B)) ⟩
      η (F₁ g) (Z , Z) ∘ η (F₁ f) (Z , Z) ∘ dinatural.α (end A) Z ≈˘⟨ pushˡ homomorphism ⟩
      η (F₁ (g E.∘ f)) (Z , Z) ∘ dinatural.α (end A) Z            ∎
    ; F-resp-≈     = λ {A B f g} eq → unique (end B) $ λ {Z} → begin
      dinatural.α (end B) Z ∘ F₁′ g                               ≈⟨ universal (end B) ⟩
      η (F₁ g) (Z , Z) ∘ dinatural.α (end A) Z                    ≈˘⟨ F-resp-≈ eq ⟩∘⟨refl ⟩
      η (F₁ f) (Z , Z) ∘ dinatural.α (end A) Z                    ∎
    }
    where F₁′ : ∀ {X Y} → X E.⇒ Y → End.E (end X) ⇒ End.E (end Y)
          F₁′ {X} {Y} f = factor (end Y) $ record
            { E         = End.E (end X)
            ; dinatural = F₁ f <∘ dinatural (end X)
            }

-- A Natural Transformation between two functors induces an arrow between the
-- (object part of) the respective ends.
module _ {P Q : Functor (Product (Category.op C) C) D} (P⇒Q : NaturalTransformation P Q) where
  open End renaming (E to end)
  open Category D

  end-η : {ep : End P} {eq : End Q} → end ep ⇒ end eq
  end-η {ep} {eq} = factor eq (record
    { E = End.E ep
    ; dinatural = dtHelper record
      { α = λ c → η (c , c) ∘ dinatural.α ep c
      ; commute = λ {C} {C′} f → begin
        Q.₁ (C.id , f) ∘ (η (C , C) ∘ αp C) ∘ D.id       ≈⟨ pullˡ sym-assoc ⟩
        ((Q.₁ (C.id , f) ∘ η (C , C)) ∘ αp C) ∘ D.id     ≈⟨ (nt.sym-commute (C.id , f) ⟩∘⟨refl ⟩∘⟨refl) ⟩
        ((η (C , C′) ∘ P.₁ (C.id , f)) ∘ αp C) ∘ D.id    ≈⟨ assoc² ⟩
        η (C , C′) ∘ (P.₁ (C.id , f) ∘ αp C ∘ D.id)      ≈⟨ (refl⟩∘⟨ αp-comm f) ⟩
        η (C , C′) ∘ P.₁ (f , C.id) ∘ αp C′ ∘ D.id       ≈˘⟨ assoc² ⟩
        ((η (C , C′) ∘ P.₁ (f , C.id)) ∘ αp C′) ∘ D.id   ≈⟨ (nt.commute (f , C.id) ⟩∘⟨refl ⟩∘⟨refl) ⟩
        ((Q.₁ (f , C.id) ∘ η (C′ , C′)) ∘ αp C′) ∘ D.id  ≈⟨ pushˡ assoc ⟩
        Q.₁ (f , C.id) ∘ (η (C′ , C′) ∘ αp C′) ∘ D.id    ∎
      }
    })
    where
    module nt = NaturalTransformation P⇒Q
    open nt using (η)
    open HomReasoning
    module C = Category C
    module D = Category D
    module P = Functor P
    module Q = Functor Q
    open DinaturalTransformation (dinatural ep) renaming (α to αp; commute to αp-comm)
    open DinaturalTransformation (dinatural eq) renaming (α to αq; commute to αq-comm)
    open Wedge
    open MR D
