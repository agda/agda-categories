{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Properties.Setoids where

open import Level
open import Relation.Binary using (Setoid; module Setoid; Preorder)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as RS
open import Function.Equality using (Π)
open import Relation.Binary.Indexed.Heterogeneous using (_=[_]⇒_)
open import Data.Product using (Σ; proj₁; proj₂; _,_; Σ-syntax)
import Relation.Binary.Construct.Symmetrize as Symmetrize
open Symmetrize hiding (setoid)

open import Categories.Category using (Category; _[_,_])
open import Categories.Functor
open import Categories.Category.Instance.Setoids
open import Categories.Diagram.Cocone
open import Categories.Category.Complete
open import Categories.Category.Cocomplete

Setoids-Cocomplete : (o ℓ e c ℓ′ : Level) → Cocomplete o ℓ e (Setoids _ _)
Setoids-Cocomplete o ℓ e c ℓ′ {J} F = record { initial = record
  { ⊥ = record
    { N = ⇛-Setoid
    ; coapex = record
      { ψ = λ j → record
        { _⟨$⟩_ = j ,_
        ; cong = λ i≈k → disorient (slish (J.id , identity i≈k))
        }
      ; commute = λ {X} X⇒Y x≈y → disorient (slash (X⇒Y , cong (F₁ X⇒Y) (Setoid.sym (F₀ X) x≈y)))
      }
    }
  ; ! = λ {A} → record
    { arr = record
      { _⟨$⟩_ = to-coapex A
      ; cong = λ eq → minimal ⇛-preorder (Cocone.N A) (to-coapex A) (coapex-cong A) eq
      }
    ; commute = λ {X} x≈y → cong (Coapex.ψ (Cocone.coapex A) X) x≈y
    }
  ; !-unique = λ {A} cocone⇒ x⇛y → Setoid.trans (Cocone.N A)
               (Setoid.sym (Cocone.N A) (Cocone⇒.commute cocone⇒ (refl (F₀ _))))
               (cong (Cocone⇒.arr cocone⇒) x⇛y)
  } }
  where
    open Setoid
    open Π
    open Functor F
    D = Cocones F
    module J = Category J
    C = Setoids _ _
    setoid : J.Obj → Category.Obj C
    setoid j = F₀ j
    module S (j : J.Obj) = Setoid (setoid j)
    open S using () renaming (_≈_ to _[_≈_])
    vertex-carrier = Σ[ j ∈ J.Obj ] Carrier (setoid j)
    _⇛_ : (x y : vertex-carrier) → Set _
    (X , x) ⇛ (Y , y) = Σ[ f ∈ J [ X , Y ] ] ( Y [ (F₁ f ⟨$⟩ x) ≈ y ])
    ⇛-preorder : Preorder _ _ _
    ⇛-preorder = record
      { Carrier = vertex-carrier
      ; _≈_ = _≡_
      ; _∼_ = _⇛_
      ; isPreorder = record
        { isEquivalence = ≡.isEquivalence
        ; reflexive = λ { {i , Fi} {.i , .Fi} ≡.refl → J.id , Functor.identity F (refl (F₀ i))}
        ; trans = λ { {i , Fi} {j , Fj} {k , Fk} i≈j j≈k → proj₁ j≈k J.∘ proj₁ i≈j ,
          let S = F₀ k in
          let open RS S in begin
          F₁ (proj₁ j≈k J.∘ proj₁ i≈j) ⟨$⟩ Fi       ≈⟨ homomorphism (refl (F₀ i)) ⟩
          F₁ (proj₁ j≈k) ⟨$⟩ (F₁ (proj₁ i≈j) ⟨$⟩ Fi) ≈⟨ cong (F₁ (proj₁ j≈k)) (proj₂ i≈j)  ⟩
          F₁ (proj₁ j≈k) ⟨$⟩ Fj                     ≈⟨ proj₂ j≈k ⟩
          Fk ∎}
        }
      }
    ⇛-Setoid : Setoid (o ⊔ c) (o ⊔ ℓ ⊔ c ⊔ ℓ′)
    ⇛-Setoid = Symmetrize.setoid ⇛-preorder
    to-coapex : (A : Cocone F) → vertex-carrier → Carrier (Cocone.N A)
    to-coapex A (j , Fj) = Cocone.ψ A j ⟨$⟩ Fj
    coapex-cong : (A : Cocone F) → _⇛_ =[ to-coapex A ]⇒ (_≈_ (Cocone.N A))
    coapex-cong A {X , x} {Y , y} (f , fx≈y) = Setoid.trans A.N
        (Setoid.sym A.N (A.commute f (refl (F₀ X))))
        (cong (A.ψ Y) fx≈y)
      where module A = Cocone A

{-
Setoids-Complete : (o ℓ e c ℓ′ : Level) → Complete o ℓ e (Setoids _ _)
Setoids-Complete o ℓ e c ℓ′ {J} F = record { terminal = record
  { ⊤ = record
    { apex = record
      { ψ = λ j → record
        { _⟨$⟩_ = λ f → proj₁ f j
        ; cong = λ eq → eq j
        }
      ; commute = λ {X} {Y} h {f} {g} f≈g → let open Setoid (F₀ Y) in trans (f≈g X) (sym (proj₂ g h))
      }
    }
  ; ! = λ {A} → record
    { arr = record
      { _⟨$⟩_ = λ c → {!!} , {!!}
      ; cong = {!!}
      }
    ; commute = {!!}
    }
  ; !-unique = {!!}
  } }
  where
    open Functor F
-}
