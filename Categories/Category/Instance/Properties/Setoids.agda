{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Properties.Setoids where

open import Level
open import Relation.Binary using (Setoid; module Setoid; Preorder)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as RS
open import Function.Equality using (Π)
open import Relation.Binary.Indexed.Heterogeneous using (_=[_]⇒_)
open import Data.Product using (Σ; proj₁; proj₂; _,_; Σ-syntax; _×_)
import Relation.Binary.Construct.Symmetrize as Symmetrize
open Symmetrize hiding (setoid; trans; sym)
open import Data.Unit using (⊤; tt)

open import Categories.Category using (Category; _[_,_])
open import Categories.Functor
open import Categories.Category.Instance.Setoids
open import Categories.Diagram.Cocone
open import Categories.Category.Construction.Cocones hiding (Cocone)
open import Categories.Diagram.Cone
open import Categories.Category.Complete
open import Categories.Category.Cocomplete

Setoids-Cocomplete : (o ℓ e c ℓ′ : Level) → Cocomplete o ℓ e (Setoids (o ⊔ c) (o ⊔ ℓ ⊔ c ⊔ ℓ′))
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


Setoids-Complete : (o ℓ e c ℓ′ : Level) → Complete o ℓ e (Setoids (ℓ′ ⊔ ℓ ⊔ o) (o ⊔ ℓ′))
Setoids-Complete o ℓ e c ℓ′ {J} F = record { terminal = record
  { ⊤ = record
    { N = record
      { Carrier = Σ
          ((j : Category.Obj J) → Setoid.Carrier (F₀ j))
          (λ P → ∀ {X Y} (f : J [ X , Y ]) → Setoid._≈_ (F₀ Y) (F₁ f Π.⟨$⟩ P X) (P Y))
      ; _≈_ = λ f g → ∀ (j : Category.Obj J) → Setoid._≈_ (F₀ j) (proj₁ f j) (proj₁ g j)
      ; isEquivalence = record
        { refl = λ j → Setoid.refl (F₀ j)
        ; sym = λ a≈b j → Setoid.sym (F₀ j) (a≈b j)
        ; trans = λ a≈b b≈c j → Setoid.trans (F₀ j) (a≈b j) (b≈c j)
        }
      }
    ;  apex = record
      { ψ = λ j → record
        { _⟨$⟩_ = λ x → proj₁ x j
        ; cong = λ x → x j
        }
      ; commute = λ {X} {Y} X⇒Y {x} {y} f≈g → Setoid.trans (F₀ Y) (proj₂ x X⇒Y) (f≈g Y)
      }
    }
  ; ! = λ {A} → record
    { arr = record
      { _⟨$⟩_ = λ x → (λ j → ψ A j Π.⟨$⟩ x) , λ {X} {Y} f → commute A f (Setoid.refl (N A))
      ; cong = λ a≈b j → Π.cong (ψ A j) a≈b
      }
    ; commute = λ {j} x≈y → Π.cong (ψ A j) x≈y
    }
  ; !-unique = λ {A} f x≈y j → Setoid.sym (F₀ j) (Cone⇒.commute f (Setoid.sym (N A) x≈y))
  } }
  where
    open Functor F
    S : Category (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
    S = Setoids c ℓ
    open Category S
    open Cone
