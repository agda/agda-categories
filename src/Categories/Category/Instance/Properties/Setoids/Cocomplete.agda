{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Properties.Setoids.Cocomplete where

open import Level using (Level; _⊔_)
open import Data.Product using (Σ; proj₁; proj₂; _,_; Σ-syntax; _×_; -,_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary using (Setoid; Preorder; Rel)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Binary.Indexed.Heterogeneous using (_=[_]⇒_)
open import Relation.Binary.Construct.Closure.SymmetricTransitive as ST using (Plus⇔; minimal)
open Plus⇔
open Func

open import Categories.Category using (Category; _[_,_])
open import Categories.Functor.Core using (Functor)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Cocomplete using (Cocomplete)

import Categories.Category.Construction.Cocones as Coc
import Relation.Binary.Reasoning.Setoid as RS

module _ {o ℓ e} c ℓ′ {J : Category o ℓ e} (F : Functor J (Setoids (o ⊔ c) (o ⊔ ℓ ⊔ c ⊔ ℓ′))) where
  private
    module J    = Category J
    open Functor F
    module F₀ j = Setoid (F₀ j)
    open F₀ using () renaming (_≈_ to _[_≈_])

  vertex-carrier : Set (o ⊔ c)
  vertex-carrier = Σ J.Obj F₀.Carrier

  coc : Rel vertex-carrier (o ⊔ ℓ ⊔ c ⊔ ℓ′)
  coc (X , x) (Y , y) = Σ[ f ∈ J [ X , Y ] ] Y [ (F₁ f ⟨$⟩ x) ≈ y ]

  coc-preorder : Preorder (o ⊔ c) (o ⊔ c) (o ⊔ ℓ ⊔ c ⊔ ℓ′)
  coc-preorder = record
    { Carrier    = vertex-carrier
    ; _≈_        = _≡_
    ; _≲_        = coc
    ; isPreorder = record
      { isEquivalence = ≡.isEquivalence
      ; reflexive     = λ { {j , _} ≡.refl → J.id , identity }
      ; trans         = λ { {a , Sa} {b , Sb} {c , Sc} (f , eq₁) (g , eq₂) →
        let open RS (F₀ c)
        in g J.∘ f , (begin
        F₁ (g J.∘ f) ⟨$⟩ Sa    ≈⟨ homomorphism ⟩
        F₁ g ⟨$⟩ (F₁ f ⟨$⟩ Sa) ≈⟨ cong (F₁ g) eq₁ ⟩
        F₁ g ⟨$⟩ Sb            ≈⟨ eq₂ ⟩
        Sc                     ∎) }
      }
    }

Setoids-Cocomplete : (o ℓ e c ℓ′ : Level) → Cocomplete o ℓ e (Setoids (o ⊔ c) (o ⊔ ℓ ⊔ c ⊔ ℓ′))
Setoids-Cocomplete o ℓ e c ℓ′ {J} F = record
  { initial =
    record
    { ⊥        = record
      { N      = ⇛-Setoid
      ; coapex = record
        { ψ       = λ j → record
          { to = j ,_
          ; cong  = λ i≈k → forth (J.id , Setoid.trans (F₀ _) identity i≈k)
          }
        ; commute = λ {X} {Y} X⇒Y → back (X⇒Y , Setoid.refl (F₀ Y))
        }
      }
    ; ⊥-is-initial = record
      { !        = λ {K} →
        let module K = Cocone K
        in record
        { arr     = record
          { to = to-coapex K
          ; cong  = minimal (coc c ℓ′ F) K.N (to-coapex K) (coapex-cong K)
          }
        ; commute = Setoid.refl K.N
        }
      ; !-unique = λ { {K} f {a , Sa} →
        let module K = Cocone K
            module f = Cocone⇒ f
            open RS K.N
        in begin
          K.ψ a ⟨$⟩ Sa       ≈˘⟨ f.commute ⟩
          f.arr ⟨$⟩ (a , Sa) ∎ }
      }
    }
  }
  where open Functor F
        open Coc F
        module J    = Category J
        module F₀ j = Setoid (F₀ j)
        open F₀ using () renaming (_≈_ to _[_≈_])

        -- this is essentially a symmetric transitive closure of coc
        ⇛-Setoid : Setoid (o ⊔ c) (o ⊔ ℓ ⊔ c ⊔ ℓ′)
        ⇛-Setoid = ST.setoid (coc c ℓ′ F) (Preorder.refl (coc-preorder c ℓ′ F))

        to-coapex : ∀ K → vertex-carrier c ℓ′ F → Setoid.Carrier (Cocone.N K)
        to-coapex K (j , Sj) = K.ψ j ⟨$⟩ Sj
          where module K = Cocone K
        coapex-cong : ∀ K → coc c ℓ′ F =[ to-coapex K ]⇒ (Setoid._≈_ (Cocone.N K))
        coapex-cong K {X , x} {Y , y} (f , fx≈y) = begin
          K.ψ X ⟨$⟩ x            ≈˘⟨ K.commute f ⟩
          K.ψ Y ⟨$⟩ (F₁ f ⟨$⟩ x)  ≈⟨ cong (K.ψ Y) fx≈y ⟩
          K.ψ Y ⟨$⟩ y            ∎
          where module K = Cocone K
                open RS K.N
