{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Complete.Properties.Construction {o ℓ e} (C : Category o ℓ e) where

open import Level
open import Data.Product using (∃₂; _,_; -,_)

open import Categories.Category.Complete
open import Categories.Diagram.Equalizer C
open import Categories.Diagram.Limit as Lim
open import Categories.Object.Product.Indexed C
open import Categories.Functor

import Categories.Category.Construction.Cones as Co
import Categories.Morphism.Reasoning as MR

private
  variable
    o′ ℓ′ e′ o″ ℓ″ e″ : Level
  module C = Category C

module _ (prods : AllProductsOf (o′ ⊔ ℓ′)) (equalizer : ∀ {A B} (f g : A C.⇒ B) → Equalizer f g) where
  private
    module Prods {I} (P : I → C.Obj) = IndexedProductOf (prods P)
    open C.HomReasoning

    module _ {J : Category o′ ℓ′ e′} (F : Functor J C) where
      private
        module J  = Category J
        open Functor F
        open MR C
        module OP = Prods {Lift ℓ′ J.Obj} (λ j → F₀ (lower j))
        module MP = Prods {∃₂ J._⇒_} (λ { (_ , B , _) → F₀ B })

      src : C.Obj
      src = OP.X

      dst : C.Obj
      dst = MP.X

      ϕ⇒ : (i : ∃₂ J._⇒_) → let (_ , B , _) = i in src C.⇒ F₀ B
      ϕ⇒ (_ , B , _) = OP.π (lift B)

      ϕ : src C.⇒ dst
      ϕ = MP.⟨ ϕ⇒ ⟩

      ψ⇒ : (i : ∃₂ J._⇒_) → let (_ , B , _) = i in src C.⇒ F₀ B
      ψ⇒ (A , B , f) = F₁ f C.∘ OP.π (lift A)

      ψ : src C.⇒ dst
      ψ = MP.⟨ ψ⇒ ⟩

      module eq = Equalizer (equalizer ϕ ψ)

      ⊤ : Co.Cone F
      ⊤ = record
        { N    = eq.obj
        ; apex = record
          { ψ       = λ X → OP.π (lift X) C.∘ eq.arr
          ; commute = λ {X Y} f → begin
            F₁ f C.∘ OP.π (lift X) C.∘ eq.arr ≈˘⟨ pushˡ (MP.commute ψ⇒ _) ⟩
            (MP.π (-, -, f) C.∘ ψ) C.∘ eq.arr ≈˘⟨ pushʳ eq.equality ⟩
            MP.π (-, -, f) C.∘ ϕ C.∘ eq.arr   ≈⟨ pullˡ (MP.commute ϕ⇒ _ ) ⟩
            OP.π (lift Y) C.∘ eq.arr          ∎
          }
        }

      module _ {K : Co.Cone F} where
        private
          module K = Co.Cone F K

        K⇒ : K.N C.⇒ src
        K⇒ = OP.⟨ (λ j → K.ψ (lower j)) ⟩

        Keq : (i : ∃₂ J._⇒_) → ϕ⇒ i C.∘ K⇒ C.≈ ψ⇒ i C.∘ K⇒
        Keq i@(A , B , f) = begin
          ϕ⇒ i C.∘ K⇒    ≈⟨ OP.commute _ _ ⟩
          K.ψ B          ≈˘⟨ K.commute _ ⟩
          F₁ f C.∘ K.ψ A ≈˘⟨ pullʳ (OP.commute _ _) ⟩
          ψ⇒ i C.∘ K⇒    ∎

        !-eq : ϕ C.∘ K⇒ C.≈ ψ C.∘ K⇒
        !-eq = begin
          ϕ C.∘ K⇒                   ≈⟨ MP.⟨⟩∘ _ _ ⟩
          MP.⟨ (λ i → ϕ⇒ i C.∘ K⇒) ⟩ ≈⟨ MP.⟨⟩-cong _ _ Keq ⟩
          MP.⟨ (λ i → ψ⇒ i C.∘ K⇒) ⟩ ≈˘⟨ MP.⟨⟩∘ _ _ ⟩
          ψ C.∘ K⇒                   ∎

        ! : Co.Cones F [ K , ⊤ ]
        ! = record
          { arr     = eq.equalize {h = K⇒} !-eq
          ; commute = λ {j} → begin
            (OP.π (lift j) C.∘ eq.arr) C.∘ eq.equalize !-eq ≈˘⟨ pushʳ eq.universal ⟩
            OP.π (lift j) C.∘ K⇒                            ≈⟨ OP.commute _ _ ⟩
            K.ψ j                                           ∎
          }

        !-unique : (f : Co.Cones F [ K , ⊤ ]) → Co.Cones F [ ! ≈ f ]
        !-unique f = ⟺ (eq.unique eq)
          where module f = Co.Cone⇒ F f
                eq : K⇒ C.≈ eq.arr C.∘ f.arr
                eq = OP.unique′ _ _ λ i → begin
                  OP.π i C.∘ K⇒                 ≈⟨ OP.commute _ _ ⟩
                  K.ψ (lower i)                 ≈˘⟨ f.commute ⟩
                  (OP.π i C.∘ eq.arr) C.∘ f.arr ≈⟨ C.assoc ⟩
                  OP.π i C.∘ eq.arr C.∘ f.arr   ∎

      complete : Limit F
      complete = record
        { terminal = record
          { ⊤        = ⊤
          ; ⊤-is-terminal = record
            { !        = !
            ; !-unique = !-unique
            }
          }
        }

  AllProducts×Equalizer⇒Complete : Complete o′ ℓ′ e′ C
  AllProducts×Equalizer⇒Complete = complete
