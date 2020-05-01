{-# OPTIONS --without-K --safe #-}

module Categories.Category.Construction.Properties.Presheaves.CartesianClosed where

open import Level
open import Data.Unit
open import Data.Product using (_,_; proj₁; proj₂)
open import Function.Equality using (Π) renaming (_∘_ to _∙_)
open import Relation.Binary

open import Categories.Category.Core using (Category)
open import Categories.Category.CartesianClosed
open import Categories.Category.CartesianClosed.Canonical renaming (CartesianClosed to CCartesianClosed)
open import Categories.Category.Construction.Presheaves
open import Categories.Category.Instance.Setoids
open import Categories.Functor
open import Categories.Functor.Hom
open import Categories.Functor.Properties
open import Categories.Functor.Presheaf
open import Categories.NaturalTransformation

import Categories.Category.Construction.Properties.Presheaves.Cartesian as Preₚ
import Categories.Morphism.Reasoning as MR
import Relation.Binary.Reasoning.Setoid as SetoidR

open Π using (_⟨$⟩_)

module HasClosed {o ℓ e} (C : Category o ℓ e) where
  private
    module C = Category C
    open C

  module _ (F G : Presheaf C (Setoids ℓ e)) where
    private
      module F = Functor F
      module G = Functor G
      open Preₚ C
      open IsCartesian o o

    Presheaf^ : Presheaf C (Setoids (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e))
    Presheaf^ = record
      { F₀           = λ X → Hom[ Presheaves C ][ Presheaves× Hom[ C ][-, X ] G , F ]
      ; F₁           = λ {A B} f → record
        { _⟨$⟩_ = λ α →
          let module α = NaturalTransformation α using (η; commute)
          in ntHelper record
          { η       = λ X → record
            { _⟨$⟩_ = λ where (g , S) → α.η X ⟨$⟩ (f ∘ g , S)
            ; cong  = λ where (eq₁ , eq₂) → Π.cong (α.η X) (∘-resp-≈ʳ eq₁ , eq₂)
            }
          ; commute = λ { {Z} {W} g {h , x} {i , y} (eq₁ , eq₂) →
            let open SetoidR (F.₀ W)
            in begin
              α.η W ⟨$⟩ (f ∘ C.id ∘ h ∘ g , G.₁ g ⟨$⟩ x)   ≈⟨ Π.cong (α.η W) (Equiv.trans (pullˡ id-comm) (center Equiv.refl) , Setoid.refl (G.₀ W)) ⟩
              α.η W ⟨$⟩ (C.id ∘ (f ∘ h) ∘ g , G.₁ g ⟨$⟩ x) ≈⟨ α.commute g (∘-resp-≈ʳ eq₁ , eq₂) ⟩
              F.₁ g ⟨$⟩ (α.η Z ⟨$⟩ (f ∘ i , y))            ∎ }
          }
        ; cong  = λ eq (eq₁ , eq₂) → eq (∘-resp-≈ʳ eq₁ , eq₂)
        }
      ; identity     = λ eq (eq₁ , eq₂) → eq (Equiv.trans identityˡ eq₁ , eq₂)
      ; homomorphism = λ eq (eq₁ , eq₂) → eq (pullʳ (∘-resp-≈ʳ eq₁) , eq₂)
      ; F-resp-≈     = λ where eq eq′ (eq₁ , eq₂) → eq′ (∘-resp-≈ eq eq₁ , eq₂)
      } where open MR C

module IsCartesianClosed {o} (C : Category o o o) where
  private
    module C = Category C using (id; _∘_; _≈_; identityˡ; identityʳ; module Equiv)
    P = Presheaves′ o o C
    open HasClosed C using (Presheaf^)
    open Preₚ.IsCartesian C o o using (Presheaves-Cartesian)
    open MR C

  CanonicalCCC : CCartesianClosed P
  CanonicalCCC = record
    { ⊤            = PC.terminal.⊤
    ; _×_          = PC._×_
    ; !            = PC.!
    ; π₁           = PC.π₁
    ; π₂           = PC.π₂
    ; ⟨_,_⟩        = PC.⟨_,_⟩
    ; !-unique     = PC.!-unique
    ; π₁-comp      = λ {_ _ f} {_ g} → PC.project₁ {h = f} {g}
    ; π₂-comp      = λ {_ _ f} {_ g} → PC.project₂ {h = f} {g}
    ; ⟨,⟩-unique   = λ {_ _ _ f g h} → PC.unique {h = h} {i = f} {j = g}
    ; _^_          = Presheaf^
    ; eval         = λ {F G} →
      let module F = Functor F
          module G = Functor G
      in ntHelper record
      { η       = λ X → record
        { _⟨$⟩_ = λ { (α , x) →
          let module α = NaturalTransformation α
          in α.η X ⟨$⟩ (C.id , x) }
        ; cong  = λ where (eq₁ , eq₂) → eq₁ (C.Equiv.refl , eq₂)
        }
      ; commute = λ { {Y} {Z} f {α , x} {β , y} (eq₁ , eq₂) →
        let module α = NaturalTransformation α
            module β = NaturalTransformation β
            open SetoidR (F.₀ Z)
        in begin
        α.η Z ⟨$⟩ (f C.∘ C.id , G.₁ f ⟨$⟩ x)          ≈⟨ eq₁ ((C.Equiv.trans id-comm (C.Equiv.sym C.identityˡ)) , Setoid.refl (G.₀ Z)) ⟩
        β.η Z ⟨$⟩ (C.id C.∘ C.id C.∘ f , G.₁ f ⟨$⟩ x) ≈⟨ β.commute f (C.Equiv.refl , eq₂) ⟩
        F.₁ f ⟨$⟩ (β.η Y ⟨$⟩ (C.id , y))              ∎ }
      }
    ; curry        = λ {F G H} α →
      let module F = Functor F
          module G = Functor G
          module H = Functor H
          module α = NaturalTransformation α
      in ntHelper record
      { η       = λ X → record
        { _⟨$⟩_ = λ x → ntHelper record
          { η       = λ Y → record
            { _⟨$⟩_ = λ where (f , y) → α.η Y ⟨$⟩ (F.₁ f ⟨$⟩ x , y)
            ; cong  = λ where (eq₁ , eq₂) → Π.cong (α.η _) (F.F-resp-≈ eq₁ (Setoid.refl (F.₀ _)) , eq₂)
            }
          ; commute = λ { {Y} {Z} f {g , y} {h , z} (eq₁ , eq₂) →
            let open SetoidR (H.₀ Z)
                open Setoid  (G.₀ Z)
            in begin
              α.η Z ⟨$⟩ (F.F₁ (C.id C.∘ g C.∘ f) ⟨$⟩ x , G.F₁ f ⟨$⟩ y)
                ≈⟨ Π.cong (α.η Z) (F.F-resp-≈ C.identityˡ (Setoid.refl (F.₀ X)) , refl) ⟩
              α.η Z ⟨$⟩ (F.F₁ (g C.∘ f) ⟨$⟩ x , G.F₁ f ⟨$⟩ y)
                ≈⟨ Π.cong (α.η Z) (F.homomorphism (Setoid.refl (F.₀ X)) , refl) ⟩
              α.η Z ⟨$⟩ (F.F₁ f ⟨$⟩ (F.F₁ g ⟨$⟩ x) , G.F₁ f ⟨$⟩ y)
                ≈⟨ α.commute f (F.F-resp-≈ eq₁ (Setoid.refl (F.₀ X)) , eq₂) ⟩
              H.F₁ f ⟨$⟩ (α.η Y ⟨$⟩ (F.F₁ h ⟨$⟩ x , z))
                ∎ }
          }
          ; cong  = λ where eq (eq₁ , eq₂) → Π.cong (α.η _) (F.F-resp-≈ eq₁ eq , eq₂)
        }
      ; commute = λ { {X} {Y} f {x} {y} eq {Z} {g , z} {h , w} (eq₁ , eq₂) →
        let open SetoidR (F.₀ Z)
            helper : g C.≈ h → Setoid._≈_ (F.₀ X) x y →
                     Setoid._≈_ (F.₀ Z) (F.₁ g ⟨$⟩ (F.₁ f ⟨$⟩ x)) (F.₁ (f C.∘ h) ⟨$⟩ y)
            helper eq eq′ = begin
              F.₁ g ⟨$⟩ (F.₁ f ⟨$⟩ x) ≈⟨ F.F-resp-≈ eq (Setoid.refl (F.₀ Y)) ⟩
              F.₁ h ⟨$⟩ (F.₁ f ⟨$⟩ x) ≈˘⟨ F.homomorphism (Setoid.sym (F.₀ X) eq′) ⟩
              F.₁ (f C.∘ h) ⟨$⟩ y     ∎
        in Π.cong (α.η _) (helper eq₁ eq , eq₂) }
      }
    ; eval-comp    = λ {F G H} {α} → λ { (eq₁ , eq₂) →
      let module H  = Functor H
          module α  = NaturalTransformation α
      in Π.cong (α.η _) (H.identity eq₁ , eq₂) }
    ; curry-resp-≈ = λ { {F} {G} eq eq₁ (eq₂ , eq₃) →
      let module G = Functor G
      in eq (G.F-resp-≈ eq₂ eq₁ , eq₃) }
    ; curry-unique = λ {F G H} {α β} eq {X} {x y} eq₁ → λ { {Y} {f , z} {g , w} (eq₂ , eq₃) →
      let module F = Functor F
          module G = Functor G
          module H = Functor H
          module α = NaturalTransformation α
          module β = NaturalTransformation β
          module αXx = NaturalTransformation (α.η X ⟨$⟩ x)
          open Setoid  (H.₀ Y)
          open SetoidR (G.₀ Y)
      in begin
        αXx.η Y ⟨$⟩ (f , z)
          ≈⟨ Π.cong (αXx.η _) (C.Equiv.sym C.identityʳ , refl) ⟩
        αXx.η Y ⟨$⟩ (f C.∘ C.id , z)
          ≈⟨ α.sym-commute f (Setoid.refl (F.₀ X)) (C.Equiv.refl , refl) ⟩
        NaturalTransformation.η (α.η Y ⟨$⟩ (F.F₁ f ⟨$⟩ x)) Y ⟨$⟩ (C.id , z)
          ≈⟨ eq (F.F-resp-≈ eq₂ eq₁ , eq₃) ⟩
        β.η Y ⟨$⟩ (F.F₁ g ⟨$⟩ y , w)
          ∎ }
    }
    where module PC = Presheaves-Cartesian

  Presheaves-CartesianClosed : CartesianClosed P
  Presheaves-CartesianClosed = Equivalence.fromCanonical P CanonicalCCC
