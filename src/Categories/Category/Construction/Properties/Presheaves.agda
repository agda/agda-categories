{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Construction.Properties.Presheaves where

open import Level
open import Data.Unit
open import Data.Product using (_,_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Function.Equality using (Π)
open import Relation.Binary

open import Categories.Category.Cartesian
open import Categories.Category.CartesianClosed
open import Categories.Category.CartesianClosed.Canonical renaming (CartesianClosed to CCartesianClosed)
open import Categories.Category.Construction.Presheaves
open import Categories.Category.Instance.Setoids
open import Categories.Functor
open import Categories.Functor.Hom
open import Categories.Functor.Properties
open import Categories.Functor.Presheaf
open import Categories.NaturalTransformation

import Categories.Object.Product as Prod
import Relation.Binary.Reasoning.Setoid as SetoidR

open Π using (_⟨$⟩_)

module _ o′ ℓ′ {o ℓ e} (C : Category o ℓ e) where
  private
    module C = Category C
    open C
    P = Presheaves′ o′ ℓ′ C
    module P = Category P
    
  Presheaves-Cartesian : Cartesian P
  Presheaves-Cartesian = record
    { terminal = record
      { ⊤        = record
        { F₀           = λ x → record
          { Carrier       = Lift o′ ⊤
          ; _≈_           = λ _ _ → Lift ℓ′ ⊤
          ; isEquivalence = _
          }
        }
      ; !        = _
      ; !-unique = _
      }
    ; products = record
      { product = λ {A B} →
        let module A = Functor A
            module B = Functor B
        in record
        { A×B      = record
          { F₀           = λ X → ×-setoid (A.₀ X) (B.₀ X)
          ; F₁           = λ f → record
            { _⟨$⟩_ = λ { (a , b) → A.₁ f ⟨$⟩ a , B.₁ f ⟨$⟩ b }
            ; cong  = λ { (eq₁ , eq₂) → Π.cong (A.₁ f) eq₁ , Π.cong (B.₁ f) eq₂ }
            }
          ; identity     = λ { (eq₁ , eq₂)    → A.identity eq₁ , B.identity eq₂ }
          ; homomorphism = λ { (eq₁ , eq₂)    → A.homomorphism eq₁ , B.homomorphism eq₂ }
          ; F-resp-≈     = λ { eq (eq₁ , eq₂) → A.F-resp-≈ eq eq₁ , B.F-resp-≈ eq eq₂ }
          }
        ; π₁       = ntHelper record
          { η       = λ X → record
            { _⟨$⟩_ = λ { (fst , _) → fst }
            ; cong  = λ { (eq , _)  → eq }
            }
          ; commute = λ { f (eq , _) → Π.cong (A.F₁ f) eq }
          }
        ; π₂       = ntHelper record
          { η       = λ X → record
            { _⟨$⟩_ = λ { (_ , snd) → snd }
            ; cong  = λ { (_ , eq)  → eq }
            }
          ; commute = λ { f (_ , eq) → Π.cong (B.F₁ f) eq }
          }
        ; ⟨_,_⟩    = λ {F} α β →
          let module F = Functor F
              module α = NaturalTransformation α
              module β = NaturalTransformation β
          in ntHelper record
          { η       = λ Y → record
            { _⟨$⟩_ = λ S → α.η Y ⟨$⟩ S , β.η Y ⟨$⟩ S
            ; cong  = λ eq → Π.cong (α.η Y) eq , Π.cong (β.η Y) eq
            }
          ; commute = λ f eq → α.commute f eq , β.commute f eq
          }
        ; project₁ = λ {F α β x} eq →
          let module F = Functor F
              module α = NaturalTransformation α
              module β = NaturalTransformation β
          in Π.cong (α.η x) eq
        ; project₂ = λ {F α β x} eq →
          let module F = Functor F
              module α = NaturalTransformation α
              module β = NaturalTransformation β
          in Π.cong (β.η x) eq
        ; unique   = λ {F α β δ} eq₁ eq₂ {x} eq →
          let module F = Functor F
              module α = NaturalTransformation α
              module β = NaturalTransformation β
              module δ = NaturalTransformation δ
          in Setoid.sym (A.₀ x) (eq₁ (Setoid.sym (F.₀ x) eq))
           , Setoid.sym (B.₀ x) (eq₂ (Setoid.sym (F.₀ x) eq))
        }
      }
    }

  module Presheaves-Cartesian = Cartesian Presheaves-Cartesian

  module _ (Car : Cartesian C) where
    open Prod C
    open Cartesian Car
  
    Pres-exp : (F : Presheaf C (Setoids o′ ℓ′)) (X : Obj) → Presheaf C (Setoids o′ ℓ′)
    Pres-exp F X = record
      { F₀           = λ Y → F.₀ (X × Y)
      ; F₁           = λ f → F.₁ (second f)
      ; identity     = λ {A} {x y} eq →
        let open Setoid  (F.₀ (X × A))
            open SetoidR (F.₀ (X × A))
        in begin
          F.₁ (second C.id) ⟨$⟩ x ≈⟨ F.F-resp-≈ (id×id (product {X} {A})) refl ⟩
          F.F₁ C.id ⟨$⟩ x         ≈⟨ F.identity eq ⟩
          y                       ∎
      ; homomorphism = λ {Y Z W} {f} {g} {x y} eq →
        let open Setoid (F.₀ (X × Y))
            open SetoidR (F.₀ (X × W))
        in begin
          F.₁ (second (f ∘ g)) ⟨$⟩ x                ≈˘⟨ [ F ]-resp-∘ second∘second (sym eq) ⟩
          F.₁ (second g) ⟨$⟩ (F.₁ (second f) ⟨$⟩ y) ∎
      ; F-resp-≈     = λ {Y Z} {f g} eq → F.F-resp-≈ (⁂-cong₂ Equiv.refl eq)
      }
      where module F = Functor F

    ExpF : (F : Presheaf C (Setoids o′ ℓ′)) → Functor C.op P
    ExpF F = record
      { F₀           = Pres-exp F
      ; F₁           = λ {A B} f → ntHelper record
        { η       = λ X → F₁ (first f)
        ; commute = λ {X Y} g {x y} eq →
          [ F ]-resp-square (Equiv.sym first↔second) eq
        }
      ; identity     = λ {A B} {x y} eq →
        let open Setoid  (F₀ (A × B))
            open SetoidR (F₀ (A × B))
        in begin
          F₁ (first C.id) ⟨$⟩ x ≈⟨ F-resp-≈ (id×id product) eq ⟩
          F₁ C.id ⟨$⟩ y         ≈⟨ identity refl ⟩
          y                     ∎
      ; homomorphism = λ {X Y Z} {f g} {W} {x y} eq →
        let open Setoid (F₀ (X × W))
            open SetoidR (F₀ (Z × W))
        in begin
          F₁ (first (f ∘ g)) ⟨$⟩ x ≈˘⟨ [ F ]-resp-∘ first∘first (sym eq) ⟩
          F₁ (first g) ⟨$⟩ (F₁ (first f) ⟨$⟩ y) ∎
      ; F-resp-≈     = λ {A B} {f g} eq → F-resp-≈ (⁂-cong₂ eq Equiv.refl)
      }
      where open Functor F

-- module _ {o} (C : Category o o o) (Car : Cartesian C) where
--   private
--     module C = Category C
--     open C
--     open Prod C
--     P = Presheaves′ o o C
--     module P = Category P
--     open Cartesian Car

--   CanonicalCCC : CCartesianClosed P
--   CanonicalCCC = record
--     { ⊤            = PC.terminal.⊤
--     ; _×_          = PC._×_
--     ; !            = PC.!
--     ; π₁           = PC.π₁
--     ; π₂           = PC.π₂
--     ; ⟨_,_⟩        = PC.⟨_,_⟩
--     ; !-unique     = PC.!-unique
--     ; π₁-comp      = λ {_ _ f} {_ g} → PC.project₁ {h = f} {g}
--     ; π₂-comp      = λ {_ _ f} {_ g} → PC.project₂ {h = f} {g}
--     ; ⟨,⟩-unique   = λ {_ _ _ f g h} → PC.unique {h = h} {i = f} {j = g}
--     ; _^_          = λ F G →
--       let module F = Functor F
--           module G = Functor G
--       in record
--       { F₀           = λ X → Hom[ F , Pres-exp G X ]
--       ; F₁           = {!!}
--       ; identity     = {!!}
--       ; homomorphism = {!!}
--       ; F-resp-≈     = {!!}
--       }
--     ; eval         = {!!}
--     ; curry        = {!!}
--     ; eval-comp    = {!!}
--     ; curry-resp-≈ = {!!}
--     ; curry-unique = {!!}
--     }
--     where module PC = Presheaves-Cartesian o o C
--           open Hom P

--   Presheaves-CartesianClosed : CartesianClosed P
--   Presheaves-CartesianClosed = Equivalence.fromCanonical P CanonicalCCC
