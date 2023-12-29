{-# OPTIONS --without-K --safe #-}

module Categories.Category.Construction.Properties.Presheaves.CartesianClosed where

open import Level using (Level; _⊔_)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Product using (_,_; proj₁; proj₂)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary using (Setoid)

open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.Core using (Category)
open import Categories.Category.CartesianClosed using (CartesianClosed)
open import Categories.Category.CartesianClosed.Canonical renaming (CartesianClosed to CCartesianClosed)
open import Categories.Category.Construction.Presheaves using (Presheaves; Presheaves′)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor.Hom using (Hom[_][_,_]; Hom[_][-,_])
open import Categories.Functor.Presheaf using (Presheaf)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.Object.Terminal using (Terminal)

import Categories.Category.Construction.Properties.Presheaves.Cartesian as Preₚ
import Categories.Morphism.Reasoning as MR
import Relation.Binary.Reasoning.Setoid as SetoidR

open Func

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
        { to = λ α →
          let module α = NaturalTransformation α using (η; commute)
          in ntHelper record
          { η       = λ X → record
            { to = λ where (g , S) → α.η X ⟨$⟩ (f ∘ g , S)
            ; cong  = λ where (eq₁ , eq₂) → cong (α.η X) (∘-resp-≈ʳ eq₁ , eq₂)
            }
          ; commute = λ { {Z} {W} g {h , x} →
            let open SetoidR (F.₀ W)
            in begin
              α.η W ⟨$⟩ (f ∘ C.id ∘ h ∘ g , G.₁ g ⟨$⟩ x)   ≈⟨ cong (α.η W) (Equiv.trans (pullˡ id-comm) (center Equiv.refl) , Setoid.refl (G.₀ W)) ⟩
              α.η W ⟨$⟩ (C.id ∘ (f ∘ h) ∘ g , G.₁ g ⟨$⟩ x) ≈⟨ α.commute g ⟩
              F.₁ g ⟨$⟩ (α.η Z ⟨$⟩ (f ∘ h , x))            ∎ }
          }
        ; cong  = λ eq → eq
        }
      ; identity     = λ {A} {α} {x} → cong (η α x) (identityˡ , Setoid.refl (G.F₀ x))
      ; homomorphism = λ {_} {_} {_} {f} {g} {α} {A} → cong (η α _) (assoc , Setoid.refl (G.F₀ _))
      ; F-resp-≈     = λ eq {α} {A} {x} → cong (η α _) (∘-resp-≈ˡ eq , Setoid.refl (G.F₀ _))
      }
      where
        open MR C
        open NaturalTransformation

module IsCartesianClosed {o} (C : Category o o o) where
  private
    module C = Category C using (id; _∘_; _≈_; identityˡ; identityʳ; module Equiv)
    P = Presheaves′ o o C
    open HasClosed C using (Presheaf^)
    open Preₚ.IsCartesian C o o using (Presheaves-Cartesian)
    open MR C

  CanonicalCCC : CCartesianClosed P
  CanonicalCCC = record
    { ⊤            = TPC.⊤
    ; _×_          = PPC._×_
    ; !            = TPC.!
    ; π₁           = PPC.π₁
    ; π₂           = PPC.π₂
    ; ⟨_,_⟩        = PPC.⟨_,_⟩
    ; !-unique     = TPC.!-unique
    ; π₁-comp      = λ {_ _ f} {_ g} → PPC.project₁ {h = f} {g}
    ; π₂-comp      = λ {_ _ f} {_ g} → PPC.project₂ {h = f} {g}
    ; ⟨,⟩-unique   = λ {_ _ _ f g h} → PPC.unique {h = h} {i = f} {j = g}
    ; _^_          = Presheaf^
    ; eval         = λ {F G} →
      let module F = Functor F
          module G = Functor G
      in ntHelper record
      { η       = λ X → record
        { to = λ { (α , x) →
          let module α = NaturalTransformation α
          in α.η X ⟨$⟩ (C.id , x) }
        ; cong  = λ { {α₁ , f₁} {α₂ , f₂} (eq₁ , eq₂) → 
            let module SR = SetoidR (F.F₀ X) in
            let open SR
                open NaturalTransformation
            in begin
              to (η α₁ X) (C.id , f₁) ≈⟨ eq₁ ⟩
              to (η α₂ X) (C.id , f₁) ≈⟨ cong (η α₂ X) (C.Equiv.refl , eq₂) ⟩
              to (η α₂ X) (C.id , f₂) ∎ }
        }
      ; commute = λ { {Y} {Z} f {α , x} →
        let module α = NaturalTransformation α
            open SetoidR (F.₀ Z)
        in begin
        α.η Z ⟨$⟩ (f C.∘ C.id , G.₁ f ⟨$⟩ x)          ≈⟨ cong (α.η Z) (C.Equiv.trans id-comm (C.Equiv.sym C.identityˡ) , Setoid.refl (G.F₀ Z)) ⟩
        α.η Z ⟨$⟩ (C.id C.∘ C.id C.∘ f , G.₁ f ⟨$⟩ x) ≈⟨ α.commute f ⟩
        F.₁ f ⟨$⟩ (α.η Y ⟨$⟩ (C.id , x))              ∎ }
      }
    ; curry        = λ {F G H} α →
      let module F = Functor F
          module G = Functor G
          module H = Functor H
          module α = NaturalTransformation α
      in ntHelper record
      { η       = λ X → record
        { to = λ x → ntHelper record
          { η       = λ Y → record
            { to = λ where (f , y) → α.η Y ⟨$⟩ (F.₁ f ⟨$⟩ x , y)
            ; cong  = λ {(eq₁ , eq₂) → cong (α.η Y) ((F.F-resp-≈ eq₁) , eq₂) }
            }
          ; commute = λ { {Y} {Z} f {g , y} →
            let open SetoidR (H.₀ Z)
                open Setoid  (G.₀ Z)
            in begin
              α.η Z ⟨$⟩ (F.F₁ (C.id C.∘ g C.∘ f) ⟨$⟩ x , G.F₁ f ⟨$⟩ y)
                ≈⟨ cong (α.η Z) (F.F-resp-≈ C.identityˡ , refl) ⟩
              α.η Z ⟨$⟩ (F.F₁ (g C.∘ f) ⟨$⟩ x , G.F₁ f ⟨$⟩ y)
                ≈⟨ cong (α.η Z) (F.homomorphism , refl) ⟩
              α.η Z ⟨$⟩ (F.F₁ f ⟨$⟩ (F.F₁ g ⟨$⟩ x) , G.F₁ f ⟨$⟩ y)
                ≈⟨ α.commute f ⟩
              H.F₁ f ⟨$⟩ (α.η Y ⟨$⟩ (F.F₁ g ⟨$⟩ x , y))
                ∎ }
          }
          ; cong  = λ eq → cong (α.η _) ((cong (F.F₁ _) eq) , (Setoid.refl (G.F₀ _)))
        }
      ; commute = λ { {X} {Y} f {x} {A} {g , z} →
            let open Setoid (F.₀ A) in
            cong (NaturalTransformation.η α A) (sym (F.homomorphism) , Setoid.refl (G.F₀ A)) }
      }
    ; eval-comp    = λ {F G H} {α} →
      let module H  = Functor H
          module α  = NaturalTransformation α
      in cong (α.η _) (H.identity , (Setoid.refl (Functor.F₀ G _)))
    ; curry-unique = λ {F G H} {α β} eq {X} {x y} → λ { {f , z} → 
      let module F = Functor F
          module G = Functor G
          module α = NaturalTransformation α
          module β = NaturalTransformation β
          module αXx = NaturalTransformation (α.η X ⟨$⟩ x)
          open Setoid  (Functor.₀ H y)
          open SetoidR (G.₀ y)
      in begin
        αXx.η y ⟨$⟩ (f , z)           ≈⟨ cong (αXx.η _) (C.Equiv.sym C.identityʳ , refl) ⟩
        αXx.η y ⟨$⟩ (f C.∘ C.id , z)  ≈⟨ α.sym-commute f ⟩
        NaturalTransformation.η (α.η y ⟨$⟩ (F.F₁ f ⟨$⟩ x)) y ⟨$⟩ (C.id , z) ≈⟨ eq ⟩
        β.η y ⟨$⟩ (F.F₁ f ⟨$⟩ x , z)
          ∎ }
    }
    where
      module PC = Presheaves-Cartesian
      module PPC = BinaryProducts PC.products using (π₁; π₂; _×_; project₁; project₂; ⟨_,_⟩; unique)
      module TPC = Terminal PC.terminal using (⊤; !; !-unique)

  Presheaves-CartesianClosed : CartesianClosed P
  Presheaves-CartesianClosed = Equivalence.fromCanonical P CanonicalCCC
