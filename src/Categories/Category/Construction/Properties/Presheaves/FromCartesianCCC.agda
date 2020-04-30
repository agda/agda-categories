{-# OPTIONS --without-K --safe #-}

module Categories.Category.Construction.Properties.Presheaves.FromCartesianCCC where

open import Level
open import Data.Unit
open import Data.Product using (_,_; proj₁; proj₂)
open import Function.Equality using (Π) renaming (_∘_ to _∙_)
open import Relation.Binary
import Relation.Binary.Reasoning.Setoid as SetoidR

open import Categories.Category.Core using (Category)
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

import Categories.Category.Construction.Properties.Presheaves.Cartesian as Preₚ
import Categories.Object.Product as Prod
import Categories.Morphism.Reasoning as MR

open Π using (_⟨$⟩_)

module FromCartesian o′ ℓ′ {o ℓ e} {C : Category o ℓ e} (Car : Cartesian C) where
  private
    module C = Category C
    P = Presheaves′ o′ ℓ′ C
    S = Setoids o′ ℓ′
    open Prod C using (id×id)
    open Cartesian Car

  Pres-exp : (F : Presheaf C S) (X : C.Obj) → Presheaf C S
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
      let open Setoid  (F.₀ (X × Y))
          open SetoidR (F.₀ (X × W))
      in begin
        F.₁ (second (f C.∘ g)) ⟨$⟩ x                ≈˘⟨ [ F ]-resp-∘ second∘second (sym eq) ⟩
        F.₁ (second g) ⟨$⟩ (F.₁ (second f) ⟨$⟩ y) ∎
    ; F-resp-≈     = λ {Y Z} {f g} eq → F.F-resp-≈ (⁂-cong₂ C.Equiv.refl eq)
    }
    where module F = Functor F

  ExpF : (F : Presheaf C (Setoids o′ ℓ′)) → Functor C.op P
  ExpF F = record
    { F₀           = Pres-exp F
    ; F₁           = λ {A B} f → ntHelper record
      { η       = λ X → F₁ (first f)
      ; commute = λ {X Y} g {x y} eq →
        [ F ]-resp-square (C.Equiv.sym first↔second) eq
      }
    ; identity     = λ {A B} {x y} eq →
      let open Setoid  (F₀ (A × B))
          open SetoidR (F₀ (A × B))
      in begin
        F₁ (first C.id) ⟨$⟩ x ≈⟨ F-resp-≈ (id×id product) eq ⟩
        F₁ C.id ⟨$⟩ y         ≈⟨ identity refl ⟩
        y                     ∎
    ; homomorphism = λ {X Y Z} {f g} {W} {x y} eq →
      let open Setoid  (F₀ (X × W))
          open SetoidR (F₀ (Z × W))
      in begin
        F₁ (first (f C.∘ g)) ⟨$⟩ x              ≈˘⟨ [ F ]-resp-∘ first∘first (sym eq) ⟩
        F₁ (first g) ⟨$⟩ (F₁ (first f) ⟨$⟩ y) ∎
    ; F-resp-≈     = λ {A B} {f g} eq → F-resp-≈ (⁂-cong₂ eq C.Equiv.refl)
    }
    where open Functor F

  module _ (F G : Presheaf C (Setoids o′ ℓ′)) where
    private
      module F = Functor F
      module G = Functor G

    Presheaf^ : Presheaf C (Setoids (o′ ⊔ ℓ′ ⊔ o ⊔ ℓ) (o′ ⊔ ℓ′ ⊔ o))
    Presheaf^ = record
      { F₀           = λ X → Hom[ Presheaves C ][ G , Pres-exp F X ]
      ; F₁           = λ {A B} f → record
        { _⟨$⟩_ = λ α →
          let module α = NaturalTransformation α
          in ntHelper record
          { η       = λ X → F.₁ (first f) ∙ α.η X
          ; commute = λ {X Y} g  {x y} eq →
            let open SetoidR (F.₀ (B × Y))
            in begin
              F.₁ (first f) ⟨$⟩ (α.η Y ⟨$⟩ (G.₁ g ⟨$⟩ x))          ≈⟨ Π.cong (F.₁ (first f)) (α.commute g eq) ⟩
              F.₁ (first f) ⟨$⟩ (F.₁ (second g) ⟨$⟩ (α.η X ⟨$⟩ y)) ≈˘⟨ [ F ]-resp-square first↔second (Setoid.refl (F.₀ (A × X))) ⟩
              F.₁ (second g) ⟨$⟩ (F.₁ (first f) ⟨$⟩ (α.η X ⟨$⟩ y)) ∎
          }
        ; cong  = λ eq eq′ → Π.cong (F.₁ (first f)) (eq eq′)
        }
      ; identity     = λ {X} {α β} eq {Y} {x y} eq′ →
        let module α = NaturalTransformation α
            module β = NaturalTransformation β
            open SetoidR (F.₀ (X × Y))
        in begin
          F.₁ (first C.id) ⟨$⟩ (α.η Y ⟨$⟩ x) ≈⟨ F.F-resp-≈ (id×id product) (eq eq′) ⟩
          F.₁ C.id ⟨$⟩ (β.η Y ⟨$⟩ y)         ≈⟨ F.identity (Setoid.refl (F.₀ (X × Y))) ⟩
          β.η Y ⟨$⟩ y                        ∎
      ; homomorphism = λ {X Y Z} eq {W} eq′ →
        let open Setoid  (F.₀ (X × W))
        in Setoid.sym (F.₀ (Z × W)) ([ F ]-resp-∘ first∘first (sym (eq eq′)))
      ; F-resp-≈     = λ eq eq′ eq″ → F.F-resp-≈ (⁂-cong₂ eq C.Equiv.refl) (eq′ eq″)
      }

module FromCartesianCCC {o} {C : Category o o o} (Car : Cartesian C) where
  private
    module C  = Category C using (identityˡ; id; module HomReasoning)
    module CH = C.HomReasoning
    P = Presheaves′ o o C
    open Cartesian Car
    open Preₚ.IsCartesian C o o using () renaming (Presheaves-Cartesian to PC)

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
    ; _^_          = FromCartesian.Presheaf^ o o Car
    ; eval         = λ {F G} →
      let module F = Functor F using (₀; ₁)
          module G = Functor G using (₀; ₁)
      in ntHelper record
        { η       = λ X → record
          { _⟨$⟩_ = λ { (α , x) →
            let module α = NaturalTransformation α using (η)
            in F.₁ Δ ⟨$⟩ (α.η X ⟨$⟩ x) }
          ; cong  = λ { (eq , eq′) → Π.cong (F.₁ Δ) (eq eq′) }
          }
        ; commute = λ {X Y} f → λ { {α , x} {β , y} (eq , eq′) →
          let module α = NaturalTransformation α using (η; commute)
              module β = NaturalTransformation β using (η)
              open Setoid  (F.₀ (X × X)) using (sym; refl)
              open SetoidR (F.₀ Y)
          in begin
            F.₁ Δ ⟨$⟩ (F.₁ (first f) ⟨$⟩ (α.η Y ⟨$⟩ (G.₁ f ⟨$⟩ x)))
              ≈⟨ Π.cong (F.₁ Δ ∙ F.₁ (first f)) (α.commute f eq′) ⟩
            F.₁ Δ ∙ F.₁ (first f) ∙ F.₁ (second f) ⟨$⟩ (α.η X ⟨$⟩ y)
              ≈⟨ Π.cong (F.₁ Δ) ([ F ]-resp-∘ second∘first refl) ⟩
            F.₁ Δ ⟨$⟩ (F.₁ (f ⁂ f) ⟨$⟩ (α.η X ⟨$⟩ y))
              ≈⟨ [ F ]-resp-∘ ⁂∘Δ refl ⟩
            F.₁ ⟨ f , f ⟩ ⟨$⟩ (α.η X ⟨$⟩ y)
              ≈˘⟨ [ F ]-resp-∘ Δ∘ (sym (eq (Setoid.refl (G.₀ X)))) ⟩
            F.₁ f ⟨$⟩ (F.₁ Δ ⟨$⟩ (β.η X ⟨$⟩ y))
              ∎ }
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
              { _⟨$⟩_ = λ y → α.η (X × Y) ⟨$⟩ (F.₁ π₁ ⟨$⟩ x , G.₁ π₂ ⟨$⟩ y)
              ; cong  = λ eq → Π.cong (α.η (X × Y)) (Setoid.refl (F.₀ (X × Y)) , Π.cong (G.₁ π₂) eq)
              }
            ; commute = λ {Y Z} f {y z} eq →
              let open SetoidR (H.₀ (X × Z))
              in begin
                α.η (X × Z) ⟨$⟩ (F.₁ π₁ ⟨$⟩ x , G.₁ π₂ ⟨$⟩ (G.₁ f ⟨$⟩ y))
                  ≈˘⟨ Π.cong (α.η (X × Z)) ( [ F ]-resp-∘ (π₁∘⁂ CH.○ C.identityˡ) (Setoid.refl (F.₀ X))
                                           , [ G ]-resp-square π₂∘⁂ (Setoid.refl (G.₀ Y))) ⟩
                α.η (X × Z) ⟨$⟩ (F.₁ (second f) ∙ F.₁ π₁ ⟨$⟩ x , G.₁ (second f) ⟨$⟩ (G.₁ π₂ ⟨$⟩ y))
                  ≈⟨ α.commute (second f) (Setoid.refl (F.₀ (X × Y)) , Π.cong (G.₁ π₂) eq) ⟩
                H.₁ (second f) ⟨$⟩ (α.η (X × Y) ⟨$⟩ (F.₁ π₁ ⟨$⟩ x , G.₁ π₂ ⟨$⟩ z))
                  ∎
            }
          ; cong  = λ eq₁ eq₂ → Π.cong (α.η _) (Π.cong (F.F₁ π₁) eq₁ , Π.cong (G.₁ π₂) eq₂)
          }
        ; commute = λ {X Y} f {x y} eq₁ {Z} {z w} eq₂ →
          let open SetoidR (H.₀ (Y × Z))
          in begin
            α.η (Y × Z) ⟨$⟩ (F.₁ π₁ ⟨$⟩ (F.₁ f ⟨$⟩ x) , G.₁ π₂ ⟨$⟩ z)
              ≈˘⟨ Π.cong (α.η _) ( [ F ]-resp-square π₁∘⁂ (Setoid.refl (F.₀ X))
                                 , [ G ]-resp-∘ (π₂∘⁂ CH.○ C.identityˡ) (Setoid.refl (G.₀ Z))) ⟩
            α.η (Y × Z) ⟨$⟩ (F.₁ (first f) ⟨$⟩ (F.₁ π₁ ⟨$⟩ x) , G.₁ (first f) ⟨$⟩ (G.₁ π₂ ⟨$⟩ z))
              ≈⟨ α.commute (first f) (Π.cong (F.₁ π₁) eq₁ , Π.cong (G.₁ π₂) eq₂) ⟩
            H.₁ (first f) ⟨$⟩ (α.η (X × Z) ⟨$⟩ (F.₁ π₁ ⟨$⟩ y , G.₁ π₂ ⟨$⟩ w))
              ∎
        }
    ; eval-comp    = λ {F G H} {α} → λ { {X} {x , y} {z , w} (eq₁ , eq₂) →
      let module F = Functor F
          module G = Functor G
          module H = Functor H
          module α = NaturalTransformation α
          module HX = Setoid (H.₀ X)
          module GX = Setoid (G.₀ X)
          open SetoidR (F.₀ X)
      in begin
        F.₁ Δ ⟨$⟩ (α.η (X × X) ⟨$⟩ (H.₁ π₁ ⟨$⟩ x , G.₁ π₂ ⟨$⟩ y))
          ≈⟨ α.sym-commute Δ (Π.cong (H.₁ π₁) eq₁ , Π.cong (G.₁ π₂) eq₂) ⟩
        α.η X ⟨$⟩ (H.₁ Δ ⟨$⟩ (H.F₁ π₁ ⟨$⟩ z) , G.₁ Δ ⟨$⟩ (G.₁ π₂ ⟨$⟩ w))
          ≈⟨ Π.cong (α.η X) ([ H ]-resp-∘ project₁ HX.refl , [ G ]-resp-∘ project₂ GX.refl) ⟩
        α.η X ⟨$⟩ (H.F₁ C.id ⟨$⟩ z , G.F₁ C.id ⟨$⟩ w)
          ≈⟨ Π.cong (α.η X) (H.identity HX.refl , G.identity GX.refl) ⟩
        α.η X ⟨$⟩ (z , w)
          ∎ }
    ; curry-resp-≈ = λ {F G H} eq eq₁ eq₂ →
      let module G = Functor G
          module H = Functor H
      in eq (Π.cong (G.₁ π₁) eq₁ , Π.cong (H.₁ π₂) eq₂)
    ; curry-unique = λ {F G H} {α β} eq {X} {x y} eq₁ {Y} {z w} eq₂ →
      let module F   = Functor F
          module G   = Functor G
          module H   = Functor H
          module α   = NaturalTransformation α
          module β   = NaturalTransformation β
          module GXY = Setoid (G.₀ (X × Y))
          module αXx = NaturalTransformation (α.η X ⟨$⟩ x)
          open SetoidR (G.₀ (X × Y))
      in begin
        αXx.η Y ⟨$⟩ z
          ≈˘⟨ G.identity GXY.refl ⟩
        G.₁ C.id ⟨$⟩ (αXx.η Y ⟨$⟩ z)
          ≈˘⟨ [ G ]-resp-∘ (⁂∘Δ CH.○ η) GXY.refl ⟩
        G.₁ Δ ⟨$⟩ (G.F₁ (π₁ ⁂ π₂) ⟨$⟩ (αXx.η Y ⟨$⟩ z))
          ≈˘⟨ Π.cong (G.₁ Δ) ([ G ]-resp-∘ second∘first GXY.refl) ⟩
        G.₁ Δ ⟨$⟩ (G.₁ (first π₁) ⟨$⟩ (G.₁ (second π₂) ⟨$⟩ (αXx.η Y ⟨$⟩ z)))
          ≈⟨ Π.cong (G.₁ Δ ∙ G.₁ (first π₁)) (αXx.sym-commute π₂ (Setoid.refl (H.₀ Y))) ⟩
        G.₁ Δ ⟨$⟩ (G.₁ (first π₁) ⟨$⟩ (αXx.η (X × Y) ⟨$⟩ (H.₁ π₂ ⟨$⟩ z)))
          ≈⟨ Π.cong (G.₁ Δ) (α.sym-commute π₁ (Setoid.refl (F.₀ X)) (Setoid.refl (H.₀ (X × Y)))) ⟩
        G.₁ Δ ⟨$⟩ (NaturalTransformation.η (α.η (X × Y) ⟨$⟩ (F.₁ π₁ ⟨$⟩ x)) (X × Y) ⟨$⟩ (H.₁ π₂ ⟨$⟩ z))
          ≈⟨ eq (Π.cong (F.₁ π₁) eq₁ , Π.cong (H.₁ π₂) eq₂) ⟩
        β.η (X × Y) ⟨$⟩ (F.₁ π₁ ⟨$⟩ y , H.₁ π₂ ⟨$⟩ w)
          ∎
    }

  Presheaves-CartesianClosed : CartesianClosed P
  Presheaves-CartesianClosed = Equivalence.fromCanonical P CanonicalCCC
