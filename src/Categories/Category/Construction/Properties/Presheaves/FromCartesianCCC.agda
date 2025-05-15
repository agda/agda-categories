{-# OPTIONS --without-K --safe #-}

module Categories.Category.Construction.Properties.Presheaves.FromCartesianCCC where

open import Level using (Level; _⊔_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Function.Construct.Composition using (function)
open import Function.Construct.Setoid using (_∙_)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidR

open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.Core using (Category)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.CartesianClosed using (CartesianClosed)
open import Categories.Category.CartesianClosed.Canonical renaming (CartesianClosed to CCartesianClosed)
open import Categories.Category.Construction.Presheaves using (Presheaves′; Presheaves)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor.Hom using (Hom[_][_,_])
open import Categories.Functor.Properties using ([_]-resp-∘; [_]-resp-square)
open import Categories.Functor.Presheaf using (Presheaf)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.Object.Product.Core using (Product) -- elide
open import Categories.Object.Terminal using (Terminal)

import Categories.Category.Construction.Properties.Presheaves.Cartesian as Preₚ
import Categories.Object.Product as Prod
import Categories.Morphism.Reasoning as MR

module FromCartesian o′ ℓ′ {o ℓ e} {C : Category o ℓ e} (Car : Cartesian C) where
  private
    module C = Category C
    P = Presheaves′ o′ ℓ′ C
    S = Setoids o′ ℓ′
    open Prod C using (id×id)
    open Cartesian Car
    open BinaryProducts products

  Pres-exp : (F : Presheaf C S) (X : C.Obj) → Presheaf C S
  Pres-exp F X = record
    { F₀           = λ Y → F.₀ (X × Y)
    ; F₁           = λ f → F.₁ (second f)
    ; identity     = λ {A} {x} →
      let open Setoid  (F.₀ (X × A))
          open SetoidR (F.₀ (X × A))
      in begin
        F.₁ (second C.id) ⟨$⟩ x ≈⟨ F.F-resp-≈ (id×id (product {X} {A})) ⟩
        F.F₁ C.id ⟨$⟩ x         ≈⟨ F.identity ⟩
        x                      ∎
    ; homomorphism = λ {Y Z W} {f} {g} {x} →
      let open Setoid  (F.₀ (X × Y))
          open SetoidR (F.₀ (X × W))
      in begin
        F.₁ (second (f C.∘ g)) ⟨$⟩ x                ≈˘⟨ [ F ]-resp-∘ second∘second ⟩
        F.₁ (second g) ⟨$⟩ (F.₁ (second f) ⟨$⟩ x) ∎
    ; F-resp-≈     = λ {Y Z} {f g} eq → F.F-resp-≈ (⁂-cong₂ C.Equiv.refl eq)
    }
    where module F = Functor F

  ExpF : (F : Presheaf C (Setoids o′ ℓ′)) → Functor C.op P
  ExpF F = record
    { F₀           = Pres-exp F
    ; F₁           = λ f → ntHelper record
      { η       = λ X → F₁ (first f)
      ; commute = λ g → [ F ]-resp-square (C.Equiv.sym first↔second)
      }
    ; identity     = λ {A B} {x} →
      let open Setoid  (F₀ (A × B))
          open SetoidR (F₀ (A × B))
      in begin
        F₁ (first C.id) ⟨$⟩ x ≈⟨ F-resp-≈ (id×id product) ⟩
        F₁ C.id ⟨$⟩ x         ≈⟨ identity ⟩
        x                     ∎
    ; homomorphism = λ {X Y Z} {f g} {W} {x} →
      let open Setoid  (F₀ (X × W))
          open SetoidR (F₀ (Z × W))
      in begin
        F₁ (first (f C.∘ g)) ⟨$⟩ x              ≈˘⟨ [ F ]-resp-∘ first∘first ⟩
        F₁ (first g) ⟨$⟩ (F₁ (first f) ⟨$⟩ x) ∎
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
        { to = λ α →
          let module α = NaturalTransformation α
          in ntHelper record
          { η       = λ X → F.₁ (first f) ∙ α.η X
          ; commute = λ {X Y} g  {x} →
            let open SetoidR (F.₀ (B × Y))
            in begin
              F.₁ (first f) ⟨$⟩ (α.η Y ⟨$⟩ (G.₁ g ⟨$⟩ x))          ≈⟨ Func.cong (F.₁ (first f)) (α.commute g) ⟩
              F.₁ (first f) ⟨$⟩ (F.₁ (second g) ⟨$⟩ (α.η X ⟨$⟩ x)) ≈˘⟨ [ F ]-resp-square first↔second ⟩
              F.₁ (second g) ⟨$⟩ (F.₁ (first f) ⟨$⟩ (α.η X ⟨$⟩ x)) ∎
          }
        ; cong  = λ {α} {β} eq → Func.cong (F.₁ (first f)) eq
        }
      ; identity     = λ {X} {α} {Y} {x} →
        let module α = NaturalTransformation α
            open SetoidR (F.₀ (X × Y))
        in begin
          F.₁ (first C.id) ⟨$⟩ (α.η Y ⟨$⟩ x) ≈⟨ F.F-resp-≈ (id×id product) ⟩
          F.₁ C.id ⟨$⟩ (α.η Y ⟨$⟩ x)         ≈⟨ F.identity ⟩
          α.η Y ⟨$⟩ x                        ∎
      ; homomorphism = λ {X Y Z} → Setoid.sym (F.₀ (Z × _)) ([ F ]-resp-∘ first∘first)
      ; F-resp-≈     = λ eq → F.F-resp-≈ (⁂-cong₂ eq C.Equiv.refl)
      }

module FromCartesianCCC {o} {C : Category o o o} (Car : Cartesian C) where
  private
    module C  = Category C using (identityˡ; id; module HomReasoning)
    module CH = C.HomReasoning
    P = Presheaves′ o o C
    open BinaryProducts (Cartesian.products Car) using (_×_; π₁; π₂; ⟨_,_⟩; Δ; first; second; _⁂_; Δ∘; ⁂∘Δ; second∘first;
      π₁∘⁂; π₂∘⁂; project₁; project₂; η; product)
    open Preₚ.IsCartesian C o o using () renaming (Presheaves-Cartesian to PC)
    module PPC = BinaryProducts PC.products using (π₁; π₂; _×_; project₁; project₂; ⟨_,_⟩; unique)
    module TPC = Terminal PC.terminal using (⊤; !; !-unique)
    open Func

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
    ; _^_          = FromCartesian.Presheaf^ o o Car
    ; eval         = λ {F G} →
      let module F = Functor F using (₀; ₁)
          module G = Functor G using (₀; ₁)
      in ntHelper record
        { η       = λ X → record
          { to = λ { (α , x) →
            let module α = NaturalTransformation α using (η)
            in F.₁ Δ ⟨$⟩ (α.η X ⟨$⟩ x) }
          ; cong  = λ { {α , gx} {β , gx′} (eq , eq′) → cong (F.₁ Δ) (
             Setoid.trans (Functor.F₀ F (Product.A×B product))
               eq
               (cong (NaturalTransformation.η β X) eq′)
             )}
          }
        ; commute = λ {X Y} f → λ { {α , x} →
          let module α = NaturalTransformation α using (η; commute)
              open Setoid  (F.₀ (X × X)) using (sym; refl)
              open SetoidR (F.₀ Y)
          in  begin
            F.₁ Δ ⟨$⟩ (F.₁ (first f) ⟨$⟩ (α.η Y ⟨$⟩ (G.₁ f ⟨$⟩ x)))    ≈⟨ cong (F.₁ Δ ∙ F.₁ (first f)) (α.commute f) ⟩
            F.₁ Δ ∙ (F.₁ (first f) ∙ F.₁ (second f)) ⟨$⟩ (α.η X ⟨$⟩ x) ≈⟨ cong (F.₁ Δ) ([ F ]-resp-∘ second∘first) ⟩
            F.₁ Δ ⟨$⟩ (F.₁ (f ⁂ f) ⟨$⟩ (α.η X ⟨$⟩ x))                 ≈⟨ [ F ]-resp-∘ ⁂∘Δ ⟩
            F.₁ ⟨ f , f ⟩ ⟨$⟩ (α.η X ⟨$⟩ x)                           ≈˘⟨ [ F ]-resp-∘ Δ∘ ⟩
            F.₁ f ⟨$⟩ (F.₁ Δ ⟨$⟩ (α.η X ⟨$⟩ x))
              ∎ }
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
              { to = λ y → α.η (X × Y) ⟨$⟩ (F.₁ π₁ ⟨$⟩ x , G.₁ π₂ ⟨$⟩ y)
              ; cong  = λ eq → cong (α.η (X × Y)) (Setoid.refl (F.₀ (X × Y)) , cong (G.₁ π₂) eq)
              }
            ; commute = λ {Y Z} f {y} →
              let open SetoidR (H.₀ (X × Z))
              in begin
                α.η (X × Z) ⟨$⟩ (F.₁ π₁ ⟨$⟩ x , G.₁ π₂ ⟨$⟩ (G.₁ f ⟨$⟩ y))
                  ≈˘⟨ cong (α.η (X × Z)) ( [ F ]-resp-∘ (π₁∘⁂ CH.○ C.identityˡ)
                                           , [ G ]-resp-square π₂∘⁂) ⟩
                α.η (X × Z) ⟨$⟩ (F.₁ (second f) ∙ F.₁ π₁ ⟨$⟩ x , G.₁ (second f) ⟨$⟩ (G.₁ π₂ ⟨$⟩ y))
                  ≈⟨ α.commute (second f) ⟩
                H.₁ (second f) ⟨$⟩ (α.η (X × Y) ⟨$⟩ (F.₁ π₁ ⟨$⟩ x , G.₁ π₂ ⟨$⟩ y))
                  ∎
            }
          ; cong  = λ eq → cong (α.η _) ((cong (F.F₁ π₁) eq) , cong (G.₁ π₂) (Setoid.refl (G.F₀ _)))
          }
        ; commute = λ {X Y} f {FX Z} {GZ} →
          let open SetoidR (H.₀ (Y × Z)) in begin
          α.η (Y × Z) ⟨$⟩ (F.₁ π₁ ⟨$⟩ (F.₁ f ⟨$⟩ FX) , G.₁ π₂ ⟨$⟩ GZ)
            ≈˘⟨ cong (α.η _) (([ F ]-resp-square π₁∘⁂) , ([ G ]-resp-∘ (π₂∘⁂ CH.○ C.identityˡ))) ⟩
          α.η (Y × Z) ⟨$⟩ (F.₁ (first f) ⟨$⟩ (F.₁ π₁ ⟨$⟩ FX) , G.₁ (first f) ⟨$⟩ (G.₁ π₂ ⟨$⟩ GZ))
            ≈⟨ α.commute (first f) ⟩
          H.₁ (first f) ⟨$⟩ (α.η (X × Z) ⟨$⟩ (F.₁ π₁ ⟨$⟩ FX , G.₁ π₂ ⟨$⟩ GZ)) ∎
        }
    ; eval-comp    = λ {F G H} {α} → λ { {X} {x , y} →
      let module F = Functor F
          module G = Functor G
          module H = Functor H
          module α = NaturalTransformation α
          module HX = Setoid (H.₀ X)
          module GX = Setoid (G.₀ X)
          open SetoidR (F.₀ X)
      in begin
        F.₁ Δ ⟨$⟩ (α.η (X × X) ⟨$⟩ (H.₁ π₁ ⟨$⟩ x , G.₁ π₂ ⟨$⟩ y))
          ≈⟨ α.sym-commute Δ ⟩
        α.η X ⟨$⟩ (H.₁ Δ ⟨$⟩ (H.F₁ π₁ ⟨$⟩ x) , G.₁ Δ ⟨$⟩ (G.₁ π₂ ⟨$⟩ y))
          ≈⟨ cong (α.η X) ([ H ]-resp-∘ project₁ , [ G ]-resp-∘ project₂) ⟩
        α.η X ⟨$⟩ (H.F₁ C.id ⟨$⟩ x , G.F₁ C.id ⟨$⟩ y)
          ≈⟨ cong (α.η X) (H.identity , G.identity) ⟩
        α.η X ⟨$⟩ (x , y)
          ∎ }
    ; curry-unique = λ {F G H} {α β} eq {X} {x} {Y} {z} →
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
          ≈˘⟨ G.identity ⟩
        G.₁ C.id ⟨$⟩ (αXx.η Y ⟨$⟩ z)
          ≈˘⟨ [ G ]-resp-∘ (⁂∘Δ CH.○ η) ⟩
        G.₁ Δ ⟨$⟩ (G.F₁ (π₁ ⁂ π₂) ⟨$⟩ (αXx.η Y ⟨$⟩ z))
          ≈˘⟨ cong (G.₁ Δ) ([ G ]-resp-∘ second∘first) ⟩
        G.₁ Δ ⟨$⟩ (G.₁ (first π₁) ⟨$⟩ (G.₁ (second π₂) ⟨$⟩ (αXx.η Y ⟨$⟩ z)))
          ≈⟨ cong (G.₁ Δ ∙ G.₁ (first π₁)) (αXx.sym-commute π₂) ⟩
        G.₁ Δ ⟨$⟩ (G.₁ (first π₁) ⟨$⟩ (αXx.η (X × Y) ⟨$⟩ (H.₁ π₂ ⟨$⟩ z)))
          ≈⟨ cong (G.₁ Δ) (α.sym-commute π₁) ⟩
        G.₁ Δ ⟨$⟩ (NaturalTransformation.η (α.η (X × Y) ⟨$⟩ (F.₁ π₁ ⟨$⟩ x)) (X × Y) ⟨$⟩ (H.₁ π₂ ⟨$⟩ z))
          ≈⟨ eq ⟩
        β.η (X × Y) ⟨$⟩ (F.₁ π₁ ⟨$⟩ x , H.₁ π₂ ⟨$⟩ z)
          ∎
    }

  Presheaves-CartesianClosed : CartesianClosed P
  Presheaves-CartesianClosed = Equivalence.fromCanonical P CanonicalCCC
