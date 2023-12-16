{-# OPTIONS --without-K --safe #-}

module Categories.Category.Concrete.Properties where

open import Data.Unit.Polymorphic
open import Function.Base using (const; _∘_)
open import Function.Bundles using (Func; _⟨$⟩_)
import Function.Construct.Constant as Const
import Function.Construct.Composition as Comp
-- open import Function.Equality using (Π; _⟨$⟩_; const; _∘_)
open import Level
open import Relation.Binary using (Setoid)
import Relation.Binary.Reasoning.Setoid as SR

open import Categories.Adjoint using (_⊣_; Adjoint)
open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Concrete
open import Categories.Functor.Core using (Functor)
open import Categories.Functor.Representable using (Representable)
open import Categories.Functor.Properties using (Faithful)
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)

open Concrete

⊣⇒Representable : {o ℓ e : Level} (C : Category o ℓ e) (conc : Concrete C ℓ e) → (F : Functor (Setoids ℓ e) C) →
  F ⊣ concretize conc  → RepresentablyConcrete C
⊣⇒Representable {_} {ℓ} {e} C conc F L = record
  { conc = conc
  ; representable = record
    { A = F.₀ OneS
    ; Iso = record
      { F⇒G = ntHelper record
        { η = λ X → record
          { to = λ x → L.counit.η X C.∘ F.₁ (Const.function OneS (U.F₀ X) x)
          ; cong = λ i≈j → C.∘-resp-≈ʳ (F.F-resp-≈ λ _ → i≈j)
          }
        ; commute = λ {X} {Y} f {x} {y} x≈y →
            let open C.HomReasoning in begin
            L.counit.η Y C.∘ F.₁ (Const.function OneS (U.F₀ Y) (U.₁ f ⟨$⟩ x))              ≈⟨ refl⟩∘⟨ F.F-resp-≈ (λ _ → Func.cong (U.₁ f) x≈y) ⟩
            L.counit.η Y C.∘ F.₁ (Comp.function (Const.function OneS (U.F₀ X) y) (U.F₁ f)) ≈⟨ pushʳ F.homomorphism ⟩
            ((L.counit.η Y C.∘ F.₁ (U.₁ f)) C.∘ F.₁ (Const.function OneS (U.F₀ X) y))      ≈⟨ pushˡ (commute L.counit f) ⟩
            f C.∘ L.counit.η X C.∘ F.₁ (Const.function OneS (U.F₀ X) y)                    ≈˘⟨ C.identityʳ ⟩
            (f C.∘ L.counit.η X C.∘ F.₁ (Const.function OneS (U.F₀ X) y)) C.∘ C.id         ∎
        }
      ; F⇐G = ntHelper record
        { η = λ c → record
          { to = λ 1⇒c → U.₁ 1⇒c ⟨$⟩ η1
          ; cong = λ i≈j → U.F-resp-≈ i≈j (Setoid.refl (U.₀ (F.₀ OneS)))
          }
        ; commute = λ {X} {Y} f {x} {y} x≈y →
             let module CH = C.HomReasoning in
             let open SR (U.₀ Y) in
             begin
             U.₁ ((f C.∘ x) C.∘ C.id) ⟨$⟩ η1 ≈⟨ U.F-resp-≈ (C.identityʳ CH.○ (CH.refl⟩∘⟨ x≈y)) Srefl ⟩
             U.₁ (f C.∘ y) ⟨$⟩ η1            ≈⟨ U.homomorphism Srefl ⟩
             U.₁ f ⟨$⟩ (U.₁ y ⟨$⟩ η1)         ∎
        }
      ; iso = λ X → record
        { isoˡ = λ {x} {y} x≈y → Setoid.trans (U.₀ X) (L.LRadjunct≈id {OneS} {X} {Const.function OneS (U.F₀ X) x} tt) x≈y
        ; isoʳ = λ {1⇒x} {1⇒y} x≈y →
          let open C.HomReasoning in begin
          L.counit.η X C.∘ F.₁ (Const.function OneS (U.F₀ X) (U.₁ 1⇒x ⟨$⟩ η1)) ≈⟨ (refl⟩∘⟨ F.F-resp-≈ λ _ → U.F-resp-≈ x≈y Srefl) ⟩
          L.counit.η X C.∘ F.₁ (Comp.function (L.unit.η OneS) (U.₁ 1⇒y))       ≈⟨ L.RLadjunct≈id {OneS} {X} {1⇒y}  ⟩
          1⇒y ∎
        }
      }
    }
  }
  where
  module C = Category C
  module U = Functor (concretize conc)
  module F = Functor F
  module L = Adjoint L
  open NaturalTransformation
  open MR C
  -- Is this somewhere else?  Should it be?
  OneS : Setoid ℓ e
  OneS = record { Carrier = ⊤ {ℓ} ; _≈_ = λ _ _ → ⊤ {e}}
  η1 : Setoid.Carrier (U.₀ (F.₀ OneS))
  η1 = L.unit.η OneS ⟨$⟩ tt
  Srefl = Setoid.refl (U.₀ (F.₀ OneS))
