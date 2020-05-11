{-# OPTIONS --without-K --safe #-}
module Categories.NaturalTransformation.Dinatural where

open import Level
open import Data.Product
open import Relation.Binary using (Rel; IsEquivalence; Setoid)

open import Categories.Category
open import Categories.NaturalTransformation as NT hiding (_∘ʳ_)
open import Categories.Functor
open import Categories.Functor.Construction.Constant
open import Categories.Functor.Bifunctor
open import Categories.Category.Product
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level
    C D E : Category o ℓ e

record DinaturalTransformation (F G : Bifunctor (Category.op C) C D) : Set (levelOfTerm F) where
  eta-equality
  private
    module C = Category C
    module D = Category D
    module F = Functor F
    module G = Functor G

  open D hiding (op)
  open Commutation D

  field
    α          : ∀ X → D [ F.F₀ (X , X) , G.F₀ (X , X) ]
    commute    : ∀ {X Y} (f : C [ X , Y ]) →
                [ F.F₀ (Y , X) ⇒ G.F₀ (X , Y) ]⟨
                  F.F₁ (f , C.id)             ⇒⟨ F.F₀ (X , X) ⟩
                  α X                         ⇒⟨ G.F₀ (X , X) ⟩
                  G.F₁ (C.id , f)
                ≈ F.F₁ (C.id , f)             ⇒⟨ F.F₀ (Y , Y) ⟩
                  α Y                         ⇒⟨ G.F₀ (Y , Y) ⟩
                  G.F₁ (f , C.id)
                ⟩
    -- We add this extra proof, because, again, we want to ensure the opposite of the
    -- opposite of dinatural transformation is definitionally equal to itself.
    op-commute : ∀ {X Y} (f : C [ X , Y ]) →
                [ F.F₀ (Y , X) ⇒ G.F₀ (X , Y) ]⟨
                  F.F₁ (C.id , f)             ⇒⟨ F.F₀ (Y , Y) ⟩
                  (α Y                         ⇒⟨ G.F₀ (Y , Y) ⟩
                  G.F₁ (f , C.id))
                ≈ F.F₁ (f , C.id)             ⇒⟨ F.F₀ (X , X) ⟩
                  (α X                         ⇒⟨ G.F₀ (X , X) ⟩
                  G.F₁ (C.id , f))
                ⟩

  op : DinaturalTransformation G.op F.op
  op = record
    { α          = α
    ; commute    = op-commute
    ; op-commute = commute
    }

-- to reduce the burden of constructing a DinaturalTransformation, we introduce
-- another helper.
record DTHelper (F G : Bifunctor (Category.op C) C D) : Set (levelOfTerm F) where
  private
    module C = Category C
    module D = Category D
    module F = Functor F
    module G = Functor G
  open D hiding (op)
  open Commutation D

  field
    α          : ∀ X → D [ F.F₀ (X , X) , G.F₀ (X , X) ]
    commute    : ∀ {X Y} (f : C [ X , Y ]) →
                [ F.F₀ (Y , X) ⇒ G.F₀ (X , Y) ]⟨
                  F.F₁ (f , C.id)             ⇒⟨ F.F₀ (X , X) ⟩
                  α X                         ⇒⟨ G.F₀ (X , X) ⟩
                  G.F₁ (C.id , f)
                ≈ F.F₁ (C.id , f)             ⇒⟨ F.F₀ (Y , Y) ⟩
                  α Y                         ⇒⟨ G.F₀ (Y , Y) ⟩
                  G.F₁ (f , C.id)
                ⟩

dtHelper : ∀ {F G : Bifunctor (Category.op C) C D} → DTHelper F G → DinaturalTransformation F G
dtHelper {D = D} θ = record
  { α          = α
  ; commute    = commute
  ; op-commute = λ f → assoc ○ ⟺ (commute f) ○ sym-assoc
  }
  where open DTHelper θ
        open Category D
        open HomReasoning

module _ {F G H : Bifunctor (Category.op C) C D} where
  private
    module C = Category C
  open Category D
  open HomReasoning
  open Functor
  open MR D

  infixr 9 _<∘_
  infixl 9 _∘>_

  _<∘_ : NaturalTransformation G H → DinaturalTransformation F G → DinaturalTransformation F H
  θ <∘ β = dtHelper record
    { α       = λ X → η (X , X) ∘ α X
    ; commute = λ {X Y} f → begin
      F₁ H (C.id , f) ∘ (η (X , X) ∘ α X) ∘ F₁ F (f , C.id)   ≈˘⟨ pushˡ (pushˡ (θ.commute (C.id , f))) ⟩
      ((η (X , Y) ∘ F₁ G (C.id , f)) ∘ α X) ∘ F₁ F (f , C.id) ≈⟨ assoc ○ pullʳ (β.commute f) ⟩
      η (X , Y) ∘ F₁ G (f , C.id) ∘ α Y ∘ F₁ F (C.id , f)     ≈⟨ pullˡ (θ.commute (f , C.id)) ○ pullʳ sym-assoc ⟩
      F₁ H (f , C.id) ∘ (η (Y , Y) ∘ α Y) ∘ F₁ F (C.id , f)   ∎
    }
    where module θ = NaturalTransformation θ
          module β = DinaturalTransformation β
          open θ
          open β

  _∘>_ : DinaturalTransformation G H → NaturalTransformation F G → DinaturalTransformation F H
  β ∘> θ = dtHelper record
    { α       = λ X → α X ∘ η (X , X)
    ; commute = λ {X Y} f → begin
      F₁ H (C.id , f) ∘ (α X ∘ η (X , X)) ∘ F₁ F (f , C.id) ≈⟨ refl⟩∘⟨ pullʳ (θ.commute (f , C.id)) ⟩
      F₁ H (C.id , f) ∘ α X ∘ F₁ G (f , C.id) ∘ η (Y , X)   ≈⟨ ∘-resp-≈ʳ sym-assoc ○ sym-assoc ⟩
      (F₁ H (C.id , f) ∘ α X ∘ F₁ G (f , C.id)) ∘ η (Y , X) ≈⟨ β.commute f ⟩∘⟨refl ⟩
      (F₁ H (f , C.id) ∘ α Y ∘ F₁ G (C.id , f)) ∘ η (Y , X) ≈˘⟨ pushʳ (assoc ○ pushʳ (θ.commute (C.id , f))) ⟩
      F₁ H (f , C.id) ∘ (α Y ∘ η (Y , Y)) ∘ F₁ F (C.id , f) ∎
    }
    where module θ = NaturalTransformation θ
          module β = DinaturalTransformation β
          open θ
          open β

module _ {F G : Bifunctor (Category.op C) C D} where
  private
    module C = Category C
  open Category D
  open HomReasoning
  open Functor
  open MR D

  infixl 9 _∘ʳ_

  _∘ʳ_ : ∀ {E : Category o ℓ e} →
           DinaturalTransformation F G → (K : Functor E C) → DinaturalTransformation (F ∘F ((Functor.op K) ⁂ K)) (G ∘F ((Functor.op K) ⁂ K))
  _∘ʳ_ {E = E} β K = dtHelper record
    { α       = λ X → α (F₀ K X)
    ; commute = λ {X Y} f → begin
      F₁ G (F₁ K E.id , F₁ K f) ∘ α (F₀ K X) ∘ F₁ F (F₁ K f , F₁ K E.id)
        ≈⟨ F-resp-≈ G (identity K , C.Equiv.refl) ⟩∘⟨ Equiv.refl ⟩∘⟨ F-resp-≈ F (C.Equiv.refl , identity K) ⟩
      F₁ G (C.id , F₁ K f) ∘ α (F₀ K X) ∘ F₁ F (F₁ K f , C.id)
        ≈⟨ commute (F₁ K f) ⟩
      F₁ G (F₁ K f , C.id) ∘ α (F₀ K Y) ∘ F₁ F (C.id , F₁ K f)
        ≈˘⟨ F-resp-≈ G (C.Equiv.refl , identity K) ⟩∘⟨ Equiv.refl ⟩∘⟨ F-resp-≈ F (identity K , C.Equiv.refl) ⟩
      F₁ G (F₁ K f , F₁ K E.id) ∘ α (F₀ K Y) ∘ F₁ F (F₁ K E.id , F₁ K f)
        ∎
    }
    where module β = DinaturalTransformation β
          module E = Category E
          open β

  infix 4 _≃_

  _≃_ : Rel (DinaturalTransformation F G) _
  β ≃ δ = ∀ {X} → α β X ≈ α δ X
    where open DinaturalTransformation

  ≃-isEquivalence : IsEquivalence _≃_
  ≃-isEquivalence = record
    { refl  = Equiv.refl
    ; sym   = λ eq → Equiv.sym eq
    ; trans = λ eq eq′ → Equiv.trans eq eq′
    }

  ≃-setoid : Setoid _ _
  ≃-setoid = record
    { Carrier       = DinaturalTransformation F G
    ; _≈_           = _≃_
    ; isEquivalence = ≃-isEquivalence
    }


-- for convenience, the following are some helpers for the cases
-- in which the bifunctor on the right is extranatural.
Extranaturalʳ : ∀ {C : Category o ℓ e} → Category.Obj D → (F : Bifunctor (Category.op C) C D) → Set _
Extranaturalʳ A F = DinaturalTransformation (const A) F

Extranaturalˡ : ∀ {C : Category o ℓ e} → (F : Bifunctor (Category.op C) C D) → Category.Obj D → Set _
Extranaturalˡ F A = DinaturalTransformation F (const A)

module _ {F : Bifunctor (Category.op C) C D} where
  open Category D
  private
    module C = Category C
    variable
      A : Obj
      X Y : C.Obj
      f : X C.⇒ Y
  open Functor F
  open HomReasoning
  open MR D

  extranaturalʳ : (a : ∀ X → A ⇒ F₀ (X , X)) →
                  (∀ {X X′ f} → F₁ (C.id , f) ∘ a X ≈ F₁ (f , C.id) ∘ a X′) →
                  Extranaturalʳ A F
  extranaturalʳ a comm = dtHelper record
    { α       = a
    ; commute = λ f → ∘-resp-≈ʳ identityʳ ○ comm ○ ∘-resp-≈ʳ (⟺ identityʳ)
    }

  open DinaturalTransformation

  extranatural-commʳ : (β : DinaturalTransformation (const A) F) →
                       F₁ (C.id , f) ∘ α β X ≈ F₁ (f , C.id) ∘ α β Y
  extranatural-commʳ {f = f} β = ∘-resp-≈ʳ (⟺ identityʳ) ○ commute β f ○ ∘-resp-≈ʳ identityʳ

  -- the dual case, the bifunctor on the left is extranatural.

  extranaturalˡ : (a : ∀ X → F₀ (X , X) ⇒ A) →
                  (∀ {X X′ f} → a X ∘ F₁ (f , C.id) ≈ a X′ ∘ F₁ (C.id , f)) →
                  Extranaturalˡ F A
  extranaturalˡ a comm = dtHelper record
    { α       = a
    ; commute = λ f → pullˡ identityˡ ○ comm ○ ⟺ (pullˡ identityˡ)
    }

  extranatural-commˡ : (β : DinaturalTransformation F (const A)) →
                       α β X ∘ F₁ (f , C.id) ≈ α β Y ∘ F₁ (C.id , f)
  extranatural-commˡ {f = f} β = ⟺ (pullˡ identityˡ) ○ commute β f ○ pullˡ identityˡ
