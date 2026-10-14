{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)

module Categories.Functor.Slice {o ℓ e} (C : Category o ℓ e) where

open import Function.Base using (_$_) renaming (id to id→)

open import Categories.Category.Cartesian C using (Cartesian)
open import Categories.Category.CartesianClosed C using (CartesianClosed)
open import Categories.Diagram.Pullback C using (Pullback; unglue; Pullback-resp-≈)
open import Categories.Functor using (Functor)
open import Categories.Functor.Properties using ([_]-resp-∘)
open import Categories.Morphism.Reasoning C
open import Categories.Object.Product C
open import Categories.Object.Terminal C

import Categories.Category.Slice as S
import Categories.Category.Construction.Pullbacks as Pbs

open Category C
open HomReasoning
open Equiv

module _ {A : Obj} where
  open S.SliceObj
  open S.Slice⇒

  -- A functor between categories induces one between the corresponding slices at a given object of C.
  Base-F : ∀ {o′ ℓ′ e′} {D : Category o′ ℓ′ e′} (F : Functor C D) → Functor (S.Slice C A) (S.Slice D (Functor.F₀ F A))
  Base-F F = record
    { F₀           = λ s → S.sliceobj (F₁ (arr s))
    ; F₁           = λ s⇒ → S.slicearr ([ F ]-resp-∘ (△ s⇒))
    ; identity     = identity
    ; homomorphism = homomorphism
    ; F-resp-≈     = F-resp-≈
    }
    where open Functor F

  open S C

  TotalSpace : Functor (Slice A) C
  TotalSpace = record
    { F₀           = Y
    ; F₁           = h
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = id→
    }

  module _ (product : {X : Obj} → Product A X) where

    private
      module product {X} = Product (product {X})
      open product

    -- this is adapted from proposition 1.33 of Aspects of Topoi (Freyd, 1972)
    ConstantFamily : Functor C (Slice A)
    ConstantFamily = record
      { F₀ = λ _ → sliceobj π₁
      ; F₁ = λ f → slicearr ([ product ⇒ product ]π₁∘× ○ identityˡ)
      ; identity = id×id product
      ; homomorphism = sym [ product ⇒ product ⇒ product ]id×∘id×
      ; F-resp-≈ = λ f≈g → ⟨⟩-cong₂ refl (∘-resp-≈ˡ f≈g)
      }

  module _ (cartesianClosed : CartesianClosed) (pb : ∀ {X Y Z} {f : X ⇒ Z} {g : Y ⇒ Z} → Pullback f g)  where

    open CartesianClosed cartesianClosed
    open Cartesian cartesian

    private
      id′ : ⊤ ⇒ A ^ A
      id′ = λg π₂

      pb′ : ∀ {B} (f : B ⇒ A) → Pullback (λg (f ∘ eval)) id′
      pb′ f = pb

      module pb {B} (f : B ⇒ A) = Pullback (pb′ f)

      abstract
        lemma : ∀ {B B′} {f : B ⇒ A} {g : B′ ⇒ A} {h : B ⇒ B′} → g ∘ h ≈ f → λg (g ∘ eval) ∘ λg (h ∘ eval) ∘ pb.p₁ f ≈ id′ ∘ pb.p₂ f
        lemma {f = f} {g = g} {h = h} △ = begin
          λg (g ∘ eval) ∘ λg (h ∘ eval) ∘ pb.p₁ f         ≈⟨ pullˡ (subst ○ λ-cong assoc) ⟩
          λg (g ∘ eval ∘ first (λg (h ∘ eval))) ∘ pb.p₁ f ≈⟨ λ-cong (∘-resp-≈ʳ β) ⟩∘⟨refl ⟩
          λg (g ∘ h ∘ eval) ∘ pb.p₁ f                     ≈⟨ λ-cong (pullˡ △) ⟩∘⟨refl ⟩
          λg (f ∘ eval) ∘ pb.p₁ f                         ≈⟨ pb.commute f ⟩
          id′ ∘ pb.p₂ f                                   ∎

    InternalSections : Functor (Slice A) C
    InternalSections = record
      { F₀ = λ (sliceobj f) → pb.P f
      ; F₁ = λ (slicearr △) → pb.universal _ (lemma △)
      ; identity = sym $ pb.unique _ identity-lemma identityʳ
      ; homomorphism = λ {_} {_} {_} {(slicearr △)} {(slicearr ▲)} → sym $ pb.unique _ (homomorphism-lemma₁ △ ▲) (homomorphism-lemma₂ △ ▲)
      ; F-resp-≈ = λ eq → pb.universal-resp-≈ _ (∘-resp-≈ˡ (λ-cong (∘-resp-≈ˡ eq))) refl
      }
      where
        identity-lemma : ∀ {B} {f : B ⇒ A} → pb.p₁ f ∘ id ≈ λg (id ∘ eval) ∘ pb.p₁ f
        identity-lemma = begin
          pb.p₁ _ ∘ id             ≈⟨ identityʳ ⟩
          pb.p₁ _                  ≈⟨ introˡ η-id ⟩
          λg eval ∘ pb.p₁ _        ≈⟨ λ-cong identityˡ ⟩∘⟨refl ⟨
          λg (id ∘ eval) ∘ pb.p₁ _ ∎

        homomorphism-lemma₁ : ∀ {B B′ B″} {f : B ⇒ A} {f′ : B′ ⇒ A} {f″ : B″ ⇒ A} {h : B ⇒ B′} {h′ : B′ ⇒ B″} (△ : f′ ∘ h ≈ f) (▲ : f″ ∘ h′ ≈ f′)
                            → pb.p₁ f″ ∘ pb.universal f″ (lemma ▲) ∘ pb.universal f′ (lemma △)
                            ≈ λg ((h′ ∘ h) ∘ eval) ∘ pb.p₁ f
        homomorphism-lemma₁ △ ▲ = begin
          pb.p₁ _ ∘ pb.universal _ (lemma ▲) ∘ pb.universal _ (lemma △) ≈⟨ glue′ (pb.p₁∘universal≈h₁ _) (pb.p₁∘universal≈h₁ _) ⟩
          (λg (_ ∘ eval) ∘ λg (_ ∘ eval)) ∘ pb.p₁ _                     ≈⟨ (subst ○ λ-cong (extendˡ β)) ⟩∘⟨refl ⟩
          λg (_ ∘ eval) ∘ pb.p₁ _                                       ∎

        homomorphism-lemma₂ : ∀ {B B′ B″} {f : B ⇒ A} {f′ : B′ ⇒ A} {f″ : B″ ⇒ A} {h : B ⇒ B′} {h′ : B′ ⇒ B″} (△ : f′ ∘ h ≈ f) (▲ : f″ ∘ h′ ≈ f′)
                            → pb.p₂ f″ ∘ pb.universal f″ (lemma ▲) ∘ pb.universal f′ (lemma △) ≈ pb.p₂ f
        homomorphism-lemma₂ △ ▲ = glueTrianglesʳ (pb.p₂∘universal≈h₂ _) (pb.p₂∘universal≈h₂ _)

