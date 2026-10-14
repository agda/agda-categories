{-# OPTIONS --safe --without-K #-}

open import Categories.Category using (Category)

module Categories.Adjoint.Instance.Slice {o ℓ e} (C : Category o ℓ e) where

open import Categories.Adjoint using (_⊣_)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.CartesianClosed C using (CartesianClosed)
open import Categories.Category.Slice C using (SliceObj; sliceobj; Slice⇒; slicearr)
open import Categories.Diagram.Pullback C using (Pullback)
open import Categories.Functor.Properties using ([_]-resp-∘; [_]-resp-square)
open import Categories.Functor.Slice C using (TotalSpace; ConstantFamily; InternalSections; InternalSections-lemma)
open import Categories.Morphism.Reasoning C
open import Categories.NaturalTransformation using (ntHelper)
open import Categories.Object.Product C

open Category C
open HomReasoning

open SliceObj
open Slice⇒

module _ {A : Obj} (product : ∀ {X} → Product X A) where

  private
    module product {X} = Product (product {X})
    open product

  TotalSpace⊣ConstantFamily : TotalSpace ⊣ ConstantFamily product
  TotalSpace⊣ConstantFamily = record
    { unit = ntHelper record
      { η = λ _ → slicearr project₂
      ; commute = λ {X} {Y} f → begin
        ⟨ id , arr Y ⟩ ∘ h f                            ≈⟨ ∘-distribʳ-⟨⟩ ⟩
        ⟨ id ∘ h f , arr Y ∘ h f ⟩                      ≈⟨ ⟨⟩-cong₂ identityˡ (△ f) ⟩
        ⟨ h f , arr X ⟩                                 ≈˘⟨ ⟨⟩-cong₂ identityʳ identityˡ ⟩
        ⟨ h f ∘ id , id ∘ arr X ⟩                       ≈˘⟨ [ product ⇒ product ]×∘⟨⟩ ⟩
        [ product ⇒ product ] h f × id ∘ ⟨ id , arr X ⟩ ∎
      }
    ; counit = ntHelper record
      { η = λ _ → π₁
      ; commute = λ _ → project₁
      }
    ; zig = project₁
    ; zag = begin
      [ product ⇒ product ] π₁ ×id ∘ ⟨ id , π₂ ⟩ ≈⟨ [ product ⇒ product ]×∘⟨⟩ ⟩
      ⟨ π₁ ∘ id , id ∘ π₂ ⟩                      ≈⟨ ⟨⟩-cong₂ identityʳ identityˡ ⟩
      ⟨ π₁ , π₂ ⟩                                ≈⟨ η ⟩
      id                                         ∎
    }

module _ {A : Obj} (cc : CartesianClosed) (pb : ∀ {X Y Z} {f : X ⇒ Z} {g : Y ⇒ Z} → Pullback f g) where

  open CartesianClosed cc
  open Cartesian cartesian

  private
    id′ : ⊤ ⇒ A ^ A
    id′ = λg π₂

    pb′ : ∀ {B} (f : B ⇒ A) → Pullback (λg (f ∘ eval)) id′
    pb′ _ = pb

    pb″ : ∀ X → Pullback (λg (π₂ {X} {A} ∘ eval)) id′
    pb″ _ = pb

    module pb {B} (f : B ⇒ A) = Pullback (pb′ f)

    abstract
      unit-η-lemma : ∀ X → λg (π₂ {X} {A} ∘ eval) ∘ λg id ≈ λg π₂ ∘ !
      unit-η-lemma X = begin
        λg (π₂ ∘ eval) ∘ λg id         ≈⟨ subst ○ λ-cong assoc ⟩
        λg (π₂ ∘ eval ∘ first (λg id)) ≈⟨ λ-cong (∘-resp-≈ʳ β) ⟩
        λg (π₂ ∘ id)                   ≈⟨ λ-cong identityʳ ⟩
        λg π₂                            ≈⟨ λ-cong π₂∘first ⟨
        λg (π₂ ∘ first !)                ≈⟨ subst ⟨
        λg π₂ ∘ !                        ∎

    abstract
      unit-commute-lemma : ∀ {X Y} (f : X ⇒ Y)
                         → pb.p₁ π₂ ∘ pb.universal π₂ (unit-η-lemma Y) ∘ f
                         ≈ pb.p₁ π₂ ∘ pb.universal π₂ (InternalSections-lemma cc pb (project₂ {h = f ∘ π₁} ○ identityˡ)) ∘ pb.universal π₂ (unit-η-lemma X)
      unit-commute-lemma f =  begin
        pb.p₁ π₂ ∘ pb.universal π₂ _ ∘ f                   ≈⟨ pullˡ (pb.p₁∘universal≈h₁ π₂) ⟩
        λg id ∘ f                                          ≈⟨ subst ○ λ-cong identityˡ ⟩
        λg (first f)                                       ≈⟨ λ-cong (introʳ β) ⟩
        λg (first f ∘ eval ∘ first (λg id))                ≈⟨ subst ○ λ-cong assoc ⟨
        λg (first f ∘ eval) ∘ λg id                        ≈⟨ refl⟩∘⟨ pb.p₁∘universal≈h₁ π₂ ⟨
        λg (first f ∘ eval) ∘ pb.p₁ π₂ ∘ pb.universal π₂ _ ≈⟨ extendʳ (pb.p₁∘universal≈h₁ π₂) ⟨
        pb.p₁ π₂ ∘ pb.universal π₂ _ ∘ pb.universal π₂ _   ∎

    abstract
      counit-η-lemma : ∀ {Y} (f : Y ⇒ A) → λg (f ∘ eval ∘ first (pb.p₁ f)) ≈ λg π₂
      counit-η-lemma f = begin
        λg (f ∘ eval ∘ first (pb.p₁ f)) ≈⟨ subst ○ λ-cong assoc ⟨
        λg (f ∘ eval) ∘ pb.p₁ f         ≈⟨ pb.commute f ⟩
        λg π₂ ∘ pb.p₂ f                 ≈⟨ subst ⟩
        λg (π₂ ∘ first (pb.p₂ f))       ≈⟨ λ-cong π₂∘first ⟩
        λg π₂                           ∎

    abstract
      zag-lemma : ∀ {B} {f : B ⇒ A}
                → pb.p₁ f ∘ pb.universal f (InternalSections-lemma cc pb (λ-inj (counit-η-lemma f))) ∘ pb.universal π₂ (unit-η-lemma (pb.P f))
                ≈ pb.p₁ f ∘ id
      zag-lemma {f = f} = begin
        pb.p₁ f ∘ pb.universal f _ ∘ pb.universal π₂ _                      ≈⟨ extendʳ (pb.p₁∘universal≈h₁ f) ⟩
        λg ((eval ∘ first (pb.p₁ f)) ∘ eval) ∘ pb.p₁ π₂ ∘ pb.universal π₂ _ ≈⟨ refl⟩∘⟨ pb.p₁∘universal≈h₁ π₂ ⟩
        λg ((eval ∘ first (pb.p₁ f)) ∘ eval) ∘ λg id                        ≈⟨ subst ○ λ-cong (cancelʳ β) ⟩
        λg (eval ∘ first (pb.p₁ f))                                         ≈⟨ η-exp ⟩
        pb.p₁ f                                                             ≈⟨ identityʳ ⟨
        pb.p₁ f ∘ id                                                        ∎

  ConstantFamily⊣InternalSections : ConstantFamily {A} product ⊣ InternalSections cc pb
  ConstantFamily⊣InternalSections = record
    { unit = ntHelper record
      { η = λ X → pb.universal π₂ (unit-η-lemma X)
      ; commute = λ f → pb.unique-diagram π₂ (unit-commute-lemma f) !-unique₂
      }
    ; counit = ntHelper record
      { η = λ (sliceobj f) → slicearr (λ-inj (counit-η-lemma f))
      ; commute = λ (slicearr {h = h} △) →  begin
        (eval ∘ first (pb.p₁ _)) ∘ first (pb.universal _ _) ≈⟨ pullʳ ([ -× A ]-resp-square (pb.p₁∘universal≈h₁ _)) ⟩
        eval ∘ first (λg (h ∘ eval)) ∘ first (pb.p₁ _)      ≈⟨ extendʳ β ⟩
        h ∘ eval ∘ first (pb.p₁ _)                          ∎
      }
    ; zig = glueTrianglesˡ β ([ -× A ]-resp-∘ (pb.p₁∘universal≈h₁ π₂))
    ; zag = λ {(sliceobj {B} f)} → pb.unique-diagram f zag-lemma !-unique₂
    }
