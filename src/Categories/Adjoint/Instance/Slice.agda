{-# OPTIONS --safe --without-K #-}

open import Categories.Category using (Category)

module Categories.Adjoint.Instance.Slice {o ℓ e} (C : Category o ℓ e) where

open import Categories.Adjoint using (_⊣_)
open import Categories.Category.BinaryProducts C
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.CartesianClosed using (CartesianClosed)
open import Categories.Category.Slice C using (SliceObj; sliceobj; Slice⇒; slicearr)
open import Categories.Functor.Slice C using (Forgetful; Free; Coforgetful)
open import Categories.Morphism.Reasoning C
open import Categories.NaturalTransformation using (ntHelper)
open import Categories.Diagram.Pullback C hiding (swap)
open import Categories.Object.Product C
open import Categories.Object.Terminal C

open import Function.Base using (_$_)

open Category C
open HomReasoning

open SliceObj
open Slice⇒

module _ {A : Obj} (product : ∀ {X} → Product A X) where

  private
    module product {X} = Product (product {X})
    open product

  Forgetful⊣Free : Forgetful ⊣ Free product
  Forgetful⊣Free = record
    { unit = ntHelper record
      { η = λ _ → slicearr project₁
      ; commute = λ {X} {Y} f → begin
        ⟨ arr Y , id ⟩ ∘ h f                            ≈⟨ ∘-distribʳ-⟨⟩ ⟩
        ⟨ arr Y ∘ h f , id ∘ h f ⟩                      ≈⟨ ⟨⟩-cong₂ (△ f) identityˡ ⟩
        ⟨ arr X , h f ⟩                                 ≈˘⟨ ⟨⟩-cong₂ identityˡ identityʳ ⟩
        ⟨ id ∘ arr X , h f ∘ id ⟩                       ≈˘⟨ [ product ⇒ product ]×∘⟨⟩ ⟩
        [ product ⇒ product ] id × h f ∘ ⟨ arr X , id ⟩ ∎
      }
    ; counit = ntHelper record
      { η = λ _ → π₂
      ; commute = λ _ → project₂
      }
    ; zig = project₂
    ; zag = begin
      [ product ⇒ product ]id× π₂ ∘ ⟨ π₁ , id ⟩ ≈⟨ [ product ⇒ product ]×∘⟨⟩ ⟩
      ⟨ id ∘ π₁ , π₂ ∘ id ⟩                     ≈⟨ ⟨⟩-cong₂ identityˡ identityʳ ⟩
      ⟨ π₁ , π₂ ⟩                               ≈⟨ η ⟩
      id                                        ∎
    }

module _ {A : Obj} (ccc : CartesianClosed C) (pullback : ∀ {X} {Y} {Z} (h : X ⇒ Z) (i : Y ⇒ Z) → Pullback h i) where

  open CartesianClosed ccc
  open Cartesian cartesian
  open Terminal terminal
  open BinaryProducts products

  Free⊣Coforgetful : Free {A = A} product ⊣ Coforgetful ccc pullback
  Free⊣Coforgetful = record
    { unit = ntHelper record
      { η = λ X → p.universal (sliceobj π₁) (λ-unique₂′ (unit-pb X))
      ; commute = λ {S} {T} f → p.unique-diagram (sliceobj π₁) !-unique₂ $ begin
        p.p₂ (sliceobj π₁) ∘ p.universal (sliceobj π₁) _ ∘ f                                       ≈⟨ pullˡ (p.p₂∘universal≈h₂ (sliceobj π₁)) ⟩
        λg swap ∘ f                                                                                ≈⟨ subst ⟩
        λg (swap ∘ first f)                                                                        ≈⟨ λ-cong swap∘⁂ ⟩
        λg (second f ∘ swap)                                                                       ≈˘⟨ λ-cong (∘-resp-≈ʳ β′) ⟩
        λg (second f ∘ eval′ ∘ first (λg swap))                                                    ≈˘⟨ λ-cong (∘-resp-≈ʳ (∘-resp-≈ʳ (⁂-cong₂ (p.p₂∘universal≈h₂ (sliceobj π₁)) Equiv.refl))) ⟩
        λg (second f ∘ eval′ ∘ first (p.p₂ (sliceobj π₁) ∘ p.universal (sliceobj π₁) _))           ≈˘⟨ λ-cong (pull-last first∘first) ⟩
        λg ((second f ∘ eval′ ∘ first (p.p₂ (sliceobj π₁))) ∘ first (p.universal (sliceobj π₁) _)) ≈˘⟨ subst ⟩
        λg (second f ∘ eval′ ∘ first (p.p₂ (sliceobj π₁))) ∘ p.universal (sliceobj π₁) _           ≈˘⟨ pullˡ (p.p₂∘universal≈h₂ (sliceobj π₁)) ⟩
        p.p₂ (sliceobj π₁) ∘ p.universal (sliceobj π₁) _ ∘ p.universal (sliceobj π₁) _             ∎
      }
    ; counit = ntHelper record
      { η = λ X → slicearr (counit-△ X)
      ; commute = λ {S} {T} f → begin
        (eval′ ∘ first (p.p₂ T) ∘ swap) ∘ second (p.universal T _) ≈⟨ pull-last swap∘⁂ ⟩
        eval′ ∘ first (p.p₂ T) ∘ first (p.universal T _) ∘ swap    ≈⟨ refl⟩∘⟨ pullˡ first∘first ⟩
        eval′ ∘ first (p.p₂ T ∘ p.universal T _) ∘ swap            ≈⟨ refl⟩∘⟨ ⁂-cong₂ (p.p₂∘universal≈h₂ T) Equiv.refl ⟩∘⟨refl ⟩
        eval′ ∘ first (λg (h f ∘ eval′ ∘ first (p.p₂ S))) ∘ swap   ≈⟨ pullˡ β′ ⟩
        (h f ∘ eval′ ∘ first (p.p₂ S)) ∘ swap                      ≈⟨ assoc²' ⟩
        h f ∘ eval′ ∘ first (p.p₂ S) ∘ swap                        ∎
      }
    ; zig = λ {X} → begin
      (eval′ ∘ first (p.p₂ (sliceobj π₁)) ∘ swap) ∘ second (p.universal (sliceobj π₁) _) ≈⟨ assoc²' ⟩
      eval′ ∘ first (p.p₂ (sliceobj π₁)) ∘ swap ∘ second (p.universal (sliceobj π₁) _)   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ swap∘⁂ ⟩
      eval′ ∘ first (p.p₂ (sliceobj π₁)) ∘ first (p.universal (sliceobj π₁) _) ∘ swap    ≈⟨ refl⟩∘⟨ pullˡ first∘first ⟩
      eval′ ∘ first (p.p₂ (sliceobj π₁) ∘ p.universal (sliceobj π₁) _) ∘ swap            ≈⟨ refl⟩∘⟨ ⁂-cong₂ (p.p₂∘universal≈h₂ (sliceobj π₁)) Equiv.refl ⟩∘⟨refl ⟩
      eval′ ∘ first (λg swap) ∘ swap                                                     ≈⟨ pullˡ β′ ⟩
      swap ∘ swap                                                                        ≈⟨ swap∘swap ⟩
      id                                                                                 ∎
    ; zag = λ {X} → p.unique-diagram X !-unique₂ $ begin
      p.p₂ X ∘ p.universal X _ ∘ p.universal (sliceobj π₁) _                                                  ≈⟨ pullˡ (p.p₂∘universal≈h₂ X) ⟩
      λg ((eval′ ∘ first (p.p₂ X) ∘ swap) ∘ eval′ ∘ first (p.p₂ (sliceobj π₁))) ∘ p.universal (sliceobj π₁) _ ≈˘⟨ pullˡ (subst ○ λ-cong assoc) ⟩
      λg ((eval′ ∘ first (p.p₂ X) ∘ swap) ∘ eval′) ∘ p.p₂ (sliceobj π₁) ∘ p.universal (sliceobj π₁) _         ≈⟨ refl⟩∘⟨ p.p₂∘universal≈h₂ (sliceobj π₁) ⟩
      λg ((eval′ ∘ first (p.p₂ X) ∘ swap) ∘ eval′) ∘ λg swap                                                  ≈⟨ subst ⟩
      λg (((eval′ ∘ first (p.p₂ X) ∘ swap) ∘ eval′) ∘ first (λg swap))                                        ≈⟨ λ-cong (pullʳ β′) ⟩
      λg ((eval′ ∘ first (p.p₂ X) ∘ swap) ∘ swap)                                                             ≈⟨ λ-cong (pullʳ (cancelʳ swap∘swap)) ⟩
      λg (eval′ ∘ first (p.p₂ X))                                                                             ≈⟨ η-exp′ ⟩
      p.p₂ X                                                                                                  ≈˘⟨ identityʳ ⟩
      p.p₂ X ∘ id                                                                                             ∎
    }
    where
      p : (X : SliceObj A) → Pullback {X = ⊤} {Z = A ^ A} {Y = Y X ^ A} (λg π₂) (λg (arr X ∘ eval′))
      p X = pullback (λg π₂) (λg (arr X ∘ eval′))
      module p X = Pullback (p X)

      abstract
        unit-pb : ∀ (X : Obj) → eval′ ∘ first {A = X} {C = A} (λg π₂ ∘ !) ≈ eval′ ∘ first (λg (π₁ ∘ eval′) ∘ λg swap)
        unit-pb X = begin
          eval′ ∘ first (λg π₂ ∘ !)                         ≈˘⟨ refl⟩∘⟨ first∘first ⟩
          eval′ ∘ first (λg π₂) ∘ first !                   ≈⟨ pullˡ β′ ⟩
          π₂ ∘ first !                                      ≈⟨ π₂∘⁂ ○ identityˡ ⟩
          π₂                                                ≈˘⟨ project₁ ⟩
          π₁ ∘ swap                                         ≈˘⟨ refl⟩∘⟨ β′ ⟩
          π₁ ∘ eval′ ∘ first (λg swap)                      ≈˘⟨ extendʳ β′ ⟩
          eval′ ∘ first (λg (π₁ ∘ eval′)) ∘ first (λg swap) ≈⟨ refl⟩∘⟨ first∘first ⟩
          eval′ ∘ first (λg (π₁ ∘ eval′) ∘ λg swap)         ∎
        -- A good chunk of the above, maybe all if you squint, is duplicated with F₁-lemma
        -- eval′ ∘ first (λg π₂ ∘ !) ≈ eval′ ∘ first (λg (f ∘ eval′) ∘ first (λg g)
        -- With f : X ⇒ Y and g : Z × Y ⇒ X. Not sure what conditions f and g need to have

        -- Would it be better if Free used π₂ rather than π₁?
        -- It would mean we could avoid this swap
        counit-△ : ∀ X → arr X ∘ eval′ ∘ first (p.p₂ X) ∘ swap ≈ π₁
        counit-△ X = begin
          arr X ∘ eval′ ∘ first (p.p₂ X) ∘ swap     ≈˘⟨ assoc² ⟩
          ((arr X ∘ eval′) ∘ first (p.p₂ X)) ∘ swap ≈⟨ lemma ⟩∘⟨refl ⟩
          (π₂ ∘ first (p.p₁ X)) ∘ swap              ≈⟨ (π₂∘⁂ ○ identityˡ) ⟩∘⟨refl ⟩
          π₂ ∘ swap                                 ≈⟨ project₂ ⟩
          π₁                                        ∎
          where
            lemma : (arr X ∘ eval′) ∘ first (p.p₂ X) ≈ π₂ ∘ first (p.p₁ X)
            lemma = λ-inj $ begin
              λg ((arr X ∘ eval′) ∘ first (p.p₂ X)) ≈˘⟨ subst ⟩
              λg (arr X ∘ eval′) ∘ p.p₂ X         ≈˘⟨ p.commute X ⟩
              λg π₂ ∘ p.p₁ X                      ≈⟨ subst ⟩
              λg (π₂ ∘ first (p.p₁ X))            ∎


