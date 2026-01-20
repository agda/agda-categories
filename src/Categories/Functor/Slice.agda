{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)

module Categories.Functor.Slice {o ℓ e} (C : Category o ℓ e) where

open import Function.Base using (_$_) renaming (id to id→)

open import Categories.Category.BinaryProducts
open import Categories.Category.Cartesian
open import Categories.Category.CartesianClosed C
open import Categories.Diagram.Pullback C using (Pullback; unglue; Pullback-resp-≈)
open import Categories.Functor using (Functor)
open import Categories.Functor.Properties using ([_]-resp-∘)
open import Categories.Morphism.Reasoning C
open import Categories.Object.Exponential C
open import Categories.Object.Product C
open import Categories.Object.Terminal C

import Categories.Category.Slice as S
import Categories.Category.Construction.Pullbacks as Pbs
import Categories.Object.Product.Construction as ×C

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

  -- This can and probably should be restricted
  -- e.g. we only need exponential objects with A as domain
  -- I don't think we need all products but I don't have a clear idea of what products we do need
  module _ (ccc : CartesianClosed) (pullback : ∀ {X} {Y} {Z} (h : X ⇒ Z) (i : Y ⇒ Z) → Pullback h i) where

    open CartesianClosed ccc
    open Cartesian cartesian
    open Terminal terminal
    open BinaryProducts products

    InternalSections : Functor (Slice A) C
    InternalSections = record
      { F₀ = p.P
      ; F₁ = λ f → p.universal _ (F₁-lemma f)
      ; identity = λ {X} → sym $ p.unique X (sym (!-unique _)) $ begin
        p.p₂ X ∘ id                      ≈⟨ identityʳ ⟩
        p.p₂ X                           ≈˘⟨ η-exp′ ⟩
        λg (eval′ ∘ first (p.p₂ X))      ≈˘⟨ λ-cong (pullˡ identityˡ) ⟩
        λg (id ∘ eval′ ∘ first (p.p₂ X)) ∎
      ; homomorphism = λ {S} {T} {U} {f} {g} → sym $ p.unique U (sym (!-unique _)) $ begin
        p.p₂ U ∘ p.universal U (F₁-lemma g) ∘ p.universal T (F₁-lemma f) ≈⟨ pullˡ (p.p₂∘universal≈h₂ U) ⟩
        λg (h g ∘ eval′ ∘ first (p.p₂ T)) ∘ p.universal T (F₁-lemma f)   ≈˘⟨ pullˡ (subst ○ λ-cong assoc) ⟩
        λg (h g ∘ eval′) ∘ p.p₂ T ∘ p.universal T (F₁-lemma f)           ≈⟨ refl⟩∘⟨ p.p₂∘universal≈h₂ T ⟩
        λg (h g ∘ eval′) ∘ λg (h f ∘ eval′ ∘ first (p.p₂ S))             ≈⟨ subst ⟩
        λg ((h g ∘ eval′) ∘ first (λg (h f ∘ eval′ ∘ first (p.p₂ S))))   ≈⟨ λ-cong (pullʳ β′) ⟩
        λg (h g ∘ (h f ∘ eval′ ∘ first (p.p₂ S)))                        ≈⟨ λ-cong sym-assoc ⟩
        λg ((h g ∘ h f) ∘ eval′ ∘ first (p.p₂ S))                        ∎
      ; F-resp-≈ = λ f≈g → p.universal-resp-≈ _ refl (λ-cong (∘-resp-≈ˡ f≈g))
      }
      where
        p : (X : SliceObj A) → Pullback {X = ⊤} {Z = A ^ A} {Y = Y X ^ A} (λg π₂) (λg (arr X ∘ eval′))
        p X = pullback (λg π₂) (λg (arr X ∘ eval′))
        module p X = Pullback (p X)

        abstract
          F₁-lemma : ∀ {S} {T} (f : Slice⇒ S T) → λg π₂ ∘ ! ≈ λg (arr T ∘ eval′) ∘ λg (h f ∘ eval′ ∘ first (p.p₂ S))
          F₁-lemma {S} {T} f = λ-unique₂′ $ begin
            eval′ ∘ first (λg π₂ ∘ !)                                                      ≈˘⟨ refl⟩∘⟨ first∘first ⟩
            eval′ ∘ first (λg π₂) ∘ first !                                                ≈⟨ pullˡ β′ ⟩
            π₂ ∘ first !                                                                   ≈⟨ π₂∘⁂ ○ identityˡ ⟩
            π₂                                                                             ≈⟨ λ-inj lemma ⟩
            arr S ∘ eval′ ∘ first (p.p₂ S)                                                 ≈˘⟨ pullˡ (△ f) ⟩
            arr T ∘ h f ∘ eval′ ∘ first (p.p₂ S)                                           ≈˘⟨ pullʳ β′ ⟩
            (arr T ∘ eval′) ∘ first (λg (h f ∘ eval′ ∘ first (p.p₂ S)))                    ≈˘⟨ pullˡ β′ ⟩
            eval′ ∘ first (λg (arr T ∘ eval′)) ∘ first (λg (h f ∘ eval′ ∘ first (p.p₂ S))) ≈⟨ refl⟩∘⟨ first∘first ⟩
            eval′ ∘ first (λg (arr T ∘ eval′) ∘ λg (h f ∘ eval′ ∘ first (p.p₂ S)))         ∎
            where
              lemma : λg π₂ ≈ λg (arr S ∘ eval′ ∘ first (p.p₂ S))
              lemma = begin
                λg π₂                               ≈˘⟨ λ-cong (π₂∘⁂ ○ identityˡ) ⟩
                λg (π₂ ∘ first (p.p₁ S))            ≈˘⟨ subst ⟩
                λg π₂ ∘ p.p₁ S                      ≈⟨ p.commute S ⟩
                λg (arr S ∘ eval′) ∘ p.p₂ S         ≈⟨ subst ○ λ-cong assoc ⟩
                λg (arr S ∘ eval′ ∘ first (p.p₂ S)) ∎
