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

  Forgetful : Functor (Slice A) C
  Forgetful = record
    { F₀           = Y
    ; F₁           = h
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = id→
    }

  module _ (pullback : ∀ {X} {Y} {Z} (h : X ⇒ Z) (i : Y ⇒ Z) → Pullback h i) where
    private
      module pullbacks {X Y Z} h i = Pullback (pullback {X} {Y} {Z} h i)
      open pullbacks using (p₂; p₂∘universal≈h₂; unique; unique-diagram; p₁∘universal≈h₁)

    pullback-functorial : ∀ {B} (f : B ⇒ A) → Functor (Slice A) (Slice B)
    pullback-functorial f = record
      { F₀ = λ X → S.sliceobj (p.p₁ X)
      ; F₁ = λ f → S.slicearr {h = p⇒.pbarr _ _ f} (p.p₁∘universal≈h₁ _ ○ identityˡ)
      ; identity = sym $ p.unique _ id-comm id-comm
      ; homomorphism = p.unique-diagram _ homomorphism-lemmaˡ homomorphism-lemmaʳ
      ; F-resp-≈ = λ {_ B} {h i} eq → p.unique-diagram B F-resp-≈-lemmaˡ (F-resp-≈-lemmaʳ eq)
      }
      where
        p : ∀ X → Pullback f (arr X)
        p X = pullback f (arr X)
        module p X = Pullback (p X)

        p⇒ : ∀ X Y (g : Slice⇒ X Y) → Pbs.Pullback⇒ C A _ _
        p⇒ X Y g = pX⇒pY
          where
            pX : Pbs.PullbackObj C A
            pX = record { pullback = p X }
            pY : Pbs.PullbackObj C A
            pY = record { pullback = p Y }
            pX⇒pY : Pbs.Pullback⇒ C A pX pY
            pX⇒pY = record
              { mor₁     = Category.id C
              ; mor₂     = h g
              ; commute₁ = identityʳ
              ; commute₂ = △ g
              }

        module p⇒ X Y g = Pbs.Pullback⇒ (p⇒ X Y g)

        homomorphism-lemmaˡ : ∀ {X Y Z α β} → p.p₁ Z ∘ p⇒.pbarr X Z _ ≈ p.p₁ Z ∘ p⇒.pbarr Y Z β ∘ p⇒.pbarr X Y α
        homomorphism-lemmaˡ {X} {Y} {Z} {α} {β} = begin
          p.p₁ Z ∘ p⇒.pbarr X Z _                  ≈⟨ p.p₁∘universal≈h₁ Z ⟩
          id ∘ p.p₁ X                              ≈˘⟨ identityˡ ⟩
          id ∘ id ∘ p.p₁ X                         ≈˘⟨ pullʳ (p.p₁∘universal≈h₁ Y) ⟩
          (id ∘ p.p₁ Y) ∘ p⇒.pbarr X Y α           ≈˘⟨ pullˡ (p.p₁∘universal≈h₁ Z) ⟩
          p.p₁ Z ∘ p⇒.pbarr Y Z β ∘ p⇒.pbarr X Y α ∎

        homomorphism-lemmaʳ : ∀ {X Y Z α β} → p.p₂ Z ∘ p⇒.pbarr X Z _ ≈ p.p₂ Z ∘ p⇒.pbarr Y Z β ∘ p⇒.pbarr X Y α
        homomorphism-lemmaʳ {X} {Y} {Z} {α} {β} = begin
          p.p₂ Z ∘ p⇒.pbarr X Z _                  ≈⟨ p.p₂∘universal≈h₂ Z ⟩
          (h β ∘ h α) ∘ p.p₂ X                     ≈˘⟨ glue′ (p.p₂∘universal≈h₂ Z) (p.p₂∘universal≈h₂ Y) ⟩
          p.p₂ Z ∘ p⇒.pbarr Y Z β ∘ p⇒.pbarr X Y α ∎

        F-resp-≈-lemmaˡ : ∀ {A B} {α β : Slice⇒ A B} → p.p₁ B ∘ p⇒.pbarr A B α ≈ p.p₁ B ∘ p⇒.pbarr A B β
        F-resp-≈-lemmaˡ {A} {B} {α} {β} = begin
          p.p₁ B ∘ p⇒.pbarr A B α ≈⟨ p.p₁∘universal≈h₁ B ⟩
          id ∘ p.p₁ A             ≈˘⟨ p.p₁∘universal≈h₁ B ⟩
          p.p₁ B ∘ p⇒.pbarr A B β ∎

        F-resp-≈-lemmaʳ : ∀ {A B} {α β : Slice⇒ A B} → h α ≈ h β → p.p₂ B ∘ p⇒.pbarr A B α ≈ p.p₂ B ∘ p⇒.pbarr A B β
        F-resp-≈-lemmaʳ {A} {B} {α} {β} eq = begin
          p.p₂ B ∘ p⇒.pbarr A B α ≈⟨ p.p₂∘universal≈h₂ B ⟩
          h α ∘ p.p₂ A            ≈⟨ eq ⟩∘⟨refl ⟩
          h β ∘ p.p₂ A            ≈˘⟨ p.p₂∘universal≈h₂ B ⟩
          p.p₂ B ∘ p⇒.pbarr A B β ∎

  module _ (product : {X : Obj} → Product A X) where

    private
      module product {X} = Product (product {X})
      open product

    -- this is adapted from proposition 1.33 of Aspects of Topoi (Freyd, 1972)
    Free : Functor C (Slice A)
    Free = record
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

    -- Needs better name!
    Coforgetful : Functor (Slice A) C
    Coforgetful = record
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
