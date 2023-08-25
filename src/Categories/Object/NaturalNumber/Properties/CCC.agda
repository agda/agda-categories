{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Object.Terminal hiding (up-to-iso)
open import Categories.Category.CartesianClosed.Bundle
open import Categories.Category.Cartesian
open import Categories.Category.BinaryProducts
open import Categories.Category.Cocartesian
open import Categories.Category.CartesianClosed
open import Categories.Object.NaturalNumber.Properties.F-Algebras
open import Categories.Object.Initial
open import Categories.Category.Construction.F-Algebras

module Categories.Object.NaturalNumber.Properties.CCC {o ℓ e} (CCC : CartesianClosedCategory o ℓ e) (𝒞-Coproducts : BinaryCoproducts (CartesianClosedCategory.U CCC)) where

open import Level

open CartesianClosedCategory CCC renaming (U to 𝒞)
open CartesianClosed cartesianClosed
open Cartesian cartesian
open BinaryProducts products
open BinaryCoproducts 𝒞-Coproducts

open import Categories.Object.NaturalNumber 𝒞 terminal
open import Categories.Object.NaturalNumber.Parametrized cartesianCategory
open import Categories.Morphism 𝒞
open import Categories.Morphism.Reasoning 𝒞
open import Categories.Functor.Algebra


open HomReasoning
open Equiv

open Terminal terminal

NNO×CCC⇒PNNO : NaturalNumber → ParametrizedNaturalNumber
NNO×CCC⇒PNNO nno = record 
  { N = N 
  ; isParametrizedNaturalNumber = record
    { z = z
    ; s = s
    ; universal = λ {A} {X} f g → (eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ⁂ id)) ∘ swap
    ; commute₁ = λ {A} {X} {f} {g} → begin 
      f ≈˘⟨ identityʳ ⟩ 
      f ∘ id ≈˘⟨ pullʳ project₂ ⟩
      (f ∘ π₂) ∘ ⟨ ! , id ⟩ ≈˘⟨ pullˡ β′ ⟩
      eval′ ∘ (λg (f ∘ π₂) ⁂ id) ∘ ⟨ ! , id ⟩ ≈⟨ refl⟩∘⟨ ⁂∘⟨⟩ ⟩
      eval′ ∘ ⟨ λg (f ∘ π₂) ∘ ! , id ∘ id ⟩ ≈˘⟨ refl⟩∘⟨ (⟨⟩-congʳ (pullˡ (sym z-commute))) ⟩
      eval′ ∘ ⟨ universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ∘ z ∘ ! , id ∘ id ⟩ ≈˘⟨ pullʳ ⁂∘⟨⟩ ⟩
      (eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ⁂ id)) ∘ ⟨ z ∘ ! , id ⟩ ≈˘⟨ pullʳ swap∘⟨⟩ ⟩
      ((eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ⁂ id)) ∘ swap) ∘ ⟨ id , z ∘ ! ⟩ ∎
    ; commute₂ = λ {A} {X} {f} {g} → begin 
      g ∘ (eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ⁂ id)) ∘ swap ≈⟨ sym-assoc ⟩ 
      (g ∘ (eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ⁂ id))) ∘ swap ≈⟨ sym-assoc ⟩∘⟨refl ⟩
      ((g ∘ eval′) ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ⁂ id)) ∘ swap ≈˘⟨ (pullˡ β′) ⟩∘⟨refl ⟩
      (eval′ ∘ ((λg (g ∘ eval′) ⁂ id) ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ⁂ id))) ∘ swap ≈⟨ (refl⟩∘⟨ ⁂∘⁂) ⟩∘⟨refl ⟩
      (eval′ ∘ (λg (g ∘ eval′) ∘ universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ⁂ id ∘ id)) ∘ swap ≈˘⟨ (refl⟩∘⟨ (⟨⟩-congʳ (∘-resp-≈ˡ (sym s-commute)))) ⟩∘⟨refl ⟩
      (eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ∘ s ⁂ id ∘ id)) ∘ swap ≈˘⟨ pullˡ (pullʳ ⁂∘⁂) ⟩
      (eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ⁂ id)) ∘ (s ⁂ id) ∘ swap ≈˘⟨ pullʳ (swap∘⁂) ⟩
      ((eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ⁂ id)) ∘ swap) ∘ (id ⁂ s) ∎
    ; unique = λ {A} {X} {f} {g} {u} eqᶻ eqˢ → swap-prop (λ-rev (begin 
      λg (u ∘ swap) ≈⟨ nno-unique (sym (λ-unique′ 
      (begin 
        eval′ ∘ (λg (u ∘ swap) ∘ z ⁂ id) ≈⟨ refl⟩∘⟨ (sym (trans ⁂∘⁂ (⁂-cong₂ refl identity²))) ⟩ 
        eval′ ∘ (λg (u ∘ swap) ⁂ id) ∘ (z ⁂ id) ≈⟨ pullˡ β′ ⟩
        (u ∘ swap) ∘ (z ⁂ id) ≈⟨ pullʳ swap∘⁂ ⟩
        u ∘ (id ⁂ z) ∘ swap ≈⟨ pushʳ (unique′ 
        (begin 
          π₁ ∘ (id ⁂ z) ∘ swap ≈⟨ pullˡ project₁ ⟩ 
          (id ∘ π₁) ∘ swap ≈⟨ pullʳ project₁ ⟩ 
          id ∘ π₂ ≈˘⟨ pullˡ project₁ ⟩ 
          π₁ ∘ ⟨ id , z ∘ ! ⟩ ∘ π₂ ∎) 
        (trans (pullˡ project₂) (trans (pullʳ project₂) (trans (sym (pullʳ !-unique₂)) (sym (pullˡ project₂)))))) ⟩
        (u ∘ ⟨ id , z ∘ ! ⟩) ∘ π₂ ≈⟨ sym (∘-resp-≈ˡ eqᶻ) ⟩
        f ∘ π₂ ∎))) 
      (begin 
        λg (g ∘ eval′) ∘ λg (u ∘ swap) ≈⟨ exp.subst product product ⟩ 
        λg ((g ∘ eval′) ∘ (λg (u ∘ swap) ⁂ id)) ≈⟨ λ-cong (pullʳ β′) ⟩
        λg (g ∘ u ∘ swap) ≈⟨ λ-cong (pullˡ eqˢ) ⟩
        λg ((u ∘ (id ⁂ s)) ∘ swap) ≈⟨ λ-cong (trans (pullʳ (sym swap∘⁂)) sym-assoc) ⟩
        λg ((u ∘ swap) ∘ (s ⁂ id)) ≈˘⟨ exp.subst product product ⟩
        λg (u ∘ swap) ∘ s ∎) ⟩ 
      universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ≈˘⟨ η-exp′ ⟩
      λg (eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ⁂ id)) ≈˘⟨ λ-cong (cancelʳ swap∘swap) ⟩
      λg (((eval′ ∘ (universal (λg (f ∘ π₂)) (λg (g ∘ eval′)) ⁂ id)) ∘ swap) ∘ swap) ∎))
    } 
  }
  where
    open NaturalNumber nno renaming (unique to nno-unique)
    open Initial (NNO⇒Initial 𝒞 terminal 𝒞-Coproducts nno) using (⊥) renaming (! to ¡)
    λg' : ∀ {A B C} → A × C ⇒ B → C ⇒ B ^ A
    λg' = λ g → λg (g ∘ swap)
    λ-rev : ∀ {A B C} {f g : C × A ⇒ B} → λg f ≈ λg g → f ≈ g
    λ-rev {f = f} {g = g} eq = trans (sym β′) (trans (∘-resp-≈ʳ (⟨⟩-congʳ (∘-resp-≈ˡ eq))) β′) 
    swap-prop : ∀ {A B C : Obj} {f g : A × B ⇒ C} → f ∘ swap ≈ g ∘ swap → f ≈ g
    swap-prop {A} {B} {C} {f} {g} eq = trans ( introʳ swap∘swap) (trans (pullˡ eq) (cancelʳ swap∘swap))
    -- λg'-prop : ∀ {A B C} {f : } {g : } → λg' f ≈ λg' g → f ≈ g
    -- λg'-prop = {!   !}

-- NNO×CCC⇒PNNO : NaturalNumber → ParametrizedNaturalNumber
-- NNO×CCC⇒PNNO nno = Initial⇒PNNO cartesianCategory 𝒞-Coproducts ⊥ λ A → record 
--   { ! = λ {X} → !' A X
--   ; !-unique = λ f → {! sym nno-unique  !}
--   }
--   where
--     open NaturalNumber nno renaming (unique to nno-unique)
--     open Initial (NNO⇒Initial 𝒞 terminal 𝒞-Coproducts nno) using (⊥) renaming (! to ¡)
--     !' : ∀ (A : Obj) (algebra : F-Algebra (coproductF cartesianCategory 𝒞-Coproducts A)) → F-Algebra-Morphism  (PNNO-Algebra cartesianCategory 𝒞-Coproducts A (F-Algebra.A ⊥) (F-Algebra.α ⊥ ∘ i₁) (F-Algebra.α ⊥ ∘ i₂)) algebra
--     !' A algebra = record 
--       { f = (eval′ ∘ (F-Algebra-Morphism.f (¡ {A = alg}) ⁂ id)) ∘ swap 
--       ; commutes = begin 
--         ((eval′ ∘ (F-Algebra-Morphism.f (¡ {A = alg}) ⁂ id)) ∘ swap) ∘ [ ⟨ id , ([ z , s ] ∘ i₁) ∘ ! ⟩ , id ⁂ ([ z , s ] ∘ i₂) ]                                                                                                                                               ≈⟨ pullʳ (⟺ swap∘⁂) ⟩∘⟨refl ⟩ 
--         ((eval′ ∘ (swap ∘ (id ⁂ F-Algebra-Morphism.f (¡ {A = alg}))))) ∘ [ ⟨ id , ([ z , s ] ∘ i₁) ∘ ! ⟩ , id ⁂ ([ z , s ] ∘ i₂) ]                                                                                                                                             ≈⟨ pullʳ (pullʳ ∘[]) ⟩
--         eval′ ∘ swap ∘ [ (id ⁂ F-Algebra-Morphism.f (¡ {A = alg})) ∘ ⟨ id , ([ z , s ] ∘ i₁) ∘ ! ⟩ , (id ⁂ F-Algebra-Morphism.f (¡ {A = alg})) ∘ (id ⁂ ([ z , s ] ∘ i₂)) ]                                                                                             ≈⟨ refl⟩∘⟨ refl⟩∘⟨ []-cong₂ ⁂∘⟨⟩ ⁂∘⁂ ⟩
--         eval′ ∘ swap ∘ [ ⟨ id ∘ id , F-Algebra-Morphism.f (¡ {A = alg}) ∘ ([ z , s ] ∘ i₁) ∘ ! ⟩ , (id ∘ id ⁂ F-Algebra-Morphism.f (¡ {A = alg}) ∘ ([ z , s ] ∘ i₂)) ]                                                                                                 ≈⟨ refl⟩∘⟨ refl⟩∘⟨ []-cong₂ (⟨⟩-cong₂ identity² (pullˡ (pullˡ (F-Algebra-Morphism.commutes ¡)))) (⟨⟩-cong₂ (∘-resp-≈ˡ identity²) (∘-resp-≈ˡ (pullˡ (F-Algebra-Morphism.commutes ¡)))) ⟩
--         eval′ ∘ swap ∘ [ ⟨ id , (([ (λg (α ∘ i₁ ∘ π₂)) , λg (α ∘ i₂ ∘ eval′) ] ∘ [ i₁ , i₂ ∘ F-Algebra-Morphism.f (¡ {A = alg})]) ∘ i₁) ∘ ! ⟩ , id ⁂ (([ (λg (α ∘ i₁ ∘ π₂)) , λg (α ∘ i₂ ∘ eval′) ] ∘ [ i₁ , i₂ ∘ F-Algebra-Morphism.f (¡ {A = alg})]) ∘ i₂) ] ≈⟨ refl⟩∘⟨ refl⟩∘⟨ []-cong₂ (⟨⟩-congˡ (∘-resp-≈ˡ (pullʳ inject₁))) (⟨⟩-congˡ (∘-resp-≈ˡ (pullʳ inject₂))) ⟩
--         eval′ ∘ swap ∘ [ ⟨ id , ([ (λg (α ∘ i₁ ∘ π₂)) , λg (α ∘ i₂ ∘ eval′) ] ∘ i₁) ∘ ! ⟩ , id ⁂ ([ (λg (α ∘ i₁ ∘ π₂)) , λg (α ∘ i₂ ∘ eval′) ] ∘ i₂ ∘ F-Algebra-Morphism.f (¡ {A = alg})) ]                                                                            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ []-cong₂ (⟨⟩-congˡ (∘-resp-≈ˡ inject₁)) (⟨⟩-congˡ (∘-resp-≈ˡ (pullˡ inject₂))) ⟩
--         eval′ ∘ swap ∘ [ ⟨ id , λg (α ∘ i₁ ∘ π₂) ∘ ! ⟩ , id ⁂ (λg (α ∘ i₂ ∘ eval′) ∘ F-Algebra-Morphism.f (¡ {A = alg})) ]                                                                                                                                                 ≈⟨ trans sym-assoc ∘[] ⟩
--         [ (eval′ ∘ swap) ∘ ⟨ id , λg (α ∘ i₁ ∘ π₂) ∘ ! ⟩ , (eval′ ∘ swap) ∘ (id ⁂ (λg (α ∘ i₂ ∘ eval′) ∘ F-Algebra-Morphism.f (¡ {A = alg}))) ]                                                                                                                            ≈⟨ []-cong₂ (pullʳ swap∘⟨⟩) (pullʳ swap∘⁂) ⟩
--         [ eval′ ∘ ⟨ λg (α ∘ i₁ ∘ π₂) ∘ ! , id ⟩ , eval′ ∘ ((λg (α ∘ i₂ ∘ eval′) ∘ F-Algebra-Morphism.f (¡ {A = alg})) ⁂ id) ∘ swap ]                                                                                                                                       ≈˘⟨ []-cong₂ (∘-resp-≈ʳ (⁂∘⟨⟩ ○ ⟨⟩-congˡ identity²)) (refl⟩∘⟨ ((⁂∘⁂ ○ ⟨⟩-congˡ ((∘-resp-≈ˡ identity²))) ⟩∘⟨refl)) ⟩ -- ∘-resp-≈ʳ (⁂∘⟨⟩ ○ ⟨⟩-congˡ identity²)
--         [ eval′ ∘ (λg (α ∘ i₁ ∘ π₂) ⁂ id) ∘ ⟨ ! , id ⟩ , eval′ ∘ ((λg (α ∘ i₂ ∘ eval′) ⁂ id) ∘ ((F-Algebra-Morphism.f (¡ {A = alg})) ⁂ id)) ∘ swap ] ≈⟨ []-cong₂ (pullˡ β′) (pullˡ (pullˡ β′)) ⟩
--         [ (α ∘ i₁ ∘ π₂) ∘ ⟨ ! , id ⟩ , ((α ∘ i₂ ∘ eval′) ∘ ((F-Algebra-Morphism.f (¡ {A = alg})) ⁂ id)) ∘ swap ] ≈⟨ []-cong₂ assoc (assoc ○ assoc) ○ ⟺ ∘[] ⟩
--         α ∘ [ (i₁ ∘ π₂) ∘ ⟨ ! , id ⟩ , (i₂ ∘ eval′) ∘ ((F-Algebra-Morphism.f (¡ {A = alg})) ⁂ id) ∘ swap ] ≈⟨ refl⟩∘⟨ []-cong₂ (pullʳ project₂) assoc ⟩
--         α ∘ [ i₁ ∘ id , i₂ ∘ eval′ ∘ ((F-Algebra-Morphism.f (¡ {A = alg})) ⁂ id) ∘ swap ] ≈⟨ refl⟩∘⟨ []-cong₂ identityʳ (∘-resp-≈ʳ sym-assoc) ⟩
--         α ∘ [ i₁ , i₂ ∘ (eval′ ∘ (F-Algebra-Morphism.f (¡ {A = alg}) ⁂ id)) ∘ swap ] ∎
--       }
--       where
--         open F-Algebra algebra renaming (A to X)
--         alg : F-Algebra (Maybe 𝒞 terminal 𝒞-Coproducts)
--         alg = record 
--           { A = X ^ A 
--           ; α = [ (λg (α ∘ i₁ ∘ π₂)) , λg (α ∘ i₂ ∘ eval′) ] 
--           }
--     !-unique' : ∀ (A : Obj) (algebra : F-Algebra (coproductF cartesianCategory 𝒞-Coproducts A)) → (f : F-Algebra-Morphism  (PNNO-Algebra cartesianCategory 𝒞-Coproducts A (F-Algebra.A ⊥) (F-Algebra.α ⊥ ∘ i₁) (F-Algebra.α ⊥ ∘ i₂)) algebra) → (F-Algebras (coproductF cartesianCategory 𝒞-Coproducts A)) [ !' A algebra ≈ f ]
--     !-unique' A algebra f = begin 
--       (eval′ ∘ (universal _ _ ⁂ id)) ∘ swap ≈⟨ {! F-Algebra-Morphism.commutes f  !} ⟩ 
--       F-Algebra-Morphism.f f ∎
--       where
--         open F-Algebra algebra renaming (A to X)
--         alg : F-Algebra (Maybe 𝒞 terminal 𝒞-Coproducts)
--         alg = record 
--           { A = X ^ A 
--           ; α = [ (λg (α ∘ i₁ ∘ π₂)) , λg (α ∘ i₂ ∘ eval′) ] 
--           }