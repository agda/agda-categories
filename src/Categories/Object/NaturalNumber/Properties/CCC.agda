{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core
open import Categories.Object.Terminal hiding (up-to-iso)
open import Categories.Category.CartesianClosed.Bundle
open import Categories.Category.Cartesian
open import Categories.Category.BinaryProducts
open import Categories.Category.Cocartesian
open import Categories.Category.CartesianClosed
open import Categories.Object.NaturalNumber.Properties.F-Algebras
open import Categories.Object.Initial

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
NNO×CCC⇒PNNO nno = Initial⇒PNNO cartesianCategory 𝒞-Coproducts (NNO⇒Initial 𝒞 terminal 𝒞-Coproducts nno) λ A → record 
  { ! = λ {X} → 
    let 
      module X = F-Algebra X
      alg : F-Algebra (Maybe 𝒞 terminal 𝒞-Coproducts)
      alg = record 
        { A = X.A ^ A 
        ; α = [ (λg (X.α ∘ i₁ ∘ π₂)) , λg (X.α ∘ i₂ ∘ eval′) ] 
        }
    in record { f = (eval′ ∘ (F-Algebra-Morphism.f (initial.! {A = alg}) ⁂ id)) ∘ swap ; commutes = begin 
      ((eval′ ∘ (F-Algebra-Morphism.f (initial.! {A = alg}) ⁂ id)) ∘ swap) ∘ [ ⟨ id , ([ z , s ] ∘ i₁) ∘ ! ⟩ , id ⁂ ([ z , s ] ∘ i₂) ] ≈⟨ pullʳ (⟺ swap∘⁂) ⟩∘⟨refl ⟩ 
      ((eval′ ∘ (swap ∘ (id ⁂ F-Algebra-Morphism.f (initial.! {A = alg}))))) ∘ [ ⟨ id , ([ z , s ] ∘ i₁) ∘ ! ⟩ , id ⁂ ([ z , s ] ∘ i₂) ] ≈⟨ pullʳ (pullʳ ∘[]) ⟩
      eval′ ∘ swap ∘ [ (id ⁂ F-Algebra-Morphism.f (initial.! {A = alg})) ∘ ⟨ id , ([ z , s ] ∘ i₁) ∘ ! ⟩ , (id ⁂ F-Algebra-Morphism.f (initial.! {A = alg})) ∘ (id ⁂ ([ z , s ] ∘ i₂)) ] ≈⟨ refl⟩∘⟨ refl⟩∘⟨ []-cong₂ ⁂∘⟨⟩ ⁂∘⁂ ⟩
      eval′ ∘ swap ∘ [ ⟨ id ∘ id , F-Algebra-Morphism.f (initial.! {A = alg}) ∘ ([ z , s ] ∘ i₁) ∘ ! ⟩ , (id ∘ id ⁂ F-Algebra-Morphism.f (initial.! {A = alg}) ∘ ([ z , s ] ∘ i₂)) ] ≈⟨ refl⟩∘⟨ refl⟩∘⟨ []-cong₂ (⟨⟩-cong₂ identity² (pullˡ (pullˡ (F-Algebra-Morphism.commutes initial.!)))) (⟨⟩-cong₂ (∘-resp-≈ˡ identity²) (∘-resp-≈ˡ (pullˡ (F-Algebra-Morphism.commutes initial.!)))) ⟩
      eval′ ∘ swap ∘ [ ⟨ id , (([ (λg (X.α ∘ i₁ ∘ π₂)) , λg (X.α ∘ i₂ ∘ eval′) ] ∘ [ i₁ , i₂ ∘ F-Algebra-Morphism.f (initial.! {A = alg})]) ∘ i₁) ∘ ! ⟩ , id ⁂ (([ (λg (X.α ∘ i₁ ∘ π₂)) , λg (X.α ∘ i₂ ∘ eval′) ] ∘ [ i₁ , i₂ ∘ F-Algebra-Morphism.f (initial.! {A = alg})]) ∘ i₂) ] ≈⟨ refl⟩∘⟨ refl⟩∘⟨ []-cong₂ (⟨⟩-congˡ (∘-resp-≈ˡ (pullʳ inject₁))) (⟨⟩-congˡ (∘-resp-≈ˡ (pullʳ inject₂))) ⟩
      eval′ ∘ swap ∘ [ ⟨ id , ([ (λg (X.α ∘ i₁ ∘ π₂)) , λg (X.α ∘ i₂ ∘ eval′) ] ∘ i₁) ∘ ! ⟩ , id ⁂ ([ (λg (X.α ∘ i₁ ∘ π₂)) , λg (X.α ∘ i₂ ∘ eval′) ] ∘ i₂ ∘ F-Algebra-Morphism.f (initial.! {A = alg})) ] ≈⟨ refl⟩∘⟨ refl⟩∘⟨ []-cong₂ (⟨⟩-congˡ (∘-resp-≈ˡ inject₁)) (⟨⟩-congˡ (∘-resp-≈ˡ (pullˡ inject₂))) ⟩
      eval′ ∘ swap ∘ [ ⟨ id , λg (X.α ∘ i₁ ∘ π₂) ∘ ! ⟩ , id ⁂ (λg (X.α ∘ i₂ ∘ eval′) ∘ F-Algebra-Morphism.f (initial.! {A = alg})) ] ≈⟨ trans sym-assoc ∘[] ⟩
      [ (eval′ ∘ swap) ∘ ⟨ id , λg (X.α ∘ i₁ ∘ π₂) ∘ ! ⟩ , (eval′ ∘ swap) ∘ (id ⁂ (λg (X.α ∘ i₂ ∘ eval′) ∘ F-Algebra-Morphism.f (initial.! {A = alg}))) ] ≈⟨ []-cong₂ (pullʳ swap∘⟨⟩) (pullʳ swap∘⁂) ⟩
      [ eval′ ∘ ⟨ λg (X.α ∘ i₁ ∘ π₂) ∘ ! , id ⟩ , eval′ ∘ ((λg (X.α ∘ i₂ ∘ eval′) ∘ F-Algebra-Morphism.f (initial.! {A = alg})) ⁂ id) ∘ swap ] ≈⟨ {!   !} ⟩
      {!   !} ≈⟨ {!   !} ⟩
      {!   !} ≈⟨ {!   !} ⟩
      -- TODO right side is eval ∘ λg, can be simplified, left side idk
      X.α ∘ [ i₁ , i₂ ∘ (eval′ ∘ (F-Algebra-Morphism.f (initial.! {A = alg}) ⁂ id)) ∘ swap ] ∎ } 
  ; !-unique = {!   !} 
  }
  where
    open NaturalNumber nno
    module initial = Initial (NNO⇒Initial 𝒞 terminal 𝒞-Coproducts nno)
    module ⊥ = F-Algebra initial.⊥
    -- alg : ∀ X → F-Algebra (Maybe 𝒞 terminal 𝒞-Coproducts)
    -- alg X = record 
    --   { A = X ^ ⊥.A 
    --   ; α = [ (λg {! ⊥.α ∘ i₁ ∘ π₁  !}) , {!   !} ] 
    --   }

-- ([ (λg (X.α ∘ i₁ ∘ π₂)) , λg (X.α ∘ i₂ ∘ eval′) ] ∘ (id +₁ F-Algebra-Morphism.f (initial.! {A = alg})))
-- ([ (λg (X.α ∘ i₁ ∘ π₂)) , λg (X.α ∘ i₂ ∘ eval′) ] ∘ [ i₁ , i₂ ∘ F-Algebra-Morphism.f (initial.! {A = alg})])