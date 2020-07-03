{-# OPTIONS --without-K --safe #-}

-- Some of the obvious properties of cartesian functors
module Categories.Functor.Cartesian.Properties where

open import Data.Product using (_,_; proj₁; proj₂)
open import Level

open import Categories.Category.Core using (Category)
open import Categories.Category.Cartesian
open import Categories.Category.Product using (Product; _⁂_)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Cartesian
open import Categories.Morphism.Reasoning
open import Categories.NaturalTransformation hiding (id)
import Categories.Object.Product as OP

private
  variable
    o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ : Level

idF-Cartesian : {A : Category o ℓ e} {CA : Cartesian A} → CartesianF CA CA idF
idF-Cartesian {A = A} {CA} = record
  { ε = id
  ; ⊗-homo = ntHelper record
    { η = λ _ → id
    ; commute = λ _ → id-comm-sym A }
  }
  where
  open Category A

∘-Cartesian : {A : Category o ℓ e} {B : Category o′ ℓ′ e′} {C : Category o″ ℓ″ e″}
  {CA : Cartesian A} {CB : Cartesian B} {CC : Cartesian C}
  {F : Functor B C} {G : Functor A B} (CF : CartesianF CB CC F) (CG : CartesianF CA CB G) → CartesianF CA CC (F ∘F G)
∘-Cartesian {B = B} {C} {CA} {CB} {CC} {F} {G} CF CG = record
  { ε = F.₁ CG.ε ∘ CF.ε
  ; ⊗-homo = ntHelper record
    { η = λ X → F.₁ (NTG.η X) ∘ NTF.η (Functor.F₀ (G ⁂ G) X)
    ; commute = λ { {A} {B} f →
      let GGA = F₀ (G ⁂ G) A in
      let GGB = F₀ (G ⁂ G) B in
      let GGf = F₁ (G ⁂ G) f in
      begin
      (F.₁ (NTG.η B) ∘ NTF.η GGB) ∘ F₁ (⊗ CC ∘F ((F ∘F G) ⁂ (F ∘F G))) f  ≈⟨ C.assoc ⟩
      F.₁ (NTG.η B) ∘ NTF.η GGB ∘ F₁ (⊗ CC ∘F ((F ∘F G) ⁂ (F ∘F G))) f    ≈⟨ (refl⟩∘⟨ NTF.commute GGf) ⟩
      F.₁ (NTG.η B) ∘ (F.₁ (F₁ (⊗ CB) GGf) ∘ NTF.η GGA)                   ≈⟨ C.sym-assoc ⟩
      (F.₁ (NTG.η B) ∘ F.₁ (F₁ (⊗ CB) GGf)) ∘ NTF.η GGA                   ≈˘⟨ (F.homomorphism ⟩∘⟨refl) ⟩
      (F.₁ (NTG.η B B.∘ F₁ (⊗ CB) GGf)) ∘ NTF.η GGA                       ≈⟨ (F.F-resp-≈ (NTG.commute f) ⟩∘⟨refl) ⟩
      F.F₁ (F₁ G (F₁ (⊗ CA) f) B.∘ NTG.η A) ∘ NTF.η GGA                   ≈⟨ (F.homomorphism ⟩∘⟨refl) ⟩
      (F₁ ((F ∘F G) ∘F ⊗ CA) f ∘ F.₁ (NTG.η A)) ∘ NTF.η GGA               ≈⟨ C.assoc ⟩
      F₁ ((F ∘F G) ∘F ⊗ CA) f ∘ F.₁ (NTG.η A) ∘ NTF.η GGA ∎}
    }
  }
  where
  module CF = CartesianF CF
  module CG = CartesianF CG
  module NTF = NaturalTransformation CF.⊗-homo
  module NTG = NaturalTransformation CG.⊗-homo
  module F = Functor F
  module B = Category B
  module C = Category C
  open C using (_≈_; _∘_)
  open C.HomReasoning
  open Cartesian CC using (products)
  open Functor
  open OP C using (Product)
  open Product
  open Cartesian using (⊗)
