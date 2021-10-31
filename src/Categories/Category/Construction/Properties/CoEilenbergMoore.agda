{-# OPTIONS --without-K --safe #-}
-- verbatim dual of Categories.Category.Construction.Properties.EilenbergMoore
module Categories.Category.Construction.Properties.CoEilenbergMoore where

open import Level
import Relation.Binary.PropositionalEquality.Core as ≡

open import Categories.Adjoint
open import Categories.Adjoint.Properties
open import Categories.Category
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Equivalence
open import Categories.Comonad

open import Categories.NaturalTransformation.Core renaming (id to idN)
open import Categories.Morphism.HeterogeneousIdentity
open import Categories.Morphism.Reasoning

open import Categories.Adjoint.Construction.CoEilenbergMoore
open import Categories.Category.Construction.CoEilenbergMoore

private
  variable
    o ℓ e : Level
    𝒞 𝒟 : Category o ℓ e

module _ {F : Functor 𝒟 𝒞} {G : Functor 𝒞 𝒟} (F⊣G : Adjoint F G) where
  private
    T : Comonad 𝒞
    T = adjoint⇒comonad F⊣G

    coEM𝒞 : Category _ _ _
    coEM𝒞 = CoEilenbergMoore T

    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟
    module coEM𝒞 = Category coEM𝒞

    open 𝒞.HomReasoning

    module T = Comonad T
    module F = Functor F
    module G = Functor G
    module FG = Functor (F ∘F G)

    open Adjoint F⊣G
    open NaturalTransformation

  -- Maclane's Comparison Functor
  ComparisonF : Functor 𝒟 coEM𝒞
  ComparisonF = record
   { F₀ = λ X → record
    { A = F.F₀ X
    ; coaction = F.F₁ (unit.η X)
    ; commute = commute-obj
    ; identity = zig
    }
   ; F₁ = λ {A} {B} f → record
    { arr = F.F₁ f
    ; commute = commute-mor
    }
   ; identity = F.identity
   ; homomorphism = F.homomorphism
   ; F-resp-≈ = F.F-resp-≈
   }
   where
    commute-obj : {X : Category.Obj 𝒟} → T.F.F₁ (F.F₁ (unit.η X)) 𝒞.∘ F.F₁ (unit.η X) 𝒞.≈ T.δ.η (F.F₀ X) 𝒞.∘ F.F₁ (unit.η X)
    commute-obj {X} = begin
      F.F₁ (G.F₁ (F.F₁ (unit.η X))) 𝒞.∘ F.F₁ (unit.η X) ≈⟨ Category.Equiv.sym 𝒞 (Functor.homomorphism F) ⟩
      F.F₁ (G.F₁ (F.F₁ (unit.η X)) 𝒟.∘ unit.η X)        ≈⟨ Functor.F-resp-≈ F (Category.Equiv.sym 𝒟 (Adjoint.unit.commute F⊣G (unit.η X))) ⟩
      F.F₁ (unit.η (G.F₀ (F.F₀ X)) 𝒟.∘ unit.η X)        ≈⟨ Functor.homomorphism F ⟩
      T.δ.η (F.F₀ X) 𝒞.∘ F.F₁ (unit.η X)                ∎
    commute-mor : {A B : Category.Obj 𝒟} {f : Category._⇒_ 𝒟 A B} → F.F₁ (unit.η B) 𝒞.∘ F.F₁ f 𝒞.≈ T.F.F₁ (F.F₁ f) 𝒞.∘ F.F₁ (unit.η A)
    commute-mor {A} {B} {f} = begin
     F.F₁ (unit.η B) 𝒞.∘ F.F₁ f          ≈⟨ Category.Equiv.sym 𝒞 (Functor.homomorphism F) ⟩
     F.F₁ (unit.η B 𝒟.∘ f)               ≈⟨ Functor.F-resp-≈ F (Adjoint.unit.commute F⊣G f) ⟩
     F.F₁ (G.F₁ (F.F₁ f) 𝒟.∘ unit.η A)   ≈⟨ Functor.homomorphism F ⟩
     T.F.F₁ (F.F₁ f) 𝒞.∘ F.F₁ (unit.η A) ∎


  private
    K = ComparisonF
    module K = Functor K
    module Fᵀ = Functor (Forgetful T)
    module Gᵀ = Functor (Cofree T)

  Comparison∘F≡Free : (ComparisonF ∘F G) ≡F Cofree T
  Comparison∘F≡Free = record
   { eq₀ = λ X → {!   !}
   ; eq₁ = {!   !}
   }
{-
  record
    { eq₀ = λ X → ≡.refl
    ; eq₁ = λ {A} {B} f → begin
      Module⇒.arr (coEM𝒞 [ (hid coEM𝒞 ≡.refl) ∘ K.F₁ (F.F₁ f) ]) ≈⟨ hid-refl coEM𝒞 {A = K.F₀ (F.F₀ B)} ⟩∘⟨refl ⟩
      Module⇒.arr (coEM𝒞 [ coEM𝒞.id ∘ K.F₁ (F.F₁ f) ])           ≈⟨ 𝒞.identityˡ {f = Module⇒.arr (K.F₁ (F.F₁ f))} ⟩
      Module⇒.arr (K.F₁ (F.F₁ f))                          ≈⟨ 𝒞.Equiv.refl ⟩
      Module⇒.arr (Fᵀ.F₁ f)                                 ≈˘⟨ coEM𝒞.identityʳ {f = Fᵀ.F₁ f} ⟩
      Module⇒.arr (coEM𝒞 [ Fᵀ.F₁ f ∘ coEM𝒞.id ])                 ≈˘⟨ refl⟩∘⟨ hid-refl coEM𝒞 {A = Fᵀ.F₀ A} ⟩
      Module⇒.arr (coEM𝒞 [ Fᵀ.F₁ f ∘ (hid coEM𝒞 ≡.refl) ])       ∎
    }
-}

  Forgetful∘ComparisonF≡G : (Forgetful T ∘F ComparisonF) ≡F F
  Forgetful∘ComparisonF≡G = record
   { eq₀ = λ X → ≡.refl
   ; eq₁ = eq-1
   }
   where
     eq-1 : {X Y : 𝒟.Obj} (f : X 𝒟.⇒ Y) → 𝒞.id 𝒞.∘ F.F₁ f 𝒞.≈ F.F₁ f 𝒞.∘ 𝒞.id
     eq-1 = λ f → begin
       𝒞.id 𝒞.∘ F.F₁ f ≈⟨ id-comm-sym 𝒞 ⟩
       F.F₁ f 𝒞.∘ 𝒞.id ∎
{-
  record
    { eq₀ = λ X → ≡.refl
    ; eq₁ = λ f → begin
      𝒞 [ (hid 𝒞 ≡.refl) ∘ (Gᵀ.F₁ (K.F₁ f)) ] ≈⟨ hid-refl 𝒞 ⟩∘⟨refl ⟩
      𝒞 [ 𝒞.id ∘ (Gᵀ.F₁ (K.F₁ f)) ]           ≈⟨ 𝒞.identityˡ ⟩
      (Gᵀ.F₁ (K.F₁ f))                         ≈⟨ 𝒞.Equiv.refl ⟩
      G.F₁ f                                   ≈˘⟨ 𝒞.identityʳ ⟩
      𝒞 [ G.F₁ f ∘ 𝒞.id ]                     ≈˘⟨ refl⟩∘⟨ hid-refl 𝒞 ⟩
      𝒞 [ G.F₁ f ∘ (hid 𝒞 ≡.refl) ]           ∎
    }
-}