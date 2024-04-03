{-# OPTIONS --without-K --safe #-}

module Categories.Comonad.Construction.CoKleisli where

-- Definition of kleisli cotriple as a relative comonad
-- and the equivalence of kleisli cotriple and comonad
-- mostly dual to Categories.Monad.Construction.Kleisli

open import Level
open import Categories.Category.Core using (Category)
open import Categories.Comonad.Relative using (RComonad⇒Functor) renaming (Comonad to RComonad)
open import Categories.Comonad using (Comonad)
open import Categories.Functor using (Functor; Endofunctor; _∘F_) renaming (id to idF)
open import Categories.NaturalTransformation using (ntHelper; NaturalTransformation)
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level

module _ (C : Category o ℓ e) where
  open Category C
  open HomReasoning
  open Equiv
  open MR C

  -- a kleisli cotriple is a relative monad with J = idF
  KleisliCotriple : Set (o ⊔ ℓ ⊔ e)
  KleisliCotriple = RComonad {C = C} idF

  -- kleisli cotriples are equivalent to comonads
  Kleisli⇒Comonad : KleisliCotriple → Comonad C
  Kleisli⇒Comonad K = record
    { F = F
    ; ε = ε
    ; δ = δ
    ; assoc = assoc'
    ; sym-assoc = sym assoc'
    ; identityˡ = identityˡ'
    ; identityʳ = K.identityʳ
    }
    where
      module K = RComonad K
      open K using (counit; cobind)

      -- Extract a functor from the relative comonad
      F : Endofunctor C
      F = RComonad⇒Functor K
      open Functor F using (F₀; F₁)

      -- constructing ε from counit
      ε = ntHelper {F = F} {G = idF} record
        { η = λ X → counit
        ; commute = λ f → K.identityʳ
        }

      -- helper for δ.commute and assoc'
      commute' : ∀ {X Y : Obj } (f : F₀ Y ⇒ X) → cobind id ∘ cobind f ≈ cobind (cobind f ∘ counit) ∘ cobind id
      commute' {X} {Y} f = begin
        cobind id ∘ cobind f                     ≈⟨ K.sym-assoc ⟩
        cobind (id ∘ cobind f)                   ≈⟨ K.cobind-≈ id-comm-sym ⟩
        cobind (cobind f ∘ id)                   ≈⟨ sym (K.cobind-≈ (pullʳ K.identityʳ)) ⟩
        cobind ((cobind f ∘ counit) ∘ cobind id) ≈⟨ K.assoc ⟩
        cobind (cobind f ∘ counit) ∘ cobind id   ∎

      -- constructing δ from cobind
      δ = ntHelper {F = F} {G = F ∘F F} record 
        { η = λ X → cobind id 
        ; commute = λ f → commute' (f ∘ counit) 
        }

      module ε = NaturalTransformation ε
      module δ = NaturalTransformation δ

      assoc' : {X : Obj} → δ.η (F₀ X) ∘ δ.η X ≈ F₁ (δ.η X) ∘ δ.η X
      assoc' = commute' id

      identityˡ' : {X : Obj} → F₁ (ε.η X) ∘ δ.η X ≈ id
      identityˡ' = begin 
        cobind (counit ∘ counit) ∘ cobind id   ≈⟨ K.sym-assoc ⟩ 
        cobind ((counit ∘ counit) ∘ cobind id) ≈⟨ K.cobind-≈ (pullʳ K.identityʳ) ⟩ 
        cobind (counit ∘ id)                   ≈⟨ K.cobind-≈ identityʳ ⟩ 
        cobind counit                          ≈⟨ K.identityˡ ⟩ 
        id                                     ∎

  Comonad⇒Kleisli : Comonad C → KleisliCotriple
  Comonad⇒Kleisli M = record
    { F₀ = F₀
    ; counit = ε.η _
    ; cobind = λ f → F₁ f ∘ δ.η _
    ; identityʳ = identityʳ'
    ; identityˡ = M.identityˡ
    ; assoc = assoc'
    ; sym-assoc = sym assoc'
    ; cobind-≈ = λ fg → ∘-resp-≈ˡ (F-resp-≈ fg)
    }
    where
      module M = Comonad M
      open Comonad M using (F; ε; δ)
      open Functor F

      identityʳ' : {X Y : Obj} {k : F₀ X ⇒ Y} → ε.η Y ∘ F₁ k ∘ δ.η X ≈ k
      identityʳ' {X} {Y} {k} = begin 
        ε.η Y ∘ F₁ k ∘ δ.η X     ≈⟨ pullˡ (ε.commute _) ⟩
        (k ∘ ε.η (F₀ X)) ∘ δ.η X ≈⟨ cancelʳ M.identityʳ ⟩
        k                        ∎

      assoc' : {X Y Z : Obj} {k : F₀ X ⇒ Y} {l : F₀ Y ⇒ Z} → F₁ (l ∘ F₁ k ∘ δ.η X) ∘ δ.η X ≈ (F₁ l ∘ δ.η Y) ∘ F₁ k ∘ δ.η X
      assoc' {X} {Y} {Z} {k} {l} = begin
        F₁ (l ∘ F₁ k ∘ δ.η X) ∘ δ.η X             ≈⟨ homomorphism ⟩∘⟨refl ⟩
        (F₁ l ∘ F₁ (F₁ k ∘ δ.η X) ) ∘ δ.η X       ≈⟨ (refl⟩∘⟨ homomorphism) ⟩∘⟨refl ⟩
        (F₁ l ∘ (F₁ (F₁ k) ∘ F₁ (δ.η X))) ∘ δ.η X ≈⟨ pullʳ (pullʳ M.sym-assoc) ⟩
        F₁ l ∘ F₁ (F₁ k) ∘ δ.η (F₀ X) ∘ δ.η X     ≈⟨ refl⟩∘⟨ pullˡ (sym (δ.commute k)) ⟩
        F₁ l ∘ (δ.η Y ∘ F₁ k) ∘ δ.η X             ≈⟨ assoc²δγ ⟩
        (F₁ l ∘ δ.η Y) ∘ F₁ k ∘ δ.η X             ∎
