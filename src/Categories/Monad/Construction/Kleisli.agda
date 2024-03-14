{-# OPTIONS --without-K --safe #-}

module Categories.Monad.Construction.Kleisli where

-- Definition of kleisli triple as a relative monad
-- and the equivalence of kleisli triple and monad
-- see https://ncatlab.org/nlab/show/extension+system (the naming differs)

open import Level
open import Categories.Category.Core using (Category)
open import Categories.Monad.Relative using (RMonad⇒Functor) renaming (Monad to RMonad)
open import Categories.Monad using (Monad)
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

  -- a kleisli triple is a relative monad with J = idF
  KleisliTriple : Set (o ⊔ ℓ ⊔ e)
  KleisliTriple = RMonad {C = C} idF

  -- kleisli triples are equivalent to monads
  Kleisli⇒Monad : KleisliTriple → Monad C
  Kleisli⇒Monad K = record
    { F = F
    ; η = η
    ; μ = μ
    ; assoc = assoc'
    ; sym-assoc = sym assoc'
    ; identityˡ = identityˡ'
    ; identityʳ = K.identityʳ
    }
    where
      module K = RMonad K
      open K using (unit; extend)

      -- Extract a functor from the relative monad
      F : Endofunctor C
      F = RMonad⇒Functor K
      open Functor F using (F₀; F₁)

      -- constructing η from unit
      η = ntHelper {F = idF} {G = F} record
        { η = λ X → unit
        ; commute = λ f → sym K.identityʳ
        }

      -- helper for μ.commute and assoc'
      commute' : ∀ {X Y : Obj } (f : X ⇒ F₀ Y) → extend id ∘ extend (unit ∘ extend f) ≈ extend f ∘ (extend id)
      commute' {X} {Y} f = begin
        extend id ∘ extend (unit ∘ extend f)   ≈⟨ K.sym-assoc ⟩
        extend (extend id ∘ unit ∘ extend f)   ≈⟨ K.extend-≈ (pullˡ K.identityʳ) ⟩
        extend (id ∘ extend f)                 ≈⟨ K.extend-≈ id-comm-sym ⟩
        extend (extend f ∘ id)                 ≈⟨ K.assoc ⟩
        extend f ∘ (extend id)                 ∎

      -- constructing μ from extend
      μ = ntHelper {F = F ∘F F} {G = F} record
        { η = λ X → extend id
        ; commute = λ f → commute' (unit ∘ f)
        }

      module η = NaturalTransformation η
      module μ = NaturalTransformation μ

      assoc' : ∀ {X : Obj} → μ.η X ∘ F₁ (μ.η X) ≈ μ.η X ∘ μ.η (F₀ X)
      assoc' = commute' id

      identityˡ' : ∀ {X : Obj} → μ.η X ∘ F₁ (η.η X) ≈ id
      identityˡ' = begin 
        extend id ∘ extend (unit ∘ unit)   ≈⟨ K.sym-assoc ⟩ 
        extend (extend id ∘ (unit ∘ unit)) ≈⟨ K.extend-≈ (pullˡ K.identityʳ) ⟩
        extend (id ∘ unit)                 ≈⟨ K.extend-≈ identityˡ ⟩
        extend unit                        ≈⟨ K.identityˡ ⟩
        id                                 ∎

  Monad⇒Kleisli : Monad C → KleisliTriple
  Monad⇒Kleisli M = record
    { F₀ = F₀
    ; unit = η.η _
    ; extend = λ f → μ.η _ ∘ F₁ f
    ; identityʳ = identityʳ'
    ; identityˡ = M.identityˡ
    ; assoc = assoc'
    ; sym-assoc = sym assoc'
    ; extend-≈ = λ fg → ∘-resp-≈ʳ (F-resp-≈ fg)
    }
    where
      module M = Monad M
      open Monad M using (F; η; μ)
      open Functor F

      identityʳ' : ∀ {X Y} {k : X ⇒ F₀ Y} → (μ.η Y ∘ F₁ k) ∘ η.η X ≈ k
      identityʳ' {X} {Y} {k}  = begin 
        ((μ.η Y ∘ F₁ k) ∘ η.η X)   ≈⟨ pullʳ (sym (η.commute _)) ⟩
        (μ.η Y ∘ η.η (F₀ Y) ∘ k)   ≈⟨ cancelˡ M.identityʳ ⟩
        k                          ∎

      assoc' : ∀  {X Y Z} {k : X ⇒ F₀ Y} {l : Y ⇒ F₀ Z} → μ.η Z ∘ F₁ ((μ.η Z ∘ F₁ l) ∘ k) ≈ (μ.η Z ∘ F₁ l) ∘ μ.η Y ∘ F₁ k
      assoc' {X} {Y} {Z} {k} {l} = begin
        (μ.η Z ∘ F₁ ((μ.η Z ∘ F₁ l) ∘ k))           ≈⟨ refl⟩∘⟨ homomorphism ⟩ 
        (μ.η Z ∘ F₁ (μ.η Z ∘ ₁ l) ∘ F₁ k)           ≈⟨ refl⟩∘⟨ homomorphism ⟩∘⟨refl ⟩ 
        (μ.η Z ∘ (F₁ (μ.η Z) ∘ F₁ (F₁ l)) ∘ F₁ k)   ≈⟨ pullˡ (pullˡ M.assoc) ⟩ 
        (((μ.η Z ∘ μ.η (F₀ Z)) ∘ F₁ (F₁ l)) ∘ F₁ k) ≈⟨ pullʳ (μ.commute l) ⟩∘⟨refl ⟩
        (μ.η Z ∘ F₁ l ∘ μ.η Y) ∘ F₁ k               ≈⟨ assoc²βγ ⟩
        (μ.η Z ∘ F₁ l) ∘ μ.η Y ∘ F₁ k               ∎


