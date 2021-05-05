{-# OPTIONS --without-K --safe #-}

-- A Solver for monoidal categories.
-- Roughly based off of "Extracting a proof of coherence for monoidal categories from a formal proof of normalization for monoids",
-- by Ilya Beylin and Peter Dybjer.
module Categories.Tactic.Monoidal where

open import Level
open import Data.Product using (_,_)
open import Data.List
open import Data.List.Properties using (++-assoc; ++-identityʳ)

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Properties
  using (subst-application)

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
import Categories.Category.Monoidal.Reasoning as MonoidalReasoning
open import Categories.Category.Monoidal.Properties using (module Kelly's)

import Categories.Morphism.Reasoning as MR

--------------------------------------------------------------------------------
-- Introduction:
-- The basic idea of this solver is similar to a coherence theorem for
-- monoidal categories. We are going to show that every single
-- chain of coherence morphisms have some canonical form.
-- Once we have done that, it is simply a matter of mapping two
-- chains of coherence morphisms to their normal forms, and checking
-- if the two are equal.

module _ {o ℓ e} {𝒞 : Category o ℓ e} (𝒱 : Monoidal 𝒞) where

  infixr 9 _∘′_

  infixr 10 _⊗₀′_ _⊗₁′_

  open Category 𝒞
  open Monoidal 𝒱

  open MR 𝒞
  open MonoidalReasoning 𝒱

  --------------------------------------------------------------------------------
  -- A 'Word' reifies all the parenthesis/tensors/units of some object
  -- in a monoidal category into a data structure
  --------------------------------------------------------------------------------
  data Word : Set o where
    _⊗₀′_ : Word → Word → Word
    unit′ : Word
    _′    : (X : Obj) → Word

  reify : Word → Obj
  reify (w₁ ⊗₀′ w₂) = reify w₁ ⊗₀ reify w₂
  reify unit′ = unit
  reify (x ′) = x

  private
    variable
      X Y Z   : Obj
      A B C D : Word

  --------------------------------------------------------------------------------
  -- An 'Expr' reifies all unitors, associators and their compositions
  -- into a data structure.
  --------------------------------------------------------------------------------
  data Expr : Word → Word → Set o where
    id′  : Expr A A
    _∘′_ : Expr B C → Expr A B → Expr A C
    _⊗₁′_ : Expr A C → Expr B D → Expr (A ⊗₀′ B) (C ⊗₀′ D)
    α′   : Expr ((A ⊗₀′ B) ⊗₀′ C) (A ⊗₀′ (B ⊗₀′ C))
    α⁻¹′ : Expr (A ⊗₀′ (B ⊗₀′ C)) ((A ⊗₀′ B) ⊗₀′ C)
    ƛ′   : Expr (unit′ ⊗₀′ A) A
    ƛ⁻¹′ : Expr A (unit′ ⊗₀′ A)
    ρ′   : Expr (A ⊗₀′ unit′) A
    ρ⁻¹′ : Expr A (A ⊗₀′ unit′)

  -- Embed a morphism in 'Expr' back into '𝒞' without normalizing.
  [_↓] : Expr A B → (reify A) ⇒ (reify B)
  [ id′ ↓]    = id
  [ f ∘′ g ↓] = [ f ↓] ∘ [ g ↓]
  [ f ⊗₁′ g ↓] = [ f ↓] ⊗₁ [ g ↓]
  [ α′ ↓]     = associator.from
  [ α⁻¹′ ↓]   = associator.to
  [ ƛ′ ↓]     = unitorˡ.from
  [ ƛ⁻¹′ ↓]   = unitorˡ.to
  [ ρ′ ↓]     = unitorʳ.from
  [ ρ⁻¹′ ↓]   = unitorʳ.to

  infix 4 _≈↓_

  -- TODO: is this sufficient or should we define an equality directly
  -- on Expr?
  _≈↓_ : (f g : Expr A B) → Set e
  f ≈↓ g = [ f ↓] ≈ [ g ↓]

  -- Invert a composition of coherence morphisms
  invert : Expr A B → Expr B A
  invert id′ = id′
  invert (f ∘′ g) = invert g ∘′ invert f
  invert (f ⊗₁′ g) = invert f ⊗₁′ invert g
  invert α′ = α⁻¹′
  invert α⁻¹′ = α′
  invert ƛ′ = ƛ⁻¹′
  invert ƛ⁻¹′ = ƛ′
  invert ρ′ = ρ⁻¹′
  invert ρ⁻¹′ = ρ′

  NfWord : Set o
  NfWord = List Obj

  data NfExpr : NfWord → NfWord → Set o where
    id′ : ∀ {N} → NfExpr N N

  -- An embedding of normal forms

  ⌞_⌟ : NfWord → Word
  ⌞ [] ⌟    = unit′
  ⌞ A ∷ N ⌟ = (A ′) ⊗₀′ ⌞ N ⌟

  ⌊_⌋ : ∀ {N M} → NfExpr N M → Expr ⌞ N ⌟ ⌞ M ⌟
  ⌊ id′ ⌋ = id′

  -- The monoidal operations are all admissible on normal forms.

  infixr 9 _∘ⁿ_
  infixr 10  _⊗ⁿ_

  _∘ⁿ_ : ∀ {N₁ N₂ N₃} →
         NfExpr N₂ N₃ → NfExpr N₁ N₂ → NfExpr N₁ N₃
  id′ ∘ⁿ id′ = id′

  _⊗ⁿ_ : ∀ {N₁ N₂ M₁ M₂} →
         NfExpr N₁ M₁ → NfExpr N₂ M₂ → NfExpr (N₁ ++ N₂) (M₁ ++ M₂)
  id′ ⊗ⁿ id′ = id′

  αⁿ : ∀ N₁ N₂ N₃ → NfExpr ((N₁ ++ N₂) ++ N₃) (N₁ ++ (N₂ ++ N₃))
  αⁿ N₁ N₂ N₃ = subst (NfExpr ((N₁ ++ N₂) ++ N₃)) (++-assoc N₁ N₂ N₃) id′

  ρⁿ : ∀ N → NfExpr (N ++ []) N
  ρⁿ N = subst (NfExpr (N ++ [])) (++-identityʳ N) id′

  invertⁿ : ∀ {N M} → NfExpr N M → NfExpr M N
  invertⁿ id′ = id′

  -- The normalization functor

  nf₀ : Word → NfWord
  nf₀ (A₁ ⊗₀′ A₂) = nf₀ A₁ ++ nf₀ A₂
  nf₀ unit′       = []
  nf₀ (X ′)       = X ∷ []

  nf₁ : Expr A B → NfExpr (nf₀ A) (nf₀ B)
  nf₁ id′                = id′
  nf₁ (f ∘′ g)           = nf₁ f ∘ⁿ nf₁ g
  nf₁ (f ⊗₁′ g)          = nf₁ f ⊗ⁿ nf₁ g
  nf₁ (α′ {A} {B} {C})   = αⁿ (nf₀ A) (nf₀ B) (nf₀ C)
  nf₁ (α⁻¹′ {A} {B} {C}) = invertⁿ (αⁿ (nf₀ A) (nf₀ B) (nf₀ C))
  nf₁ ƛ′                 = id′
  nf₁ ƛ⁻¹′               = id′
  nf₁ ρ′                 = ρⁿ _
  nf₁ ρ⁻¹′               = invertⁿ (ρⁿ _)

  -- The embedding is a monoidal functor

  ⌊⌋-id : ∀ {N} → ⌊ id′ {N} ⌋ ≈↓ id′
  ⌊⌋-id = Equiv.refl

  ⌊⌋-∘ : ∀ {N₁ N₂ N₃} (f : NfExpr N₂ N₃) (g : NfExpr N₁ N₂) →
         ⌊ f ∘ⁿ g ⌋ ≈↓ ⌊ f ⌋ ∘′ ⌊ g ⌋
  ⌊⌋-∘ id′ id′ = ⟺ identity²

  ⌞⌟-⊗ : ∀ N M → Expr (⌞ N ⌟ ⊗₀′ ⌞ M ⌟) ⌞ N ++ M ⌟
  ⌞⌟-⊗ [] M      = ƛ′
  ⌞⌟-⊗ (X ∷ N) M = id′ ⊗₁′ ⌞⌟-⊗ N M ∘′ α′

  ⌊⌋-⊗ : ∀ {N₁ N₂ M₁ M₂} (f : NfExpr N₁ M₁) (g : NfExpr N₂ M₂) →
         ⌊ f ⊗ⁿ g ⌋ ∘′ ⌞⌟-⊗ N₁ N₂ ≈↓ ⌞⌟-⊗ M₁ M₂ ∘′ ⌊ f ⌋ ⊗₁′ ⌊ g ⌋
  ⌊⌋-⊗ {N₁} {N₂} id′ id′ = begin
    id ∘ [ ⌞⌟-⊗ N₁ N₂ ↓]         ≈⟨ id-comm-sym ⟩
    [ ⌞⌟-⊗ N₁ N₂ ↓] ∘ id         ≈˘⟨ refl⟩∘⟨ ⊗.identity ⟩
    [ ⌞⌟-⊗ N₁ N₂ ↓] ∘ id ⊗₁ id   ∎

  ⌊⌋-ρ : ∀ N → ⌊ ρⁿ N ⌋ ∘′ ⌞⌟-⊗ N [] ≈↓ ρ′
  ⌊⌋-ρ [] = identityˡ ○ Kelly's.coherence₃ 𝒱
  ⌊⌋-ρ (X ∷ N) = begin
      [ ⌊ subst (NfExpr (X ∷ N ++ [])) (cong (X ∷_) (++-identityʳ N)) id′ ⌋ ↓] ∘
      id ⊗₁ [ ⌞⌟-⊗ N [] ↓] ∘ associator.from
    ≡⟨ cong (λ f → [ ⌊ f ⌋ ∘′ id′ ⊗₁′ ⌞⌟-⊗ N [] ∘′ α′ ↓])
            (helper₁ (++-identityʳ N)) ⟩
      [ ⌊ id′ ⊗ⁿ ρⁿ N ⌋ ↓] ∘ id ⊗₁ [ ⌞⌟-⊗ N [] ↓] ∘ associator.from
    ≈⟨ helper₂ (ρⁿ N) ⟩∘⟨refl ⟩
      id ⊗₁ [ ⌊ ρⁿ N ⌋ ↓] ∘ id ⊗₁ [ ⌞⌟-⊗ N [] ↓] ∘ associator.from
    ≈⟨ merge₂ ⌊⌋-ρ N ⟩∘⟨ Equiv.refl ⟩
      id ⊗₁ unitorʳ.from ∘ associator.from
    ≈⟨ Kelly's.coherence₂ 𝒱 ⟩
      unitorʳ.from
    ∎
    where

      -- FIXME: give these better names and reuse them in the proof of
      -- the hexagon identity (the ⌊⌋-α yet to be written).

      helper₁ : ∀ {X N M} (eq : N ≡ M) →
                subst (NfExpr (X ∷ N)) (cong (X ∷_) eq) (id′ ⊗ⁿ id′ {N}) ≡
                id′ ⊗ⁿ subst (NfExpr N) eq id′
      helper₁ refl = refl

      helper₂ : ∀ {X N M} (f : NfExpr N M) → ⌊ id′ ⊗ⁿ f ⌋ ≈↓ id′ {X ′} ⊗₁′ ⌊ f ⌋
      helper₂ id′ = ⟺ ⊗.identity

  invert-resp-≈ : ∀ (f g : Expr A B) → f ≈↓ g → invert f ≈↓ invert g
  invert-resp-≈ f g eq = {!!}

  ⌊⌋-invert : ∀ {M} {N O} (f : Expr M ⌞ N ⌟) (g : NfExpr N O) (h : Expr M ⌞ O ⌟) → ⌊ g ⌋ ∘′ f ≈↓ h  → invert f ∘′ ⌊ invertⁿ g ⌋ ≈↓ invert h
  ⌊⌋-invert f id′ h eq = begin
    [ invert f ↓] ∘ id ≈⟨ identityʳ ⟩
    [ invert f ↓]      ≈⟨ invert-resp-≈ f h (⟺ identityˡ ○ eq) ⟩
    [ invert h ↓]      ∎

  -- Build a coherence morphism out of some word into it's normal form.
  into : ∀ (A : Word) → Expr A ⌞ nf₀ A ⌟
  into (A ⊗₀′ B) = ⌞⌟-⊗ (nf₀ A) (nf₀ B) ∘′ (into A ⊗₁′ into B)
  into unit′     = id′
  into (x ′)     = ρ⁻¹′

  -- Build a coherence morphism into a word from it's normal form.
  out : ∀ (A : Word) → Expr ⌞ nf₀ A ⌟ A
  out A = invert (into A)

  -- Normalize an expression.
  -- We do this by building maps into and out of the normal forms of the
  -- domain/codomain, then using our 'strict' coherence morphism to link them together.
  normalize : Expr A B → Expr A B
  normalize {A = A} {B = B} f = out B ∘′ ⌊ nf₁ f ⌋ ∘′ into A

  -- Witness the isomorphism between 'f' and 'invert f'.
  invert-isoˡ : ∀ (f : Expr A B) → [ invert f ↓] ∘ [ f ↓] ≈ id
  invert-isoˡ id′ = identity²
  invert-isoˡ (f ∘′ g) = begin
    ([ invert g ↓] ∘ [ invert f ↓]) ∘ ([ f ↓] ∘ [ g ↓]) ≈⟨ cancelInner (invert-isoˡ f)  ⟩
    [ invert g ↓] ∘ [ g ↓]                              ≈⟨ invert-isoˡ g ⟩
    id                                                  ∎
  invert-isoˡ (f ⊗₁′ g) = begin
    ([ invert f ↓] ⊗₁ [ invert g ↓]) ∘ ([ f ↓] ⊗₁ [ g ↓]) ≈˘⟨ ⊗.homomorphism ⟩
    ([ invert f ↓] ∘ [ f ↓]) ⊗₁ ([ invert g ↓] ∘ [ g ↓])  ≈⟨ ⊗.F-resp-≈ (invert-isoˡ f , invert-isoˡ g) ⟩
    id ⊗₁ id                                              ≈⟨ ⊗.identity ⟩
    id                                                    ∎
  invert-isoˡ α′   = associator.isoˡ
  invert-isoˡ α⁻¹′ = associator.isoʳ
  invert-isoˡ ƛ′   = unitorˡ.isoˡ
  invert-isoˡ ƛ⁻¹′ = unitorˡ.isoʳ
  invert-isoˡ ρ′   = unitorʳ.isoˡ
  invert-isoˡ ρ⁻¹′ = unitorʳ.isoʳ

  -- Witness the isomorphism between 'f' and 'invert f'.
  invert-isoʳ : ∀ (f : Expr A B) → [ f ↓] ∘ [ invert f ↓] ≈ id
  invert-isoʳ id′ = identity²
  invert-isoʳ (f ∘′ g) = begin
    ([ f ↓] ∘ [ g ↓]) ∘ ([ invert g ↓] ∘ [ invert f ↓]) ≈⟨ cancelInner (invert-isoʳ g) ⟩
    [ f ↓] ∘ [ invert f ↓]                              ≈⟨ invert-isoʳ f ⟩
    id                                                  ∎
  invert-isoʳ (f ⊗₁′ g) = begin
    ([ f ↓] ⊗₁ [ g ↓]) ∘ ([ invert f ↓] ⊗₁ [ invert g ↓]) ≈˘⟨ ⊗.homomorphism ⟩
    ([ f ↓] ∘ [ invert f ↓]) ⊗₁ ([ g ↓] ∘ [ invert g ↓])  ≈⟨ ⊗.F-resp-≈ (invert-isoʳ f , invert-isoʳ g) ⟩
    id ⊗₁ id                                              ≈⟨ ⊗.identity ⟩
    id                                                    ∎
  invert-isoʳ α′   = associator.isoʳ
  invert-isoʳ α⁻¹′ = associator.isoˡ
  invert-isoʳ ƛ′   = unitorˡ.isoʳ
  invert-isoʳ ƛ⁻¹′ = unitorˡ.isoˡ
  invert-isoʳ ρ′   = unitorʳ.isoʳ
  invert-isoʳ ρ⁻¹′ = unitorʳ.isoˡ

  -- Helper lemma for showing that mapping into a normal form then back out
  -- is identity.
  into-out : ∀ (A : Word) → [ out A ↓] ∘ id ∘ [ into A ↓] ≈ id
  into-out A = begin
    [ out A ↓] ∘ id ∘ [ into A ↓] ≈⟨ refl⟩∘⟨ identityˡ ⟩
    [ out A ↓] ∘ [ into A ↓]      ≈⟨ invert-isoˡ (into A) ⟩
    id ∎

  -- Normalization preserves equality.
  preserves-≈ : ∀ (f : Expr A B) → normalize f ≈↓ f
  preserves-≈ (id′ {A}) = into-out A
  preserves-≈ (_∘′_ {B} {C} {A} f g) = begin
      [ out C ↓] ∘ [ ⌊ nf₁ (f ∘′ g) ⌋ ↓] ∘ [ into A ↓]
    ≈⟨ refl⟩∘⟨ ⌊⌋-∘ (nf₁ f) (nf₁ g) ⟩∘⟨refl ⟩
      [ out C ↓] ∘ ([ ⌊ nf₁ f ⌋ ↓] ∘ [ ⌊ nf₁ g ⌋ ↓]) ∘ [ into A ↓]
    ≈˘⟨ refl⟩∘⟨ cancelInner (invert-isoʳ (into B)) ⟩∘⟨refl ⟩
      [ out C ↓] ∘
      (([ ⌊ nf₁ f ⌋ ↓] ∘ [ into B ↓]) ∘ ([ out B ↓] ∘ [ ⌊ nf₁ g ⌋ ↓])) ∘
      [ into A ↓]
    ≈⟨ center⁻¹ (preserves-≈ f) (assoc ○ preserves-≈ g) ⟩
      [ f ↓] ∘ [ g ↓]
    ∎
  preserves-≈ (_⊗₁′_ {A} {C} {B} {D} f g) = begin
      ([ out C ↓] ⊗₁ [ out D ↓] ∘ [ invert (⌞⌟-⊗ (nf₀ C) (nf₀ D)) ↓]) ∘
      [ ⌊ nf₁ (f ⊗₁′ g) ⌋ ↓] ∘
      [ ⌞⌟-⊗ (nf₀ A) (nf₀ B) ↓] ∘ [ into A ↓] ⊗₁ [ into B ↓]
    ≈⟨ (refl⟩∘⟨ pullˡ (⌊⌋-⊗ (nf₁ f) (nf₁ g))) ⟩
      ([ out C ↓] ⊗₁ [ out D ↓] ∘ [ invert (⌞⌟-⊗ (nf₀ C) (nf₀ D)) ↓]) ∘
      ([ ⌞⌟-⊗ (nf₀ C) (nf₀ D) ↓] ∘ [ ⌊ nf₁ f ⌋ ⊗₁′ ⌊ nf₁ g ⌋ ↓]) ∘
      [ into A ↓] ⊗₁ [ into B ↓]
    ≈⟨ pullˡ (cancelInner (invert-isoˡ (⌞⌟-⊗ (nf₀ C) (nf₀ D)))) ⟩
      ([ out C ⊗₁′ out D ↓] ∘ [ ⌊ nf₁ f ⌋ ⊗₁′ ⌊ nf₁ g ⌋ ↓]) ∘
      [ into A ⊗₁′ into B ↓]
    ≈˘⟨ pushʳ ⊗.homomorphism ⟩
      ([ out C ⊗₁′ out D ↓] ∘ [ (⌊ nf₁ f ⌋ ∘′ into A) ⊗₁′ (⌊ nf₁ g ⌋ ∘′ into B) ↓])
    ≈˘⟨ ⊗.homomorphism ⟩
      ([ out C ∘′ ⌊ nf₁ f ⌋ ∘′ into A ↓] ⊗₁ [ out D ∘′ ⌊ nf₁ g ⌋ ∘′ into B ↓])
    ≈⟨ preserves-≈ f ⟩⊗⟨ preserves-≈ g ⟩
      [ f ↓] ⊗₁ [ g ↓]
    ∎
  preserves-≈ (α′ {A} {B} {C}) = {!!}
  preserves-≈ α⁻¹′ = {!!}
  preserves-≈ (ƛ′ {A}) = begin
    [ out A ↓] ∘ id ∘ unitorˡ.from ∘ id ⊗₁ [ into A ↓] ≈⟨ refl⟩∘⟨ refl⟩∘⟨ unitorˡ-commute-from ⟩
    [ out A ↓] ∘ id ∘ [ into A ↓] ∘ unitorˡ.from       ≈˘⟨ assoc²' ⟩
    ([ out A ↓] ∘ id ∘ [ into A ↓]) ∘ unitorˡ.from     ≈⟨ elimˡ (into-out A)  ⟩
    unitorˡ.from                                       ∎
  preserves-≈ (ƛ⁻¹′ {A}) = begin
    (id ⊗₁ [ out A ↓] ∘ unitorˡ.to) ∘ id ∘ [ into A ↓] ≈˘⟨ unitorˡ-commute-to ⟩∘⟨refl ⟩
    (unitorˡ.to ∘ [ out A ↓]) ∘ id ∘ [ into A ↓]       ≈⟨ cancelʳ (into-out A) ⟩
    unitorˡ.to                                                   ∎
  preserves-≈ (ρ′ {A}) = begin
      [ out A ↓] ∘ [ ⌊ ρⁿ (nf₀ A) ⌋ ↓] ∘ [ ⌞⌟-⊗ (nf₀ A) [] ↓] ∘ [ into A ↓] ⊗₁ id
    ≈⟨ refl⟩∘⟨ pullˡ (⌊⌋-ρ (nf₀ A)) ⟩
      [ out A ↓] ∘ unitorʳ.from ∘ ([ into A ↓] ⊗₁ id)
    ≈⟨ refl⟩∘⟨ unitorʳ-commute-from ⟩
      [ out A ↓] ∘ [ into A ↓] ∘ unitorʳ.from
    ≈⟨ cancelˡ (invert-isoˡ (into A)) ⟩
      unitorʳ.from
    ∎
  preserves-≈ (ρ⁻¹′ {A}) = begin
      ([ out A ↓] ⊗₁ id ∘ [ invert (⌞⌟-⊗ (nf₀ A) []) ↓]) ∘ ([ ⌊ invertⁿ (ρⁿ (nf₀ A)) ⌋ ↓] ∘ [ into A ↓])
    ≈⟨ center (⌊⌋-invert (⌞⌟-⊗ (nf₀ A) []) (ρⁿ (nf₀ A)) ρ′ (⌊⌋-ρ (nf₀ A))) ⟩
      [ out A ↓] ⊗₁ id ∘ unitorʳ.to ∘ [ into A ↓]
    ≈⟨ refl⟩∘⟨ unitorʳ-commute-to ⟩
      [ out A ↓] ⊗₁ id ∘ [ into A ↓] ⊗₁ id ∘ unitorʳ.to
    ≈⟨ pullˡ (⟺ ⊗.homomorphism) ⟩
      ([ out A ↓] ∘ [ into A ↓]) ⊗₁ (id ∘ id) ∘ unitorʳ.to
    ≈⟨ (invert-isoˡ (into A) ⟩⊗⟨ identity²) ⟩∘⟨refl ⟩
      id ⊗₁ id ∘ unitorʳ.to
    ≈⟨ elimˡ ⊗.identity ⟩
      unitorʳ.to ∎
