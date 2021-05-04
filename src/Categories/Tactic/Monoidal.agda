{-# OPTIONS --without-K --safe #-}

-- A Solver for monoidal categories.
-- Roughly based off of "Extracting a proof of coherence for monoidal categories from a formal proof of normalization for monoids",
-- by Ilya Beylin and Peter Dybjer.
module Categories.Tactic.Monoidal where

open import Level
open import Data.Product using (_,_)

open import Relation.Binary.PropositionalEquality

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)

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

  open HomReasoning
  open MR 𝒞

  --------------------------------------------------------------------------------
  -- A 'Word' reifies all the parenthesis/tensors/units of some object
  -- in a monoidal category into a data structure
  --------------------------------------------------------------------------------
  data Word : Set o where
    _⊗₀′_ : Word → Word → Word
    unit′ : Word
    _′    : Obj → Word

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
  data Expr : Word → Word → Set (o ⊔ ℓ) where
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

  -- Reassociate all the tensors to the right.
  -- 
  -- Note [reassoc + lists]:
  -- We could use a list here, but this version is somewhat nicer,
  -- as we can get things like right-identity for free.
  reassoc : Word → (Word → Word)
  reassoc (w₁ ⊗₀′ w₂) rest = reassoc w₁ (reassoc w₂ rest)
  reassoc unit′ rest = rest
  reassoc (x ′) rest = (x ′) ⊗₀′ rest

  -- This is the key proof of the entire tactic.
  -- 'coherence e' proves that all of our coherence morphisms
  -- in 'e' are not required after reassociation, as they are on-the-nose equal.
  coherence : Expr A B → (X : Word) → reassoc A X ≡ reassoc B X
  coherence id′                         X = refl
  coherence (f ∘′ g)                    X = trans (coherence g X) (coherence f X)
  coherence (_⊗₁′_ {A} {B} {C} {D} f g) X = trans (cong (reassoc A) (coherence g X)) (coherence f (reassoc D X))
  coherence α′                          X = refl
  coherence α⁻¹′                        X = refl
  coherence ƛ′                          X = refl
  coherence ƛ⁻¹′                        X = refl
  coherence ρ′                          X = refl
  coherence ρ⁻¹′                        X = refl

  -- Place every word into a normal form
  -- > nf ((W ′ ⊗₀′ X ′) ⊗₀′ (Y ′ ⊗₀′ Z ′))
  --   W ′ ⊗₀ X ′ ⊗₀ Y ′ ⊗₀ Z ′ ⊗₀ unit′
  nf : Word → Word
  nf w = reassoc w unit′

  -- Given some coherence morphism, build a morphisms between
  -- the normal forms of it's domain and codomain.
  -- This will be equal to the identity morphism.
  strict : Expr A B → Expr (nf A) (nf B)
  strict {A = A} {B = B} e = subst (λ X → Expr (reassoc A unit′) X) (coherence e unit′) id′

  -- If we reassociate and tensor after that, we can find some coherence
  -- morphism that removes the pointless unit.
  slurp : ∀ (A B : Word) → Expr (reassoc A unit′ ⊗₀′ B) (reassoc A B)
  slurp (A ⊗₀′ B) C = slurp A (reassoc B C) ∘′ (id′ ⊗₁′ slurp B C) ∘′ α′ ∘′ (invert (slurp A (reassoc B unit′) ⊗₁′ id′))
  slurp unit′     B = ƛ′
  slurp (x ′)     B = ρ′ ⊗₁′ id′

  -- Coherence morphism witnessing the concatentation of normal forms.
  nf-homo : ∀ (A B : Word) → Expr (nf A ⊗₀′ nf B) (nf (A ⊗₀′ B))
  nf-homo A B = slurp A (reassoc B unit′)

  -- Build a coherence morphism out of some word into it's normal form.
  into : ∀ (A : Word) → Expr A (nf A)
  into (A ⊗₀′ B) = nf-homo A B ∘′ (into A ⊗₁′ into B)
  into unit′ = id′
  into (x ′) = ρ⁻¹′

  -- Build a coherence morphism into a word from it's normal form.
  out : ∀ (A : Word) → Expr (nf A) A
  out A = invert (into A)

  -- Normalize an expression.
  -- We do this by building maps into and out of the normal forms of the
  -- domain/codomain, then using our 'strict' coherence morphism to link them together.
  normalize : Expr A B → Expr A B
  normalize {A = A} {B = B} f = out B ∘′ strict f ∘′ into A

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

  -- Slurping on a unit is the same as removing the redundant unit by using
  -- the right associator.
  slurp-unit : ∀ (A : Word) → [ slurp A unit′ ↓] ≈ [ ρ′ {reassoc A unit′} ↓]
  slurp-unit (A ⊗₀′ A₁) = {!!}
  slurp-unit unit′ = {!!}
  slurp-unit (x ′) = {!!}

  -- The strict coherence morphism of a composition is the composition of the strict morphisms.
  strict-∘ : ∀ (f : Expr B C) (g : Expr A B) → [ strict (f ∘′ g) ↓] ≈ [ strict f ↓] ∘ [ strict g ↓]
  strict-∘ f g rewrite (coherence g unit′) | (coherence f unit′) = Equiv.sym identity²

  -- For whatever reason this is HARD TO PROVE.
  -- We run into all sorts of crazy issues when we try to rewrite any of the 'coherence f' proofs.
  strict-⊗ : ∀ (f : Expr A C) (g : Expr B D) → [ strict (f ⊗₁′ g) ↓] ≈ [ (nf-homo C D) ↓] ∘ [ strict f ↓] ⊗₁ [ strict g ↓] ∘ [ invert (nf-homo A B) ↓]
  strict-⊗ {A} {C} {B} {D} f g = {!!}

  -- Normalization preserves equality.
  preserves-≈ : ∀ (f : Expr A B) → [ normalize f ↓] ≈ [ f ↓]
  preserves-≈ (id′ {A}) = into-out A
  preserves-≈ (_∘′_ {B} {C} {A} f g) = begin
    [ out C ↓] ∘ [ strict (f ∘′ g) ↓] ∘ [ into A ↓]                                           ≈⟨ refl⟩∘⟨ strict-∘ f g ⟩∘⟨refl ⟩
    [ out C ↓] ∘ ([ strict f ↓] ∘ [ strict g ↓]) ∘ [ into A ↓]                                ≈˘⟨ refl⟩∘⟨ cancelInner (invert-isoʳ (into B)) ⟩∘⟨refl ⟩
    [ out C ↓] ∘ (([ strict f ↓] ∘ [ into B ↓]) ∘ ([ out B ↓] ∘ [ strict g ↓])) ∘ [ into A ↓] ≈⟨ center⁻¹ (preserves-≈ f) (assoc ○ preserves-≈ g) ⟩
    [ f ↓] ∘ [ g ↓]                                                                           ∎
  preserves-≈ (_⊗₁′_ {A} {C} {B} {D} f g) = begin
    ([ out C ↓] ⊗₁ [ out D ↓] ∘ [ invert (nf-homo C D) ↓]) ∘ [ strict (f ⊗₁′ g) ↓] ∘ [ nf-homo A B ↓] ∘ [ into A ↓] ⊗₁ [ into B ↓]
      ≈⟨ refl⟩∘⟨ strict-⊗ f g ⟩∘⟨refl ⟩
    ([ out C ↓] ⊗₁ [ out D ↓] ∘ [ invert (nf-homo C D) ↓]) ∘ ([ (nf-homo C D) ↓] ∘ [ strict f ↓] ⊗₁ [ strict g ↓] ∘ [ invert (nf-homo A B) ↓]) ∘ [ nf-homo A B ↓] ∘ [ into A ↓] ⊗₁ [ into B ↓]
      ≈⟨ {!!} ⟩
    [ out C ↓] ⊗₁ [ out D ↓] ∘ [ strict f ↓] ⊗₁ [ strict g ↓] ∘ [ into A ↓] ⊗₁ [ into B ↓]
      ≈⟨ {!!} ⟩
    ([ out C ↓] ∘ [ strict f ↓] ∘ [ into A ↓]) ⊗₁ ([ out D ↓] ∘ [ strict g ↓] ∘ [ into B ↓])
      ≈⟨ ⊗.F-resp-≈ (preserves-≈ f , preserves-≈ g) ⟩
    [ f ↓] ⊗₁ [ g ↓] ∎
  preserves-≈ (α′ {A} {B} {C}) = begin
    ([ invert (into A) ↓] ⊗₁ ([ invert (into B) ↓] ⊗₁ [ invert (into C) ↓] ∘ [ invert (nf-homo B C) ↓]) ∘ [ invert (nf-homo A (B ⊗₀′ C)) ↓]) ∘ id ∘ ([ slurp A (reassoc B (reassoc C unit′)) ↓] ∘ id ⊗₁ [ slurp B (reassoc C unit′) ↓] ∘ associator.from ∘ [ invert (slurp A (reassoc B unit′)) ↓] ⊗₁ id) ∘ ([ nf-homo A B ↓] ∘ [ into A ↓] ⊗₁ [ into B ↓]) ⊗₁ [ into C ↓] ≈⟨ {!!} ⟩
    associator.from ∎
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
    [ out A ↓] ∘ id ∘ [ slurp A unit′ ↓] ∘ ([ into A ↓] ⊗₁ id) ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (slurp-unit A ⟩∘⟨refl) ⟩
    [ out A ↓] ∘ id ∘ unitorʳ.from ∘ ([ into A ↓] ⊗₁ id)       ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ unitorʳ-commute-from) ⟩
    [ out A ↓] ∘ id ∘ [ into A ↓] ∘ unitorʳ.from               ≈˘⟨ assoc²' ⟩
    ([ out A ↓] ∘ id ∘ [ into A ↓]) ∘ unitorʳ.from             ≈⟨ elimˡ (into-out A)  ⟩
    unitorʳ.from                                               ∎
  preserves-≈ (ρ⁻¹′ {A}) = {!!}

