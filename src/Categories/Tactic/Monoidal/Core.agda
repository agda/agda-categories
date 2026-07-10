{-# OPTIONS --without-K --safe #-}

--------------------------------------------------------------------------------
-- Core interpretation and proof for monoidal coherence.
--
-- The object-level solver is organized as a monoid homomorphism:
--  ( List Atom , ++ , [] , _≡_ )  ──⟦_⟧ᴹ──▶  ( Obj , ⊗₀ , unit ; _≅_ )
--
-- The source is the free monoid on atoms.  The target is the monoid of objects
-- in a monoidal category, with tensor as multiplication and isomorphism as the
-- equality relation.  Strictification transports an object to the interpretation
-- of its normal form, and `object-coherence` gives the canonical structural
-- isomorphism between any two objects with the same normal form.
--
-- The morphism-level theorem is the standard normal-form proof of Mac Lane
-- coherence. See Mac Lane, "Natural Associativity and Commutativity", Rice
-- University Studies 49 (1963), pp. 28-46, Categories for the Working
-- Mathematician, Chapter VII; and Kelly, "On MacLane's Conditions for Coherence
-- of Natural Associativities, Commutativities, etc.", Journal of Algebra 1
-- (1964), pp. 397-402.
--------------------------------------------------------------------------------

open import Level using (Level; _⊔_)
open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal using (Monoidal)

module Categories.Tactic.Monoidal.Core
  {o ℓ e a : Level}
  {𝒞 : Category o ℓ e}
  (M : Monoidal 𝒞)
  {Atom : Set a}
  (⟦_⟧ₐ : Atom → Category.Obj 𝒞)
  where

open import Data.Product using (_,_)
open import Data.List.Base using (List; []; _∷_; _++_; ++-[]-rawMonoid)
import Data.List.Effectful.Foldable as List
open import Data.List.Properties using (++-assoc; ++-identityʳ)
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_; refl; cong; cong₂)
open import Algebra.Bundles using (Monoid)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)

open import Categories.Tactic.Monoidal.Free public
open import Categories.Morphism 𝒞 using (_≅_; module ≅)
open import Categories.Category.Monoidal.Utilities M
  using (_⊗ᵢ_; Obj-⊗-Monoid; module Shorthands; pentagon-inv)
open import Categories.Category.Monoidal.Properties M
  using (coherence₂; coherence₃; coherence-inv₁)
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Morphism.Reasoning 𝒞

open Category 𝒞
open Monoidal M hiding (⊗; _⊗-; -⊗_)
open Monoidal M using (module ⊗)
open Shorthands using (α⇒; α⇐; λ⇒; λ⇐; ρ⇒; ρ⇐)
open Free Atom using (Ob; ‹_›; I; _⊗_; nf; ⇒⇒nf; invert; idₘ; module NormalForm)
  renaming
    ( _⇒_ to _⊸_ ; _∘_ to _⊚_ ; _⊗₁_ to _⊗ˢ_
    ; α⇒  to α⇒ᶠ ; α⇐  to α⇐ᶠ ;  λ⇒  to λ⇒ᶠ ; λ⇐ to λ⇐ᶠ ; ρ⇒ to ρ⇒ᶠ ; ρ⇐ to ρ⇐ᶠ
    )
open NormalForm using (assocₙ; unitʳₙ)

private
  variable
    P Q R S : Obj
    A B C X Y Z W : Ob

-- ----------------------------------------------------------------------------
-- §1: The interpretation monoid homomorphism
-- ----------------------------------------------------------------------------
--
-- `eval` is the fold-map out of the free monoid on atoms into the monoid of
-- objects under tensor.

eval : List Atom → Obj
eval = List.foldMap (Monoid.rawMonoid Obj-⊗-Monoid) ⟦_⟧ₐ

open MonoidMorphisms (++-[]-rawMonoid Atom) (Monoid.rawMonoid Obj-⊗-Monoid)
  using (IsMonoidHomomorphism)

eval-homomorphism : IsMonoidHomomorphism eval
eval-homomorphism = List.foldMap-morphism Obj-⊗-Monoid ⟦_⟧ₐ

eval-homo : (x y : List Atom) → eval (x ++ y) ≅ eval x ⊗₀ eval y
eval-homo = IsMonoidHomomorphism.homo eval-homomorphism

-- ----------------------------------------------------------------------------
-- §2: Object interpretation and strictification
-- ----------------------------------------------------------------------------
--
-- `⟦_⟧₀` interprets a full object (with bracketing and units); `⟦ ⌜ w ⌝ ⟧₀`
-- coincides definitionally with `eval w`. `strictify` is the canonical iso
-- reassociating any object to (the image of) its normal form.

⟦_⟧₀ : Ob → Obj
⟦ ‹ x › ⟧₀ = ⟦ x ⟧ₐ
⟦ I ⟧₀     = unit
⟦ X ⊗ Y ⟧₀ = ⟦ X ⟧₀ ⊗₀ ⟦ Y ⟧₀

strictify : (X : Ob) → eval (nf X) ≅ ⟦ X ⟧₀
strictify ‹ x ›   = unitorʳ
strictify I       = ≅.refl
strictify (X ⊗ Y) = ≅.trans (eval-homo (nf X) (nf Y)) (strictify X ⊗ᵢ strictify Y)

-- Object-level coherence: any two objects with the same normal form are
-- canonically isomorphic.  No Mac Lane theorem is needed here; this is the free
-- monoid interpretation transported along `strictify`.
object-coherence : nf X ≡ nf Y → ⟦ X ⟧₀ ≅ ⟦ Y ⟧₀
object-coherence {X} {Y} p =
  ≅.trans (≅.sym (strictify X)) (≅.trans (≅.reflexive (cong eval p)) (strictify Y))

-- ----------------------------------------------------------------------------
-- §3: Morphism interpretation and semantic invertibility
-- ----------------------------------------------------------------------------
--
-- `⟦_⟧₁` is the strictify monoidal functor on arrows; every generator goes to the
-- corresponding structural component. `invert-iso{ˡ,ʳ}` show it sends `invert`
-- to a genuine two-sided inverse, so every free morphism interprets to an iso.

⟦_⟧₁ : X ⊸ Y → ⟦ X ⟧₀ ⇒ ⟦ Y ⟧₀
⟦ idₘ ⟧₁    = id
⟦ g ⊚ f ⟧₁  = ⟦ g ⟧₁ ∘ ⟦ f ⟧₁
⟦ f ⊗ˢ g ⟧₁ = ⟦ f ⟧₁ ⊗₁ ⟦ g ⟧₁
⟦ α⇒ᶠ ⟧₁    = α⇒
⟦ α⇐ᶠ ⟧₁    = α⇐
⟦ λ⇒ᶠ ⟧₁    = λ⇒
⟦ λ⇐ᶠ ⟧₁    = λ⇐
⟦ ρ⇒ᶠ ⟧₁    = ρ⇒
⟦ ρ⇐ᶠ ⟧₁    = ρ⇐

invert-isoˡ : (f : X ⊸ Y) → ⟦ invert f ⟧₁ ∘ ⟦ f ⟧₁ ≈ id
invert-isoˡ idₘ      = identity²
invert-isoˡ (g ⊚ f)  = cancelInner (invert-isoˡ g) ○ invert-isoˡ f
invert-isoˡ (f ⊗ˢ g) = ⊗-cancel (invert-isoˡ f) (invert-isoˡ g)
invert-isoˡ α⇒ᶠ      = associator.isoˡ
invert-isoˡ α⇐ᶠ      = associator.isoʳ
invert-isoˡ λ⇒ᶠ      = unitorˡ.isoˡ
invert-isoˡ λ⇐ᶠ      = unitorˡ.isoʳ
invert-isoˡ ρ⇒ᶠ      = unitorʳ.isoˡ
invert-isoˡ ρ⇐ᶠ      = unitorʳ.isoʳ

invert-isoʳ : (f : X ⊸ Y) → ⟦ f ⟧₁ ∘ ⟦ invert f ⟧₁ ≈ id
invert-isoʳ idₘ      = identity²
invert-isoʳ (g ⊚ f)  = cancelInner (invert-isoʳ f) ○ invert-isoʳ g
invert-isoʳ (f ⊗ˢ g) = ⊗-cancel (invert-isoʳ f) (invert-isoʳ g)
invert-isoʳ α⇒ᶠ      = associator.isoʳ
invert-isoʳ α⇐ᶠ      = associator.isoˡ
invert-isoʳ λ⇒ᶠ      = unitorˡ.isoʳ
invert-isoʳ λ⇐ᶠ      = unitorˡ.isoˡ
invert-isoʳ ρ⇒ᶠ      = unitorʳ.isoʳ
invert-isoʳ ρ⇐ᶠ      = unitorʳ.isoˡ

-- ----------------------------------------------------------------------------
-- §4: Morphism-level coherence — the loop reduction
-- ----------------------------------------------------------------------------

-- The solver primitive: to show `f` and `g` interpret equally, discharge the
-- single loop `invert g ∘ f`.
coherence-from-loop : {f g : X ⊸ Y} → ⟦ invert g ⊚ f ⟧₁ ≈ id → ⟦ f ⟧₁ ≈ ⟦ g ⟧₁
coherence-from-loop {f = f} {g} loop = begin
  ⟦ f ⟧₁                               ≈⟨ introˡ (invert-isoʳ g) ⟩
  (⟦ g ⟧₁ ∘ ⟦ invert g ⟧₁) ∘ ⟦ f ⟧₁     ≈⟨ pullʳ loop ⟩
  ⟦ g ⟧₁ ∘ id                          ≈⟨ identityʳ ⟩
  ⟦ g ⟧₁                               ∎

-- ----------------------------------------------------------------------------
-- §5: Naturality of strictification
-- ----------------------------------------------------------------------------

private
  id⊗α-cancel : (id {P} ⊗₁ α⇐ {Q} {R} {S}) ∘ (id ⊗₁ α⇒) ≈ id
  id⊗α-cancel = ⊗-cancel identity² associator.isoˡ

  assoc-shuffle
    : α⇒ {P ⊗₀ Q} {R} {S} ∘ (α⇐ {P} {Q} {R} ⊗₁ id) ∘ α⇐ {P} {Q ⊗₀ R} {S}
      ≈ α⇐ {P} {Q} {R ⊗₀ S} ∘ (id ⊗₁ α⇒ {Q} {R} {S})
  assoc-shuffle = begin
    α⇒ ∘ ((α⇐ ⊗₁ id) ∘ α⇐)                               ≈⟨ refl⟩∘⟨ pentagon-tail ⟩
    α⇒ ∘ ((α⇐ ∘ α⇐) ∘ (id ⊗₁ α⇒))                        ≈⟨ refl⟩∘⟨ assoc ⟩
    α⇒ ∘ α⇐ ∘ α⇐ ∘ (id ⊗₁ α⇒)                            ≈⟨ cancelˡ associator.isoʳ ⟩
    α⇐ ∘ (id ⊗₁ α⇒)                                      ∎
    where
      pentagon-tail : (α⇐ {P} {Q} {R} ⊗₁ id {S}) ∘ α⇐ {P} {Q ⊗₀ R} {S}
                      ≈ (α⇐ {P ⊗₀ Q} {R} {S} ∘ α⇐ {P} {Q} {R ⊗₀ S}) ∘ (id {P} ⊗₁ α⇒ {Q} {R} {S})
      pentagon-tail = begin
        (α⇐ ⊗₁ id) ∘ α⇐                                  ≈⟨ insertʳ id⊗α-cancel ⟩
        (((α⇐ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ α⇐)) ∘ (id ⊗₁ α⇒)    ≈⟨ pentagon-inv ⟩∘⟨refl ⟩
        (α⇐ ∘ α⇐) ∘ (id ⊗₁ α⇒)                           ∎

  λ⇐-assoc : α⇒ ∘ (λ⇐ {P} ⊗₁ id {Q}) ≈ λ⇐
  λ⇐-assoc = begin
    α⇒ ∘ (λ⇐ ⊗₁ id)            ≈⟨ refl⟩∘⟨ ⟺ coherence-inv₁ ⟩
    α⇒ ∘ (α⇐ ∘ λ⇐)             ≈⟨ cancelˡ associator.isoʳ ⟩
    λ⇐ ∎

  ρ⇒-assoc : ρ⇒ ∘ α⇐ {P} {Q} {unit} ≈ id ⊗₁ ρ⇒
  ρ⇒-assoc = begin
    ρ⇒ ∘ α⇐                    ≈˘⟨ coherence₂ ⟩∘⟨refl ⟩
    (id ⊗₁ ρ⇒ ∘ α⇒) ∘ α⇐       ≈⟨ cancelʳ associator.isoʳ ⟩
    id ⊗₁ ρ⇒                   ∎

-- `μ⇒ x y` is the forward direction of the homomorphism's multiplicativity
-- witness: it merges two normalized products.
μ⇒ : (x y : List Atom) → eval (x ++ y) ⇒ (eval x ⊗₀ eval y)
μ⇒ x y = _≅_.from (eval-homo x y)

private
  μₙ : (A B : Ob) → eval (nf (A ⊗ B)) ⇒ (eval (nf A) ⊗₀ eval (nf B))
  μₙ A B = μ⇒ (nf A) (nf B)

-- Coercion of interpretations along an equality of words.
substₑ : {x y : List Atom} → x ≡ y → eval x ⇒ eval y
substₑ refl = id

private
  module EvalCoercion where
    assocₑ : (A B C : Ob) → eval (nf ((A ⊗ B) ⊗ C)) ⇒ eval (nf (A ⊗ (B ⊗ C)))
    assocₑ A B C = substₑ (assocₙ A B C)

    unitʳₑ : (A : Ob) → eval (nf (A ⊗ I)) ⇒ eval (nf A)
    unitʳₑ A = substₑ (unitʳₙ A)

  open EvalCoercion

substₑ-cons : {b : Atom} {x y : List Atom} (p : x ≡ y)
  → substₑ (cong (b ∷_) p) ≈ id {⟦ b ⟧ₐ} ⊗₁ substₑ p
substₑ-cons refl = ⟺ ⊗.identity

-- Associativity coherence of the homomorphism.  This is the specialized
-- pentagon needed by strictifier naturality at the associator.
μ-assoc : (u v w : List Atom)
  → α⇒ ∘ (μ⇒ u v ⊗₁ id) ∘ μ⇒ (u ++ v) w
    ≈ (id ⊗₁ μ⇒ v w) ∘ μ⇒ u (v ++ w) ∘ substₑ (++-assoc u v w)
μ-assoc [] v w = begin
  α⇒ ∘ (λ⇐ ⊗₁ id) ∘ μ⇒ v w        ≈⟨ pullˡ λ⇐-assoc ⟩
  λ⇐ ∘ μ⇒ v w                     ≈⟨ unitorˡ-commute-to ⟩
  (id ⊗₁ μ⇒ v w) ∘ λ⇐             ≈˘⟨ refl⟩∘⟨ identityʳ ⟩
  (id ⊗₁ μ⇒ v w) ∘ λ⇐ ∘ id        ∎

μ-assoc (b ∷ bs) v w = begin
  α⇒ ∘ (μ⇒ (b ∷ bs) v ⊗₁ id) ∘ μ⇒ (b ∷ (bs ++ v)) w
    -- Expand the leading atom and collect the tail associativity problem.
    ≈⟨ refl⟩∘⟨ split₁ˡ ⟩∘⟨refl ⟩
  α⇒ ∘ ((α⇐ ⊗₁ id) ∘ ((id ⊗₁ μ-bs-v) ⊗₁ id)) ∘ (α⇐ ∘ (id ⊗₁ μ-bsv-w))
    ≈⟨ refl⟩∘⟨ pullʳ (pullˡ (⟺ assoc-commute-to)) ⟩
  α⇒ ∘ (α⇐ ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ (μ-bs-v ⊗₁ id))) ∘ (id ⊗₁ μ-bsv-w)
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullʳ merge₂ˡ ⟩
  α⇒ ∘ (α⇐ ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ ((μ-bs-v ⊗₁ id) ∘ μ-bsv-w)))
    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  α⇒ ∘ ((α⇐ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ ((μ-bs-v ⊗₁ id) ∘ μ-bsv-w))
    ≈⟨ pullˡ assoc-shuffle ⟩
  (α⇐ ∘ (id ⊗₁ α⇒)) ∘ (id ⊗₁ ((μ-bs-v ⊗₁ id) ∘ μ-bsv-w))
    ≈⟨ pullʳ merge₂ˡ ⟩
  α⇐ ∘ (id ⊗₁ (α⇒ ∘ (μ-bs-v ⊗₁ id) ∘ μ-bsv-w))
    -- Use the induction hypothesis under the right tensor.
    ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ μ-assoc bs v w ⟩
  α⇐ ∘ (id ⊗₁ ((id ⊗₁ μ-v-w) ∘ μ-bs-vw ∘ substₑ p))
    -- Rebuild the leading atom.
    ≈⟨ refl⟩∘⟨ split₂ˡ ⟩
  α⇐ ∘ ((id ⊗₁ (id ⊗₁ μ-v-w)) ∘ (id ⊗₁ (μ-bs-vw ∘ substₑ p)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₂ˡ ⟩
  α⇐ ∘ ((id ⊗₁ (id ⊗₁ μ-v-w)) ∘ ((id ⊗₁ μ-bs-vw) ∘ (id ⊗₁ substₑ p)))
    ≈⟨ pullˡ assoc-commute-to ⟩
  (((id ⊗₁ id) ⊗₁ μ-v-w) ∘ α⇐) ∘ ((id ⊗₁ μ-bs-vw) ∘ (id ⊗₁ substₑ p))
    ≈⟨ (⊗.identity ⟩⊗⟨refl) ⟩∘⟨refl ⟩∘⟨refl ⟩
  ((id ⊗₁ μ-v-w) ∘ α⇐) ∘ ((id ⊗₁ μ-bs-vw) ∘ (id ⊗₁ substₑ p))
    ≈⟨ assoc²γδ ⟩
  (id ⊗₁ μ-v-w) ∘ ((α⇐ ∘ (id ⊗₁ μ-bs-vw)) ∘ (id ⊗₁ substₑ p))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ (substₑ-cons p) ⟩
  (id ⊗₁ μ-v-w) ∘ μ⇒ (b ∷ bs) (v ++ w) ∘ substₑ p⁺
    ∎
  where
    p  = ++-assoc bs v w
    p⁺ = ++-assoc (b ∷ bs) v w

    μ-bs-v : eval (bs ++ v) ⇒ eval bs ⊗₀ eval v
    μ-bs-v = μ⇒ bs v

    μ-bsv-w : eval ((bs ++ v) ++ w) ⇒ eval (bs ++ v) ⊗₀ eval w
    μ-bsv-w = μ⇒ (bs ++ v) w

    μ-v-w : eval (v ++ w) ⇒ eval v ⊗₀ eval w
    μ-v-w = μ⇒ v w

    μ-bs-vw : eval (bs ++ (v ++ w)) ⇒ eval bs ⊗₀ eval (v ++ w)
    μ-bs-vw = μ⇒ bs (v ++ w)

private
  μ-assocₙ : (A B C : Ob)
    → α⇒ ∘ (μₙ A B ⊗₁ id) ∘ μₙ (A ⊗ B) C
      ≈ (id ⊗₁ μₙ B C) ∘ μₙ A (B ⊗ C) ∘ assocₑ A B C
  μ-assocₙ A B C = μ-assoc (nf A) (nf B) (nf C)

-- The co-strictifier: eval (nf X) ⇒ ⟦ X ⟧₀ (the `.from` of `strictify`). Its tensor
-- case exposes `μ⇒`, so the associator coherence lands on `μ-assoc`.
κ⁻¹ : (X : Ob) → eval (nf X) ⇒ ⟦ X ⟧₀
κ⁻¹ X = _≅_.from (strictify X)

-- coercions compose
substₑ-∘ : {x y z : List Atom} (p : x ≡ y) (q : y ≡ z) → substₑ (≡.trans p q) ≈ substₑ q ∘ substₑ p
substₑ-∘ refl q = ⟺ identityʳ

-- naturality of `μ⇒` along coercions
μ-natural : {x x' y y' : List Atom} (p : x ≡ x') (q : y ≡ y')
  → (substₑ p ⊗₁ substₑ q) ∘ μ⇒ x y ≈ μ⇒ x' y' ∘ substₑ (cong₂ _++_ p q)
μ-natural {x = x} {y = y} refl refl = begin
  (id ⊗₁ id) ∘ μ⇒ x y   ≈⟨ ⊗.identity ⟩∘⟨refl ⟩
  id ∘ μ⇒ x y           ≈⟨ id-comm-sym ⟩
  μ⇒ x y ∘ id           ∎

-- right-unit coherence of the homomorphism (the ρ analogue of `μ-assoc`)
μ-unitʳ : (x : List Atom) → ρ⇒ ∘ μ⇒ x [] ≈ substₑ (++-identityʳ x)
μ-unitʳ [] = begin
  ρ⇒ ∘ λ⇐                          ≈˘⟨ coherence₃ ⟩∘⟨refl ⟩
  λ⇒ ∘ λ⇐                          ≈⟨ unitorˡ.isoʳ ⟩
  id                               ∎
μ-unitʳ (b ∷ bs) = begin
  ρ⇒ ∘ (α⇐ ∘ (id ⊗₁ μ⇒ bs []))     ≈⟨ pullˡ ρ⇒-assoc ⟩
  (id ⊗₁ ρ⇒) ∘ (id ⊗₁ μ⇒ bs [])    ≈⟨ merge₂ˡ ⟩
  id ⊗₁ (ρ⇒ ∘ μ⇒ bs [])            ≈⟨ refl⟩⊗⟨ μ-unitʳ bs ⟩
  id ⊗₁ substₑ p                   ≈˘⟨ substₑ-cons p ⟩
  substₑ (++-identityʳ (b ∷ bs))   ∎
  where
    p  = ++-identityʳ bs

private
  μ-unitʳₙ : (A : Ob) → ρ⇒ ∘ μₙ A I ≈ unitʳₑ A
  μ-unitʳₙ A = μ-unitʳ (nf A)

  -- Naturality of the strictifier at the right unitor (forward direction).
  κ⁻¹-ρ⇒ : (X : Ob) → ρ⇒ ∘ κ⁻¹ (X ⊗ I) ≈ κ⁻¹ X ∘ unitʳₑ X
  κ⁻¹-ρ⇒ X = begin
    ρ⇒ ∘ ((κ⁻¹ X ⊗₁ id) ∘ μₙ X I)  ≈⟨ pullˡ unitorʳ-commute-from ⟩
    (κ⁻¹ X ∘ ρ⇒) ∘ μₙ X I          ≈⟨ pullʳ (μ-unitʳₙ X) ⟩
    κ⁻¹ X ∘ unitʳₑ X               ∎

  κ⁻¹[_⊗_] : (A B : Ob) → eval (nf A) ⊗₀ eval (nf B) ⇒ ⟦ A ⟧₀ ⊗₀ ⟦ B ⟧₀
  κ⁻¹[ A ⊗ B ] = κ⁻¹ A ⊗₁ κ⁻¹ B

  κ⁻¹-⊗-assoc : (A B C : Ob) → α⇒ ∘ (κ⁻¹[ A ⊗ B ] ⊗₁ κ⁻¹ C) ≈ (κ⁻¹ A ⊗₁ κ⁻¹[ B ⊗ C ]) ∘ α⇒
  κ⁻¹-⊗-assoc A B C = assoc-commute-from

  -- Naturality of the strictifier at the associator (forward direction); this is
  -- where `μ-assoc` discharges the work.
  κ⁻¹-α⇒ : (A B C : Ob)
    → α⇒ ∘ κ⁻¹ ((A ⊗ B) ⊗ C) ≈ κ⁻¹ (A ⊗ (B ⊗ C)) ∘ assocₑ A B C
  κ⁻¹-α⇒ A B C = begin
    α⇒ ∘ (((κ⁻¹[ A ⊗ B ] ∘ μₙ A B) ⊗₁ κ⁻¹ C) ∘ μₙ (A ⊗ B) C)
      ≈⟨ push-center split₁ʳ ⟩
    α⇒ ∘ ((κ⁻¹[ A ⊗ B ] ⊗₁ κ⁻¹ C) ∘ ((μₙ A B ⊗₁ id) ∘ μₙ (A ⊗ B) C))
      ≈⟨ pullˡ (κ⁻¹-⊗-assoc A B C) ⟩
    ((κ⁻¹ A ⊗₁ κ⁻¹[ B ⊗ C ]) ∘ α⇒) ∘ ((μₙ A B ⊗₁ id) ∘ μₙ (A ⊗ B) C)
      ≈⟨ pullʳ (μ-assocₙ A B C) ⟩
    (κ⁻¹ A ⊗₁ κ⁻¹[ B ⊗ C ]) ∘ ((id ⊗₁ μₙ B C) ∘ μₙ A (B ⊗ C) ∘ assocₑ A B C)
      ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    (κ⁻¹ A ⊗₁ κ⁻¹[ B ⊗ C ]) ∘ (((id ⊗₁ μₙ B C) ∘ μₙ A (B ⊗ C)) ∘ assocₑ A B C)
      ≈⟨ pull-first merge₂ʳ ⟩
    (κ⁻¹ A ⊗₁ (κ⁻¹[ B ⊗ C ] ∘ μₙ B C)) ∘ (μₙ A (B ⊗ C) ∘ assocₑ A B C)
      ≈⟨ sym-assoc ⟩
    ((κ⁻¹ A ⊗₁ (κ⁻¹[ B ⊗ C ] ∘ μₙ B C)) ∘ μₙ A (B ⊗ C)) ∘ assocₑ A B C
      ∎

-- `substₑ p` is an isomorphism with inverse `substₑ (≡.sym p)`.
substₑ-isoˡ : {x y : List Atom} (p : x ≡ y) → substₑ (≡.sym p) ∘ substₑ p ≈ id
substₑ-isoˡ refl = identity²

substₑ-isoʳ : {x y : List Atom} (p : x ≡ y) → substₑ p ∘ substₑ (≡.sym p) ≈ id
substₑ-isoʳ refl = identity²

private
  -- Naturality at an inverse generator follows from naturality at the generator:
  -- invert the interpretation on the left, the coercion on the right.
  κ⁻¹-natural-sym : {X Y : Ob} (p : nf X ≡ nf Y)
                    {u : ⟦ X ⟧₀ ⇒ ⟦ Y ⟧₀} {v : ⟦ Y ⟧₀ ⇒ ⟦ X ⟧₀} → v ∘ u ≈ id
                  → u ∘ κ⁻¹ X ≈ κ⁻¹ Y ∘ substₑ p
                  → v ∘ κ⁻¹ Y ≈ κ⁻¹ X ∘ substₑ (≡.sym p)
  κ⁻¹-natural-sym {X} {Y} p {u} {v} v∘u≈id nat = begin
    v ∘ κ⁻¹ Y                                    ≈⟨ refl⟩∘⟨ insertʳ (substₑ-isoʳ p) ⟩
    v ∘ ((κ⁻¹ Y ∘ substₑ p) ∘ substₑ (≡.sym p))  ≈˘⟨ refl⟩∘⟨ (nat ⟩∘⟨refl) ⟩
    v ∘ ((u ∘ κ⁻¹ X) ∘ substₑ (≡.sym p))         ≈⟨ refl⟩∘⟨ assoc ⟩
    v ∘ (u ∘ (κ⁻¹ X ∘ substₑ (≡.sym p)))         ≈⟨ cancelˡ v∘u≈id ⟩
    κ⁻¹ X ∘ substₑ (≡.sym p)                     ∎

-- The strictifier is natural: interpreting a structural morphism and then
-- co-strictifying equals co-strictifying and then coercing along the (equal)
-- object normal forms.
κ⁻¹-natural : ∀ {X Y} (f : X ⊸ Y) → ⟦ f ⟧₁ ∘ κ⁻¹ X ≈ κ⁻¹ Y ∘ substₑ (⇒⇒nf f)
κ⁻¹-natural {X} idₘ = begin
  id ∘ κ⁻¹ X  ≈⟨ identityˡ ⟩
  κ⁻¹ X       ≈˘⟨ identityʳ ⟩
  κ⁻¹ X ∘ id  ∎
κ⁻¹-natural (_⊚_ {X} {Y} {Z} g f) =
  let
    p = ⇒⇒nf f
    q = ⇒⇒nf g
  in begin
    (⟦ g ⟧₁ ∘ ⟦ f ⟧₁) ∘ κ⁻¹ X       ≈⟨ pullʳ (κ⁻¹-natural f) ⟩
    ⟦ g ⟧₁ ∘ (κ⁻¹ Y ∘ substₑ p)    ≈⟨ pullˡ (κ⁻¹-natural g) ⟩
    (κ⁻¹ Z ∘ substₑ q) ∘ substₑ p  ≈⟨ pullʳ (⟺ (substₑ-∘ p q)) ⟩
    κ⁻¹ Z ∘ substₑ (≡.trans p q)   ∎
κ⁻¹-natural (_⊗ˢ_ {X} {Y} {Z} {W} f g) =
  let
    p = ⇒⇒nf f
    q = ⇒⇒nf g
  in begin
    (⟦ f ⟧₁ ⊗₁ ⟦ g ⟧₁) ∘ (κ⁻¹[ X ⊗ Z ] ∘ μₙ X Z)          ≈⟨ pullˡ (⟺ ⊗-distrib-over-∘) ⟩
    ((⟦ f ⟧₁ ∘ κ⁻¹ X) ⊗₁ (⟦ g ⟧₁ ∘ κ⁻¹ Z)) ∘ μₙ X Z       ≈⟨ (κ⁻¹-natural f ⟩⊗⟨ κ⁻¹-natural g) ⟩∘⟨refl ⟩
    ((κ⁻¹ Y ∘ substₑ p) ⊗₁ (κ⁻¹ W ∘ substₑ q)) ∘ μₙ X Z  ≈⟨ pushˡ ⊗-distrib-over-∘ ⟩
    κ⁻¹[ Y ⊗ W ] ∘ ((substₑ p ⊗₁ substₑ q) ∘ μₙ X Z)     ≈⟨ refl⟩∘⟨ μ-natural p q ⟩
    κ⁻¹[ Y ⊗ W ] ∘ (μₙ Y W ∘ substₑ (cong₂ _++_ p q))    ≈⟨ sym-assoc ⟩
    (κ⁻¹[ Y ⊗ W ] ∘ μₙ Y W) ∘ substₑ (cong₂ _++_ p q)    ∎
κ⁻¹-natural (λ⇒ᶠ {X}) = begin
  λ⇒ ∘ ((id ⊗₁ κ⁻¹ X) ∘ λ⇐)   ≈⟨ pullˡ unitorˡ-commute-from ⟩
  (κ⁻¹ X ∘ λ⇒) ∘ λ⇐           ≈⟨ cancelʳ unitorˡ.isoʳ ⟩
  κ⁻¹ X                       ≈˘⟨ identityʳ ⟩
  κ⁻¹ X ∘ id                  ∎
κ⁻¹-natural (λ⇐ᶠ {X}) = begin
  λ⇐ ∘ κ⁻¹ X                  ≈⟨ unitorˡ-commute-to ⟩
  (id ⊗₁ κ⁻¹ X) ∘ λ⇐          ≈˘⟨ identityʳ ⟩
  ((id ⊗₁ κ⁻¹ X) ∘ λ⇐) ∘ id   ∎
κ⁻¹-natural (ρ⇒ᶠ {X})         = κ⁻¹-ρ⇒ X
κ⁻¹-natural (α⇒ᶠ {A} {B} {C}) = κ⁻¹-α⇒ A B C
κ⁻¹-natural (α⇐ᶠ {A} {B} {C}) =
  κ⁻¹-natural-sym {(A ⊗ B) ⊗ C} {A ⊗ (B ⊗ C)} (assocₙ A B C) associator.isoˡ (κ⁻¹-α⇒ A B C)
κ⁻¹-natural (ρ⇐ᶠ {X}) =
  κ⁻¹-natural-sym {X ⊗ I} {X} (unitʳₙ X) unitorʳ.isoˡ (κ⁻¹-ρ⇒ X)

-- Coherence for loops whose induced normal-form equality computes to `refl`.
-- This is the entry point used by the reflection macro.
loop-trivial : ∀ {X} (h : X ⊸ X) → ⇒⇒nf h ≡ refl → ⟦ h ⟧₁ ≈ id
loop-trivial {X} h h-refl = begin
  ⟦ h ⟧₁                                            ≈⟨ introʳ (_≅_.isoʳ (strictify X)) ⟩
  ⟦ h ⟧₁ ∘ (κ⁻¹ X ∘ _≅_.to (strictify X))           ≈⟨ pullˡ (κ⁻¹-natural h) ⟩
  (κ⁻¹ X ∘ substₑ (⇒⇒nf h)) ∘ _≅_.to (strictify X)  ≈⟨ elimʳ coeₕ≈id ⟩∘⟨refl ⟩
  κ⁻¹ X ∘ _≅_.to (strictify X)                      ≈⟨ _≅_.isoʳ (strictify X) ⟩
  id                                                ∎
  where coeₕ≈id = Equiv.reflexive (cong substₑ h-refl)

coherence : ∀ {X Y} (f g : X ⊸ Y) → ⇒⇒nf (invert g ⊚ f) ≡ refl → ⟦ f ⟧₁ ≈ ⟦ g ⟧₁
coherence f g loop-refl =
  coherence-from-loop {f = f} {g = g} (loop-trivial (invert g ⊚ f) loop-refl)
