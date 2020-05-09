{-# OPTIONS --without-K --safe #-}
open import Categories.Category using (Category; module Definitions)

-- 'Heterogeneous' identity morphism and some laws about them.

module Categories.Morphism.HeterogeneousIdentity {o ℓ e} (C : Category o ℓ e) where

open import Level
open import Relation.Binary.PropositionalEquality

import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning.Iso as Reasoning

open Category C
open Definitions C
open Morphism C
open Reasoning C using (switch-tofromʳ)


-- If Agda was an extensional type theory, any pair of morphisms
--
--   f : A ⇒ B   and   g : A ⇒ C,
--
-- where `A ≡ B`, would belong to the same homset, even if `A` and `B`
-- are not definitionally equal.  In particular, the identity on `B`
-- could be given the type |id {B} : B ⇒ C|.
--
-- But Agda is an intensional type theory, so the identity cannot have
-- this type, in general.  Instead one needs to manually 'transport'
-- |id {B}| into the homset |B ⇒ C|.  Given |p : B ≡ C| one obtains
--
--   subst (B ⇒_) p (id {B})
--
-- Morphisms like thes are no longer identities (in the strict
-- sense) but they still enjoy many of the properties identities do.
--
-- To make this precise, this module introduces a notion of
-- 'heterogeneous identity', which is an identity morphism whose
-- domain and codomain are propositionally equal (but not necessarily
-- syntically equal).


-- A heterogeneous identity is just the transport of an identity
-- along a 'strict' equation of objects.

hid : ∀ {A B} (p : A ≡ B) → A ⇒ B
hid {A} p = subst (A ⇒_) p id

-- Lemmas about heterogeneous identities

hid-refl : ∀ {A : Obj} → hid refl ≈ id {A}
hid-refl = Equiv.refl

hid-trans : ∀ {A B C} (p : B ≡ C) (q : A ≡ B) →
            hid p ∘ hid q ≈ hid (trans q p)
hid-trans refl refl = identityˡ

hid-symˡ : ∀ {A B} (p : A ≡ B) → hid (sym p) ∘ hid p ≈ id {A}
hid-symˡ refl = identityˡ

hid-symʳ : ∀ {A B} (p : A ≡ B) → hid p ∘ hid (sym p) ≈ id {B}
hid-symʳ refl = identityˡ

hid-sym-sym : ∀ {A B} (p : A ≡ B) → hid (sym (sym p)) ≈ hid p
hid-sym-sym refl = Equiv.refl

hid-iso : ∀ {A B} (p : A ≡ B) → Iso (hid p) (hid (sym p))
hid-iso p = record { isoˡ = hid-symˡ p ; isoʳ = hid-symʳ p }

hid-≅ : ∀ {A B} (p : A ≡ B) → A ≅ B
hid-≅ p = record { from = hid p ; to = hid (sym p) ; iso = hid-iso p }

hid-cong : ∀ {A B} {p q : A ≡ B} → p ≡ q → hid p ≈ hid q
hid-cong refl = Equiv.refl

-- Transporting the domain/codomain is the same as
-- pre/post-composing with heterogeneous identity.

hid-subst-dom : ∀ {A B C} (p : A ≡ B) (f : B ⇒ C) →
                subst (_⇒ C) (sym p) f ≈ f ∘ hid p
hid-subst-dom refl f = Equiv.sym identityʳ

hid-subst-cod : ∀ {A B C} (f : A ⇒ B) (p : B ≡ C) →
                subst (A ⇒_) p f ≈ hid p ∘ f
hid-subst-cod f refl = Equiv.sym identityˡ

hid-subst₂ : ∀ {A B C D} (p : A ≡ B) (q : C ≡ D) (f : A ⇒ C) →
             subst₂ (_⇒_) p q f ≈ hid q ∘ f ∘ hid (sym p)
hid-subst₂ refl refl f = Equiv.sym (Equiv.trans identityˡ identityʳ)

hid-square : ∀ {A B C D} {f : A ⇒ B} {p : A ≡ C} {q : B ≡ D} {g : C ⇒ D} →
             (subst₂ _⇒_ p q f ≈ g) →
             CommutativeSquare f (hid p) (hid q) g
hid-square {f = f} {p} {q} {g} eq = switch-tofromʳ (hid-≅ p) (begin
  (hid q ∘ f) ∘ hid (sym p)     ≈⟨ assoc ⟩
  hid q ∘ f ∘ hid (sym p)       ≈˘⟨ hid-subst₂ p q f ⟩
  subst₂ _⇒_ p q f              ≈⟨ eq ⟩
  g                             ∎)
  where open HomReasoning
