{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Properties where

-- Properties valid of all Functors
open import Level
open import Data.Product using (proj₁; proj₂; _,_)
open import Function.Surjection using (Surjective)
open import Function.Equivalence using (Equivalence)
open import Function.Equality hiding (_∘_)

open import Categories.Category
open import Categories.Functor.Core
open import Categories.Functor
open import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning as Reas
open import Categories.Morphism.IsoEquiv as IsoEquiv
open import Categories.Morphism.Isomorphism

open import Relation.Binary using (_Preserves_⟶_)

private
  variable
    o ℓ e : Level
    C D : Category o ℓ e

-- a series of [ Functor ]-respects-Thing combinators (with respects -> resp)

module _ (F : Functor C D) where
  private
    module C = Category C
    module D = Category D
    module IsoC = IsoEquiv C
    module IsoD = IsoEquiv D
  open C hiding (_∘_)
  open Functor F

  private
    variable
      A B E : Obj
      f g h i : A ⇒ B

  [_]-resp-∘ : C [ C [ f ∘ g ] ≈ h ] → D [ D [ F₁ f ∘ F₁ g ] ≈ F₁ h ]
  [_]-resp-∘ {f = f} {g = g} {h = h} eq = begin
    F₁ f ∘ F₁ g      ≈˘⟨ homomorphism ⟩
    F₁ (C [ f ∘ g ]) ≈⟨ F-resp-≈ eq ⟩
    F₁ h             ∎
    where open D
          open D.HomReasoning

  [_]-resp-square : C.CommutativeSquare f g h i →
                    D.CommutativeSquare (F₁ f) (F₁ g) (F₁ h) (F₁ i)
  [_]-resp-square {f = f} {g = g} {h = h} {i = i} sq = begin
    F₁ h ∘ F₁ f      ≈˘⟨ homomorphism ⟩
    F₁ (C [ h ∘ f ]) ≈⟨ F-resp-≈ sq ⟩
    F₁ (C [ i ∘ g ]) ≈⟨ homomorphism ⟩
    F₁ i ∘ F₁ g       ∎
    where open D
          open D.HomReasoning

  [_]-resp-Iso : Iso C f g → Iso D (F₁ f) (F₁ g)
  [_]-resp-Iso {f = f} {g = g} iso = record
    { isoˡ = begin
      F₁ g ∘ F₁ f      ≈⟨ [ isoˡ ]-resp-∘ ⟩
      F₁ C.id          ≈⟨ identity ⟩
      D.id             ∎
    ; isoʳ = begin
      F₁ f ∘ F₁ g      ≈⟨ [ isoʳ ]-resp-∘ ⟩
      F₁ C.id          ≈⟨ identity ⟩
      D.id             ∎
    }
    where open Iso iso
          open D
          open D.HomReasoning

  [_]-resp-≅ : F₀ Preserves _≅_ C ⟶ _≅_ D
  [_]-resp-≅ i≅j = record
    { from       = F₁ from
    ; to         = F₁ to
    ; iso        = [ iso ]-resp-Iso
    }
    where open _≅_ i≅j

  [_]-resp-≃ : ∀ {f g :  _≅_ C A B} → f IsoC.≃ g → [ f ]-resp-≅ IsoD.≃ [ g ]-resp-≅
  [_]-resp-≃ ⌞ eq ⌟ = ⌞ F-resp-≈ eq ⌟

  homomorphismᵢ : ∀ {f : _≅_ C B E} {g : _≅_ C A B} → [ _∘ᵢ_ C f g ]-resp-≅ IsoD.≃ (_∘ᵢ_ D [ f ]-resp-≅ [ g ]-resp-≅ )
  homomorphismᵢ = ⌞ homomorphism ⌟

  -- Uses a strong version of Essential Surjectivity.
  EssSurj×Full×Faithful⇒Invertible : EssentiallySurjective F → Full F → Faithful F → Functor D C
  EssSurj×Full×Faithful⇒Invertible surj full faith = record
    { F₀ = λ d → proj₁ (surj d)
    ; F₁ = λ {A} {B} f →
      let (a , sa) = surj A in
      let (b , sb) = surj B in
      let module S = Surjective (full {a} {b}) in
      S.from ⟨$⟩ (_≅_.to sb) ∘ f ∘ (_≅_.from sa)
    ; identity = λ {A} →
      let (a , sa) = surj A in begin
      from full ⟨$⟩  _≅_.to sa ∘ D.id ∘ _≅_.from sa ≈⟨ cong (from full) (D.∘-resp-≈ʳ D.identityˡ D.HomReasoning.○ _≅_.isoˡ sa) ⟩
      from full ⟨$⟩ D.id                            ≈˘⟨ cong (from full) identity ⟩
      from full ⟨$⟩ F₁ C.id                         ≈⟨ faith _ _ (right-inverse-of full (F₁ C.id)) ⟩
      C.id ∎
    ; homomorphism = λ {X} {Y} {Z} {f} {g} →
      let (x , sx) = surj X in
      let (y , sy) = surj Y in
      let (z , sz) = surj Z in
      let open Morphism._≅_ in faith _ _ (E.begin
      F₁ (from full ⟨$⟩ to sz ∘ (g ∘ f) ∘ from sx)                                     E.≈⟨ right-inverse-of full _ ⟩
      (to sz ∘ (g ∘ f) ∘ from sx)                                                      E.≈⟨ D.∘-resp-≈ʳ (D.∘-resp-≈ˡ (D.∘-resp-≈ʳ (introˡ (isoʳ sy)))) ⟩
      (to sz ∘ (g ∘ (from sy ∘ to sy) ∘ f) ∘ from sx)                                  E.≈⟨ D.sym-assoc ⟩
      (to sz ∘ g ∘ ((from sy ∘ to sy) ∘ f)) ∘ from sx                                  E.≈⟨ D.∘-resp-≈ˡ (D.∘-resp-≈ʳ (D.∘-resp-≈ʳ D.assoc)) ⟩
      (to sz ∘ g ∘ (from sy ∘ (to sy ∘ f))) ∘ from sx                                  E.≈⟨ D.∘-resp-≈ˡ D.sym-assoc ⟩
      ((to sz ∘ g) ∘ (from sy ∘ (to sy ∘ f))) ∘ from sx                                E.≈⟨ D.∘-resp-≈ˡ D.sym-assoc ⟩
      (((to sz ∘ g) ∘ from sy) ∘ (to sy ∘ f)) ∘ from sx                                E.≈⟨ D.assoc ⟩
      ((to sz ∘ g) ∘ from sy) ∘ ((to sy ∘ f) ∘ from sx)                                E.≈⟨ D.∘-resp-≈ D.assoc D.assoc  ⟩
      (to sz ∘ g ∘ from sy) ∘ (to sy ∘ f ∘ from sx)                                    E.≈˘⟨ D.∘-resp-≈ (right-inverse-of full _) (right-inverse-of full _) ⟩
      F₁ (from full ⟨$⟩ to sz ∘ g ∘ from sy) ∘ F₁ (from full ⟨$⟩ to sy ∘ f ∘ from sx)  E.≈˘⟨ homomorphism ⟩
      F₁ ((from full ⟨$⟩ to sz ∘ g ∘ from sy) C.∘ (from full ⟨$⟩ to sy ∘ f ∘ from sx)) E.∎)
    ; F-resp-≈ = λ f≈g → cong (from full) (D.∘-resp-≈ʳ (D.∘-resp-≈ˡ f≈g))
    }
    where
    open Morphism D
    open Reas D
    open Category D
    open Surjective
    open C.HomReasoning
    module E = D.HomReasoning

-- Functor Composition is Associative and the unit laws are found in
-- NaturalTransformation.NaturalIsomorphism, reified as associator, unitorˡ and unitorʳ.
