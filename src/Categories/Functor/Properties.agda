{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Properties where

-- Properties valid of all Functors
open import Level
open import Data.Product using (proj₁; proj₂; _,_; _×_; Σ)
open import Function.Surjection using (Surjective)
open import Function.Equivalence using (Equivalence)
open import Function.Equality using (Π; _⟶_; _⟨$⟩_; cong)
open import Relation.Binary using (_Preserves_⟶_)
open import Relation.Nullary

open import Categories.Category
open import Categories.Functor
import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning as Reas
open import Categories.Morphism.IsoEquiv as IsoEquiv
open import Categories.Morphism.Isomorphism

private
  variable
    o ℓ e o′ ℓ′ e′ : Level
    C D : Category o ℓ e

Contravariant : ∀ (C : Category o ℓ e) (D : Category o′ ℓ′ e′) → Set _
Contravariant C D = Functor (Category.op C) D

Faithful : Functor C D → Set _
Faithful {C = C} {D = D} F = ∀ {X Y} → (f g : C [ X , Y ]) → D [ F₁ f ≈ F₁ g ] → C [ f ≈ g ]
  where open Functor F

Full : Functor C D → Set _
Full {C = C} {D = D} F = ∀ {X Y} → Surjective {To = D.hom-setoid {F₀ X} {F₀ Y}} G
  where
    module C = Category C
    module D = Category D
    open Functor F
    G : ∀ {X Y} → (C.hom-setoid {X} {Y}) ⟶ D.hom-setoid {F₀ X} {F₀ Y}
    G = record { _⟨$⟩_ = F₁ ; cong = F-resp-≈ }

FullyFaithful : Functor C D → Set _
FullyFaithful F = Full F × Faithful F

-- Note that this is a constructive version of Essentially Surjective, which is
-- quite a strong assumption.
EssentiallySurjective : Functor C D → Set _
EssentiallySurjective {C = C} {D = D} F = (d : Category.Obj D) → Σ C.Obj (λ c → Functor.F₀ F c ≅ d)
  where
  open Morphism D
  module C = Category C

-- a series of [ Functor ]-respects-Thing combinators (with respects -> resp)

module _ (F : Functor C D) where
  private
    module C = Category C using (Obj; _∘_; _⇒_; id; module HomReasoning)
    module D = Category D
    module IsoC = IsoEquiv C
    module IsoD = IsoEquiv D
  open C hiding (_∘_)
  open Functor F
  open Morphism

  private
    variable
      A B E : Obj
      f g h i : A ⇒ B

  [_]-resp-∘ : C [ C [ f ∘ g ] ≈ h ] → D [ D [ F₁ f ∘ F₁ g ] ≈ F₁ h ]
  [_]-resp-∘ {f = f} {g = g} {h = h} eq = begin
    F₁ f D.∘ F₁ g    ≈˘⟨ homomorphism ⟩
    F₁ (C [ f ∘ g ]) ≈⟨ F-resp-≈ eq ⟩
    F₁ h             ∎
    where open D.HomReasoning

  [_]-resp-square : Definitions.CommutativeSquare C f g h i →
                    Definitions.CommutativeSquare D (F₁ f) (F₁ g) (F₁ h) (F₁ i)
  [_]-resp-square {f = f} {g = g} {h = h} {i = i} sq = begin
    D [ F₁ h ∘ F₁ f ]  ≈˘⟨ homomorphism ⟩
    F₁ (C [ h ∘ f ])   ≈⟨ F-resp-≈ sq ⟩
    F₁ (C [ i ∘ g ])   ≈⟨ homomorphism ⟩
    D [ F₁ i ∘ F₁ g ]  ∎
    where open D.HomReasoning

  [_]-resp-Iso : Iso C f g → Iso D (F₁ f) (F₁ g)
  [_]-resp-Iso {f = f} {g = g} iso = record
    { isoˡ = begin
      F₁ g D.∘ F₁ f    ≈⟨ [ isoˡ ]-resp-∘ ⟩
      F₁ C.id          ≈⟨ identity ⟩
      D.id             ∎
    ; isoʳ = begin
      F₁ f D.∘ F₁ g    ≈⟨ [ isoʳ ]-resp-∘ ⟩
      F₁ C.id          ≈⟨ identity ⟩
      D.id             ∎
    }
    where open Iso iso
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
      let ff = from full
          (a , sa) = surj A in begin
      ff ⟨$⟩ _≅_.to sa ∘ D.id ∘ _≅_.from sa ≈⟨ cong ff (E.refl⟩∘⟨ D.identityˡ) ⟩
      ff ⟨$⟩ _≅_.to sa ∘ _≅_.from sa        ≈⟨ cong ff (_≅_.isoˡ sa) ⟩
      ff ⟨$⟩ D.id                           ≈˘⟨ cong ff identity ⟩
      ff ⟨$⟩ F₁ C.id                        ≈⟨ faith _ _ (right-inverse-of full (F₁ C.id)) ⟩
      C.id ∎
    ; homomorphism = λ {X} {Y} {Z} {f} {g} →
      let
          (x , sx) = surj X
          (y , sy) = surj Y
          (z , sz) = surj Z
          fsx      = from sx
          tsz      = to sz
          ff {T₁} {T₂} = from (full {T₁} {T₂}) in
      faith _ _ (E.begin
      F₁ (ff ⟨$⟩ tsz ∘ (g ∘ f) ∘ fsx)                             E.≈⟨ right-inverse-of full _ ⟩
      (tsz ∘ (g ∘ f) ∘ fsx)                                      E.≈⟨ pullˡ (E.refl⟩∘⟨ (E.refl⟩∘⟨ introˡ (isoʳ sy))) ⟩
      (tsz ∘ g ∘ ((from sy ∘ to sy) ∘ f)) ∘ fsx                  E.≈⟨ pushʳ (E.refl⟩∘⟨ D.assoc) E.⟩∘⟨refl ⟩
      ((tsz ∘ g) ∘ (from sy ∘ (to sy ∘ f))) ∘ fsx                E.≈⟨ D.sym-assoc E.⟩∘⟨refl ⟩
      (((tsz ∘ g) ∘ from sy) ∘ (to sy ∘ f)) ∘ fsx                E.≈⟨ D.assoc ⟩
      ((tsz ∘ g) ∘ from sy) ∘ ((to sy ∘ f) ∘ fsx)                E.≈⟨ D.assoc E.⟩∘⟨ D.assoc  ⟩
      (tsz ∘ g ∘ from sy) ∘ (to sy ∘ f ∘ fsx)                    E.≈˘⟨ right-inverse-of full _ E.⟩∘⟨ right-inverse-of full _ ⟩
      F₁ (ff ⟨$⟩ tsz ∘ g ∘ from sy) ∘ F₁ (ff ⟨$⟩ to sy ∘ f ∘ fsx)  E.≈˘⟨ homomorphism ⟩
      F₁ ((ff ⟨$⟩ tsz ∘ g ∘ from sy) C.∘ (ff ⟨$⟩ to sy ∘ f ∘ fsx)) E.∎)
    ; F-resp-≈ = λ f≈g → cong (from full) (D.∘-resp-≈ʳ (D.∘-resp-≈ˡ f≈g))
    }
    where
    open Morphism._≅_
    open Morphism D
    open Reas D
    open Category D
    open Surjective
    open C.HomReasoning
    module E = D.HomReasoning

-- Functor Composition is Associative and the unit laws are found in
-- NaturalTransformation.NaturalIsomorphism, reified as associator, unitorˡ and unitorʳ.
