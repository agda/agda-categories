{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Properties where

-- Properties valid of all Functors
open import Level using (Level)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Function.Base using (_$_)
open import Function.Definitions using (Injective; StrictlySurjective)
open import Relation.Binary using (_Preserves_⟶_)

open import Categories.Category using (Category; _[_,_]; _[_≈_]; _[_∘_]; module Definitions)
open import Categories.Category.Construction.Core using (module Shorthands)
open import Categories.Functor.Core using (Functor)
import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning as Reas
open import Categories.Morphism.IsoEquiv as IsoEquiv
open import Categories.Morphism.Notation

open Shorthands using (_∘ᵢ_)

private
  variable
    o ℓ e o′ ℓ′ e′ : Level
    C D : Category o ℓ e

Contravariant : ∀ (C : Category o ℓ e) (D : Category o′ ℓ′ e′) → Set _
Contravariant C D = Functor (Category.op C) D

Faithful : Functor C D → Set _
Faithful {C = C} {D = D} F = ∀ {X Y} → Injective {A = C [ X , Y ]} (C [_≈_]) (D [_≈_]) F₁
  where open Functor F

Full : Functor C D → Set _
Full {C = C} {D = D} F = ∀ {X Y} → StrictlySurjective {A = C [ X , Y ]} (D [_≈_]) F₁
  where open Functor F

FullyFaithful : Functor C D → Set _
FullyFaithful F = Full F × Faithful F

-- Note that this is a constructive version of Essentially Surjective, which is
-- quite a strong assumption.
EssentiallySurjective : Functor C D → Set _
EssentiallySurjective {C = C} {D = D} F = (d : Category.Obj D) → Σ C.Obj (λ c → Functor.F₀ F c ≅ d)
  where
  open Morphism D
  module C = Category C

Conservative : Functor C D → Set _
Conservative {C = C} {D = D} F = ∀ {A B} {f : C [ A , B ]} {g : D [ F₀ B , F₀ A ]} → Iso D (F₁ f) g → Σ (C [ B , A ]) (Iso C f)
  where
    open Functor F
    open Morphism

PreservesCoequalizers : Functor C D → Set _
PreservesCoequalizers {C = C} {D = D} F = ∀ {A B : C.Obj} {f g : A C.⇒ B} {coeq : Coequalizer C f g}
                      → IsCoequalizer D (F₁ f) (F₁ g) (F₁ (arr coeq))
  where
    module C = Category C
    open Functor F
    open import Categories.Diagram.Coequalizer
    open Coequalizer

-- a series of [ Functor ]-respects-Thing combinators (with respects -> resp)

module _ (F : Functor C D) where
  private
    module C = Category C
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
      let (a , sa) = surj A
          (b , sb) = surj B
      in proj₁ (full (_≅_.to sb ∘ f ∘ _≅_.from sa))
    ; identity = λ {A} →
      let (a , sa) = surj A
          (f , p) = full (_≅_.to sa ∘ D.id ∘ _≅_.from sa)
      in faith $ begin
        F₁ f                           ≈⟨ p ⟩
        _≅_.to sa ∘ D.id ∘ _≅_.from sa ≈⟨ refl⟩∘⟨ D.identityˡ ⟩
        _≅_.to sa ∘ _≅_.from sa        ≈⟨ _≅_.isoˡ sa ⟩
        D.id                           ≈˘⟨ identity ⟩
        F₁ C.id                        ∎
    ; homomorphism = λ {X} {Y} {Z} {f} {g} →
      let (a , sa) = surj X
          (b , sb) = surj Y
          (c , sc) = surj Z
          (⟨g∘f⟩ , p) = full (_≅_.to sc ∘ (g ∘ f) ∘ _≅_.from sa)
          (⟨f⟩ , q) = full (_≅_.to sb ∘ f ∘ _≅_.from sa)
          (⟨g⟩ , r) = full (_≅_.to sc ∘ g ∘ _≅_.from sb)
      in faith $ begin
        F₁ ⟨g∘f⟩                                                        ≈⟨ p ⟩
        _≅_.to sc ∘ (g ∘ f) ∘ _≅_.from sa                               ≈⟨ assoc²δγ ⟩
        (_≅_.to sc ∘ g) ∘ (f ∘ _≅_.from sa)                             ≈⟨ insertInner (_≅_.isoʳ sb) ⟩
        ((_≅_.to sc ∘ g) ∘ _≅_.from sb) ∘ (_≅_.to sb ∘ f ∘ _≅_.from sa) ≈⟨ D.assoc ⟩∘⟨refl ⟩
        (_≅_.to sc ∘ g ∘ _≅_.from sb) ∘ (_≅_.to sb ∘ f ∘ _≅_.from sa)   ≈˘⟨ (r ⟩∘⟨ q ) ⟩
        F₁ ⟨g⟩ ∘ F₁ ⟨f⟩                                                 ≈˘⟨ homomorphism ⟩
        F₁ (⟨g⟩ C.∘ ⟨f⟩)                                                ∎
    ; F-resp-≈ = λ {X} {Y} {f} {g} f≈g →
      let sa = proj₂ (surj X)
          sb = proj₂ (surj Y)
          (⟨f⟩ , p) = full (_≅_.to sb ∘ f ∘ _≅_.from sa)
          (⟨g⟩ , q) = full (_≅_.to sb ∘ g ∘ _≅_.from sa)
      in faith $ begin
        F₁ ⟨f⟩                      ≈⟨ p ⟩
        _≅_.to sb ∘ f ∘ _≅_.from sa ≈⟨ refl⟩∘⟨ f≈g ⟩∘⟨refl ⟩
        _≅_.to sb ∘ g ∘ _≅_.from sa ≈˘⟨ q ⟩
        F₁ ⟨g⟩                      ∎
    }
    where
      open Category D
      open D.HomReasoning
      open Reas D

-- Functor Composition is Associative and the unit laws are found in
-- NaturalTransformation.NaturalIsomorphism, reified as associator, unitorˡ and unitorʳ.
