{-# OPTIONS --without-K --safe #-}
module Categories.Adjoint.Relative where

-- Relative Adjoints, in their biased, level-restricted version
--   In other words, this uses the Hom-Setoid equivalent variant
--   of the adjoint formulation because relative adjoints don't
--   have a natural unit/counit formulation.

-- We use the Altenkirch-Chapman-Uustalu formulation, which means
-- that what is adjoint is a Functor and a Category.

open import Level

open import Data.Product using (_,_; _×_)
open import Function using (_$_) renaming (_∘_ to _∙_)
open import Function.Equality using (Π; _⟶_; _⟨$⟩_)
open import Relation.Binary using (Setoid)

-- be explicit in imports to 'see' where the information comes from
open import Categories.Adjoint
open import Categories.Category.Core using (Category)
open import Categories.Category.Product using (Product; _⁂_)
open import Categories.Category.Instance.Setoids
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Functor.Hom using (Hom[_][-,-])
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (NaturalIsomorphism)
import Categories.Morphism.Reasoning as MR
open import Categories.Monad.Relative renaming (Monad to RMonad)

private
  variable
    o o′ ℓ ℓ′ e e′ : Level
    E : Category o ℓ e

record RelativeAdjoint {C : Category o ℓ e} (D : Category o ℓ e) (J : Functor E C)  : Set (levelOfTerm D ⊔ levelOfTerm J) where
  field
    L : Functor E D
    R : Functor D C

  private
    module C = Category C
    module D = Category D
    module E = Category E
    module L = Functor L
    module R = Functor R
    module J = Functor J

  Hom[L-,-] : Bifunctor E.op D (Setoids _ _)
  Hom[L-,-] = Hom[ D ][-,-] ∘F (L.op ⁂ idF)

  Hom[J-,R-] : Bifunctor E.op D (Setoids _ _)
  Hom[J-,R-] = Hom[ C ][-,-] ∘F (J.op ⁂ R)

  module Hom[L-,-] = Functor Hom[L-,-]
  module Hom[J-,R-] = Functor Hom[J-,R-]

  field
    Hom-NI : NaturalIsomorphism Hom[J-,R-] Hom[L-,-]

RA⇒RMonad : {C D : Category o ℓ e} {E : Category o′ ℓ′ e′} {J : Functor E C} → RelativeAdjoint D J → RMonad J
RA⇒RMonad {C = C} {D} {E} {J} RA = record
  { F₀ = F₀ (R ∘F L)
  ; unit = λ {c} → ⇐.η (c , F₀ L c) ⟨$⟩ D.id {F₀ L c}
  ; extend = λ {X} {Y} k → F₁ R (⇒.η (X , F₀ L Y) ⟨$⟩ k)
  ; identityʳ = idʳ
  ; identityˡ = R.F-resp-≈ (iso.isoʳ _ D.Equiv.refl) ○ R.identity
  ; assoc = a
  ; extend-≈ = λ k≈h → F-resp-≈ R (Π.cong (⇒.η _) k≈h)
  }
  where
  open RelativeAdjoint RA
  open Functor
  open NaturalIsomorphism Hom-NI
  module D = Category D
  module E = Category E
  module J = Functor J
  module L = Functor L
  module R = Functor R
  open Category C
  open HomReasoning
  open MR C
  idʳ : {x y : E.Obj} {k : J.₀ x ⇒ F₀ (R ∘F L) y} → R.₁ (⇒.η (x , L.₀ y) ⟨$⟩ k) ∘ (⇐.η (x , L.₀ x) ⟨$⟩ D.id) ≈ k
  idʳ {x} {y} {k} = begin
    R.₁ (⇒.η (x , L.₀ y) ⟨$⟩ k) ∘ (⇐.η (x , L.₀ x) ⟨$⟩ D.id)               ≈⟨ introʳ J.identity ⟩
    (R.₁ (⇒.η (x , L.₀ y) ⟨$⟩ k) ∘ (⇐.η (x , L.₀ x) ⟨$⟩ D.id)) ∘ J.₁ E.id  ≈⟨ assoc ⟩
    R.₁ (⇒.η (x , L.₀ y) ⟨$⟩ k) ∘ (⇐.η (x , L.₀ x) ⟨$⟩ D.id) ∘ J.₁ E.id    ≈⟨ ⇐.sym-commute (E.id , ⇒.η (x , L.₀ y) ⟨$⟩ k) (D.Equiv.refl) ⟩
    ⇐.η (x , L.₀ y) ⟨$⟩ ((⇒.η (x , L.₀ y) ⟨$⟩ k) D.∘ D.id D.∘ L.F₁ E.id)   ≈⟨ Π.cong (⇐.η _) (MR.elimʳ D (MR.elimʳ D L.identity)) ⟩
    ⇐.η (x , L.₀ y) ⟨$⟩ (⇒.η (x , L.₀ y) ⟨$⟩ k)                            ≈⟨ iso.isoˡ (x , _) Equiv.refl ⟩
    k            ∎
  a : {x y z : E.Obj} {k : J.₀ x ⇒ R.₀ (L.₀ y)} {l : J.₀ y ⇒ R.₀ (L.₀ z)} →
      R.₁ (⇒.η (x , L.₀ z) ⟨$⟩ R.₁ (⇒.η (y , L.₀ z) ⟨$⟩ l) ∘ k) ≈
      R.₁ (⇒.η (y , L.₀ z) ⟨$⟩ l) ∘ R.₁ (⇒.η (x , L.₀ y) ⟨$⟩ k)
  a {x} {y} {z} {k} {l} = begin
    R.₁ (⇒.η (x , L.₀ z) ⟨$⟩ (R.₁ (⇒.η (y , L.₀ z) ⟨$⟩ l) ∘ k)) ≈⟨ R.F-resp-≈ lemma ⟩
    R.₁ ((⇒.η (y , L.₀ z) ⟨$⟩ l) D.∘ (⇒.η (x , L.₀ y) ⟨$⟩ k))   ≈⟨ R.homomorphism ⟩
    R.₁ (⇒.η (y , L.₀ z) ⟨$⟩ l) ∘ R.₁ (⇒.η (x , L.₀ y) ⟨$⟩ k)   ∎
    where
    xz = (x , L.₀ z)
    yz = (y , L.₀ z)
    xy = (x , L.₀ y)
    module DR = D.HomReasoning
    lemma : ⇒.η xz ⟨$⟩ R.₁ (⇒.η yz ⟨$⟩ l) ∘ k D.≈ (⇒.η yz ⟨$⟩ l) D.∘ (⇒.η xy ⟨$⟩ k)
    lemma = DR.begin
      ⇒.η xz ⟨$⟩ R.₁ (⇒.η yz ⟨$⟩ l) ∘ k                DR.≈⟨ Π.cong (⇒.η xz) (refl⟩∘⟨ introʳ J.identity ) ⟩
      ⇒.η xz ⟨$⟩ R.₁ (⇒.η yz ⟨$⟩ l) ∘ (k ∘ J.₁ E.id)   DR.≈⟨ ⇒.commute (E.id , ⇒.η yz ⟨$⟩ l) Equiv.refl ⟩
      (⇒.η yz ⟨$⟩ l) D.∘ (⇒.η xy ⟨$⟩ k) D.∘ L.₁ E.id   DR.≈⟨ D.sym-assoc  ⟩
      ((⇒.η yz ⟨$⟩ l) D.∘ (⇒.η xy ⟨$⟩ k)) D.∘ L.₁ E.id DR.≈⟨ MR.elimʳ D L.identity ⟩
      (⇒.η yz ⟨$⟩ l) D.∘ (⇒.η xy ⟨$⟩ k) DR.∎

⊣⇒RAdjoint : {C D : Category o ℓ e} {E : Category o′ ℓ′ e′} (L : Functor C D) (R : Functor D C) (J : Functor E C) → L ⊣ R → RelativeAdjoint D J
⊣⇒RAdjoint {C = C} {D} L R J A = record
  { L = L ∘F J
  ; R = R
  ; Hom-NI = record
    { F⇒G = ntHelper record
      { η = λ _ → record { _⟨$⟩_ = Radjunct ; cong = ∘-resp-≈ʳ ∙ L.F-resp-≈ }
      ; commute = λ _ x≈y → Radjunct-comm x≈y
      }
    ; F⇐G = ntHelper record
      { η = λ _ → record { _⟨$⟩_ = Ladjunct ; cong = C.∘-resp-≈ˡ ∙ R.F-resp-≈ }
      ; commute = λ _ x≈y → Ladjunct-comm x≈y
      }
    ; iso = λ X → record
      { isoˡ = λ eq → LRadjunct≈id ○ eq
      ; isoʳ = Equiv.trans RLadjunct≈id
      }
    }
  }
  where
  open Adjoint A
  open Category D
  module C = Category C
  module L = Functor L
  module R = Functor R
  module J = Functor J
  open C.HomReasoning
