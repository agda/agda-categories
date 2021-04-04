{-# OPTIONS --without-K --safe #-}

open import Categories.Bicategory using (Bicategory)

module Categories.Bicategory.Extras {o ℓ e t} (Bicat : Bicategory o ℓ e t) where

open import Data.Product using (_,_)

open import Categories.Category.Construction.Functors using (Functors; module curry)
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor using (flip-bifunctor)
open import Categories.Functor.Bifunctor.Properties
open import Categories.NaturalTransformation
  using (NaturalTransformation; ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)

import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR
import Categories.Morphism.IsoEquiv as IsoEquiv
open import Categories.NaturalTransformation.NaturalIsomorphism.Properties
  using (push-eq)

open Bicategory Bicat public
private
  variable
    A B C D : Obj
    f g h i : A ⇒₁ B
    α β γ δ : f ⇒₂ g

infixr 7 _∘ᵢ_
infixr 9 _▷ᵢ_
infixl 9 _◁ᵢ_
infixr 6 _⟩⊚⟨_ refl⟩⊚⟨_
infixl 7 _⟩⊚⟨refl

module ⊚ {A B C}          = Functor (⊚ {A} {B} {C})
module ⊚-assoc {A B C D}  = NaturalIsomorphism (⊚-assoc {A} {B} {C} {D})
module unitˡ {A B}        = NaturalIsomorphism (unitˡ {A} {B})
module unitʳ {A B}        = NaturalIsomorphism (unitʳ {A} {B})
module id {A}             = Functor (id {A})

unitorˡ : {A B : Obj} {f : A ⇒₁ B} → Mor._≅_ (hom A B) (id₁ ∘ₕ f) f
unitorˡ {_} {_} {f} = record
  { from = unitˡ.⇒.η (_ , f)
  ; to   = unitˡ.⇐.η (_ , f)
  ; iso  = unitˡ.iso (_ , f)
  }

module unitorˡ {A B f} = Mor._≅_ (unitorˡ {A} {B} {f})

unitorʳ : {A B : Obj} {f : A ⇒₁ B} → Mor._≅_ (hom A B) (f ∘ₕ id₁) f
unitorʳ {_} {_} {f} = record
  { from = unitʳ.⇒.η (f , _)
  ; to   = unitʳ.⇐.η (f , _)
  ; iso  = unitʳ.iso (f , _)
  }

module unitorʳ {A B f} = Mor._≅_ (unitorʳ {A} {B} {f})

associator : {A B C D : Obj} {f : D ⇒₁ B} {g : C ⇒₁ D} {h : A ⇒₁ C} →  Mor._≅_ (hom A B) ((f ∘ₕ g) ∘ₕ h) (f ∘ₕ g ∘ₕ h)
associator {_} {_} {_} {_} {f} {g} {h} = record
  { from = ⊚-assoc.⇒.η ((f , g) , h)
  ; to   = ⊚-assoc.⇐.η ((f , g) , h)
  ; iso  = ⊚-assoc.iso ((f , g) , h)
  }

module associator {A B C D} {f : C ⇒₁ B} {g : D ⇒₁ C} {h} = Mor._≅_ (associator {A = A} {B = B} {f = f} {g = g} {h = h})

module Shorthands where
  λ⇒ = unitorˡ.from
  λ⇐ = unitorˡ.to

  ρ⇒ = unitorʳ.from
  ρ⇐ = unitorʳ.to

  α⇒ = associator.from
  α⇐ = associator.to
open Shorthands

-- Two curried versions of ⊚.

-⊚[-] : Functor (hom A B) (Functors (hom B C) (hom A C))
-⊚[-] = curry.F₀ (flip-bifunctor ⊚)

[-]⊚- : Functor (hom B C) (Functors (hom A B) (hom A C))
[-]⊚- = curry.F₀ ⊚

-⊚_ : A ⇒₁ B → Functor (hom B C) (hom A C)
-⊚_ = Functor.F₀ -⊚[-]

_⊚- : B ⇒₁ C → Functor (hom A B) (hom A C)
_⊚- = Functor.F₀ [-]⊚-

-▷_ : ∀ {C} → f ⇒₂ g → NaturalTransformation (-⊚_ {C = C} f) (-⊚ g)
-▷_ = Functor.F₁ -⊚[-]

_◁- : ∀ {A} → f ⇒₂ g → NaturalTransformation (_⊚- {A = A} f) (g ⊚-)
_◁- = Functor.F₁ [-]⊚-

identity₂ˡ : id₂ ∘ᵥ α ≈ α
identity₂ˡ = hom.identityˡ

identity₂ʳ : α ∘ᵥ id₂ ≈ α
identity₂ʳ = hom.identityʳ

assoc₂ : (α ∘ᵥ β) ∘ᵥ γ ≈ α ∘ᵥ β ∘ᵥ γ
assoc₂ = hom.assoc

id₂◁ : id₂ {f = g} ◁ f ≈ id₂
id₂◁ = ⊚.identity

▷id₂ : f ▷ id₂ {f = g} ≈ id₂
▷id₂ = ⊚.identity

open hom.HomReasoning
open hom.Equiv
private
  module MR′ {A} {B} where
    open MR (hom A B) public hiding (push-eq)
    open Mor (hom A B) using (_≅_; module ≅) public
    open IsoEquiv (hom A B) using (⌞_⌟; _≃_) public
  open MR′
idᵢ  = λ {A B f} → ≅.refl {A} {B} {f}
_∘ᵢ_ = λ {A B f g h} α β → ≅.trans {A} {B} {f} {g} {h} β α

_⊚ᵢ_ : f ≅ h → g ≅ i → f ⊚₀ g ≅ h ⊚₀ i
α ⊚ᵢ β = record
  { from = from α ⊚₁ from β
  ; to   = to α ⊚₁ to β
  ; iso  = record
    { isoˡ = [ ⊚ ]-merge (isoˡ α) (isoˡ β) ○ ⊚.identity
    ; isoʳ = [ ⊚ ]-merge (isoʳ α) (isoʳ β) ○ ⊚.identity }
  }
  where open _≅_

_◁ᵢ_ : {g h : B ⇒₁ C} (α : g ≅ h) (f : A ⇒₁ B) → g ∘ₕ f ≅ h ∘ₕ f
α ◁ᵢ _ = α ⊚ᵢ idᵢ

_▷ᵢ_ : {f g : A ⇒₁ B} (h : B ⇒₁ C) (α : f ≅ g) → h ∘ₕ f ≅ h ∘ₕ g
_ ▷ᵢ α = idᵢ ⊚ᵢ α

⊚-resp-≈ : α ≈ β → γ ≈ δ → α ⊚₁ γ ≈ β ⊚₁ δ
⊚-resp-≈ p q = ⊚.F-resp-≈ (p , q)

⊚-resp-≈ˡ : α ≈ β → α ⊚₁ γ ≈ β ⊚₁ γ
⊚-resp-≈ˡ p = ⊚.F-resp-≈ (p , hom.Equiv.refl)

⊚-resp-≈ʳ : γ ≈ δ → α ⊚₁ γ ≈ α ⊚₁ δ
⊚-resp-≈ʳ q = ⊚.F-resp-≈ (hom.Equiv.refl , q)

_⟩⊚⟨_ : α ≈ β → γ ≈ δ → α ⊚₁ γ ≈ β ⊚₁ δ
_⟩⊚⟨_ = ⊚-resp-≈

refl⟩⊚⟨_ : γ ≈ δ → α ⊚₁ γ ≈ α ⊚₁ δ
refl⟩⊚⟨_ = ⊚-resp-≈ʳ

_⟩⊚⟨refl : α ≈ β → α ⊚₁ γ ≈ β ⊚₁ γ
_⟩⊚⟨refl = ⊚-resp-≈ˡ

∘ᵥ-distr-◁ : (α ◁ f) ∘ᵥ (β ◁ f) ≈ (α ∘ᵥ β) ◁ f
∘ᵥ-distr-◁ {f = f} = ⟺ (Functor.homomorphism (-⊚ f))

∘ᵥ-distr-▷ : (f ▷ α) ∘ᵥ (f ▷ β) ≈ f ▷ (α ∘ᵥ β)
∘ᵥ-distr-▷ {f = f} = ⟺ (Functor.homomorphism (f ⊚-))

λ⇒-∘ᵥ-▷ : λ⇒ ∘ᵥ (id₁ ▷ α) ≈ α ∘ᵥ λ⇒
λ⇒-∘ᵥ-▷ {α = α} = begin
  λ⇒ ∘ᵥ (id₁ ▷ α)    ≈˘⟨ refl⟩∘⟨ id.identity ⟩⊚⟨refl ⟩
  λ⇒ ∘ᵥ id.F₁ _ ⊚₁ α ≈⟨ unitˡ.⇒.commute (_ , α) ⟩
  α ∘ᵥ λ⇒            ∎

▷-∘ᵥ-λ⇐ : (id₁ ▷ α) ∘ᵥ λ⇐ ≈ λ⇐ ∘ᵥ α
▷-∘ᵥ-λ⇐ = conjugate-to (≅.sym unitorˡ) (≅.sym unitorˡ) λ⇒-∘ᵥ-▷

ρ⇒-∘ᵥ-◁ : ρ⇒ ∘ᵥ (α ◁ id₁) ≈ α ∘ᵥ ρ⇒
ρ⇒-∘ᵥ-◁ {α = α} = begin
  ρ⇒ ∘ᵥ (α ◁ id₁)      ≈˘⟨ refl⟩∘⟨ refl⟩⊚⟨ id.identity ⟩
  ρ⇒ ∘ᵥ (α ⊚₁ id.F₁ _) ≈⟨ unitʳ.⇒.commute (α , _) ⟩
  α ∘ᵥ ρ⇒              ∎

◁-∘ᵥ-ρ⇐ : (α ◁ id₁) ∘ᵥ ρ⇐ ≈ ρ⇐ ∘ᵥ α
◁-∘ᵥ-ρ⇐ = conjugate-to (≅.sym unitorʳ) (≅.sym unitorʳ) ρ⇒-∘ᵥ-◁

α⇐-◁-∘ₕ : α⇐ ∘ᵥ (γ ◁ (g ∘ₕ f)) ≈ ((γ ◁ g) ◁ f) ∘ᵥ α⇐
α⇐-◁-∘ₕ {γ = γ} {g = g} {f = f} = begin
  α⇐ ∘ᵥ (γ ◁ (g ∘ₕ f))    ≈˘⟨ refl⟩∘⟨ refl⟩⊚⟨ ⊚.identity ⟩
  α⇐ ∘ᵥ (γ ⊚₁ id₂ ⊚₁ id₂)  ≈⟨ ⊚-assoc.⇐.commute ((γ , id₂) , id₂) ⟩
  ((γ ◁ g) ◁ f) ∘ᵥ α⇐      ∎

α⇒-◁-∘ₕ : α⇒ ∘ᵥ γ ◁ g ◁ f ≈ γ ◁ (g ∘ₕ f) ∘ᵥ α⇒
α⇒-◁-∘ₕ = ⟺ (conjugate-to associator associator α⇐-◁-∘ₕ)

α⇐-▷-◁ : α⇐ ∘ᵥ (f ▷ (γ ◁ g)) ≈ ((f ▷ γ) ◁ g) ∘ᵥ α⇐
α⇐-▷-◁ {f = f} {γ = γ} {g = g} = ⊚-assoc.⇐.commute ((id₂ , γ) , id₂)

α⇒-▷-∘ₕ : α⇒ ∘ᵥ (f ∘ₕ g) ▷ γ ≈ f ▷ g ▷ γ ∘ᵥ α⇒
α⇒-▷-∘ₕ{f = f} {g = g} {γ = γ} = begin
  α⇒ ∘ᵥ (f ⊚₀ g) ▷ γ     ≈˘⟨ refl⟩∘⟨ ⊚.identity ⟩⊚⟨refl ⟩
  α⇒ ∘ᵥ (f ▷ id₂) ⊚₁ γ   ≈⟨ ⊚-assoc.⇒.commute ((id₂ , id₂) , γ) ⟩
  f ▷ g ▷ γ ∘ᵥ α⇒        ∎

α⇐-▷-∘ₕ : α⇐ ∘ᵥ (g ▷ (f ▷ γ)) ≈ ((g ∘ₕ f) ▷ γ) ∘ᵥ α⇐
α⇐-▷-∘ₕ = conjugate-from associator associator (⟺ α⇒-▷-∘ₕ)

◁-▷-exchg : ∀ {α : f ⇒₂ g} {β : h ⇒₂ i} → (i ▷ α) ∘ᵥ (β ◁ f) ≈ (β ◁ g) ∘ᵥ (h ▷ α)
◁-▷-exchg = [ ⊚ ]-commute

triangle-iso : {f : A ⇒₁ B} {g : B ⇒₁ C} →
               (g ▷ᵢ unitorˡ ∘ᵢ associator) ≃ (unitorʳ ◁ᵢ f)
triangle-iso = ⌞ triangle ⌟

triangle-inv : {f : A ⇒₁ B} {g : B ⇒₁ C} → α⇐ ∘ᵥ g ▷ λ⇐ ≈ ρ⇐ ◁ f
triangle-inv = _≃_.to-≈ triangle-iso

pentagon-iso : ∀ {E} {f : A ⇒₁ B} {g : B ⇒₁ C} {h : C ⇒₁ D} {i : D ⇒₁ E} →
               (i ▷ᵢ associator ∘ᵢ associator ∘ᵢ associator ◁ᵢ f) ≃
               (associator {f = i} {h} {g ∘ₕ f} ∘ᵢ associator)
pentagon-iso = ⌞ pentagon ⌟

pentagon-inv : ∀ {E} {f : A ⇒₁ B} {g : B ⇒₁ C} {h : C ⇒₁ D} {i : D ⇒₁ E} →
               (α⇐ ◁ f ∘ᵥ α⇐) ∘ᵥ i ▷ α⇐ ≈ α⇐ ∘ᵥ α⇐ {f = i} {h} {g ∘ₕ f}
pentagon-inv = _≃_.to-≈ pentagon-iso

module UnitorCoherence where

  -- Extra coherence laws for the unitors.
  --
  -- These are similar to the extra coherence laws for monoidal
  -- categories that Kelly proved admissible in 1964.  The proofs are
  -- largely the same.  See Categories.Category.Monoidal.Properties
  -- for the monoidal versions and
  --
  --   https://ncatlab.org/nlab/show/monoidal+category
  --
  -- for an explanation of the proof and references to Kelly's paper.

  open ComHom

  -- As described on nLab, we start by proving that the 'perimeters'
  -- of two large diagrams commute...

  id▷λ-perimeter : [ ((id₁ ⊚₀ id₁) ⊚₀ f) ⊚₀ g ⇒ id₁ ⊚₀ (f ⊚₀ g) ]⟨
                     α⇒ ◁ g       ⇒⟨ (id₁ ⊚₀ (id₁ ⊚₀ f)) ⊚₀ g ⟩
                     α⇒           ⇒⟨ id₁ ⊚₀ ((id₁ ⊚₀ f) ⊚₀ g) ⟩
                     id₁ ▷ α⇒     ⇒⟨ id₁ ⊚₀ (id₁ ⊚₀ (f ⊚₀ g)) ⟩
                     id₁ ▷ λ⇒
                   ≈ ρ⇒ ◁ f ◁ g   ⇒⟨ (id₁ ⊚₀ f) ⊚₀ g ⟩
                     α⇒
                   ⟩
  id▷λ-perimeter {f = f} {g = g} = begin
    id₁ ▷ λ⇒ ∘ᵥ id₁ ▷ α⇒ ∘ᵥ α⇒ ∘ᵥ α⇒ ◁ g   ≈⟨ refl⟩∘⟨ pentagon ⟩
    id₁ ▷ λ⇒ ∘ᵥ α⇒ ∘ᵥ α⇒                   ≈⟨ pullˡ triangle ⟩
    ρ⇒ ◁ (f ⊚₀ g) ∘ᵥ α⇒                    ≈˘⟨ refl⟩⊚⟨ ⊚.identity ⟩∘⟨refl ⟩
    ρ⇒ ⊚₁ (id₂ ◁ g) ∘ᵥ α⇒                  ≈˘⟨ ⊚-assoc.⇒.commute _ ⟩
    α⇒ ∘ᵥ ρ⇒ ◁ f ◁ g                       ∎

  ρ◁id-perimeter : [ ((f ⊚₀ g) ⊚₀ id₁) ⊚₀ id₁ ⇒ f ⊚₀ (g ⊚₀ id₁) ]⟨
                     α⇒ ◁ id₁     ⇒⟨ (f ⊚₀ (g ⊚₀ id₁)) ⊚₀ id₁ ⟩
                     α⇒           ⇒⟨ f ⊚₀ ((g ⊚₀ id₁) ⊚₀ id₁) ⟩
                     f ▷ α⇒       ⇒⟨ f ⊚₀ (g ⊚₀ (id₁ ⊚₀ id₁)) ⟩
                     f ▷ g ▷ λ⇒
                   ≈ ρ⇒ ◁ id₁     ⇒⟨ (f ⊚₀ g) ⊚₀ id₁ ⟩
                     α⇒
                   ⟩
  ρ◁id-perimeter {f = f} {g = g} = begin
    f ▷ g ▷ λ⇒ ∘ᵥ f ▷ α⇒ ∘ᵥ α⇒ ∘ᵥ α⇒ ◁ id₁   ≈⟨ refl⟩∘⟨ pentagon ⟩
    f ▷ g ▷ λ⇒ ∘ᵥ α⇒ ∘ᵥ α⇒                   ≈˘⟨ pushˡ (⊚-assoc.⇒.commute _) ⟩
    (α⇒ ∘ᵥ (f ▷ id₂) ⊚₁ λ⇒) ∘ᵥ α⇒       ≈⟨ pullʳ (⊚.identity ⟩⊚⟨refl ⟩∘⟨refl) ⟩
    α⇒ ∘ᵥ (f ⊚₀ g) ▷ λ⇒ ∘ᵥ α⇒           ≈⟨ refl⟩∘⟨ triangle ⟩
    α⇒ ∘ᵥ ρ⇒ ◁ id₁                      ∎

  -- ... which allow us to prove that the following triangles commute...

  id▷λ-coherence : [ id₁ ⊚₀ ((id₁ ⊚₀ f) ⊚₀ g) ⇒ id₁ ⊚₀ (f ⊚₀ g) ]⟨
                     id₁ ▷ (λ⇒ ◁ g)
                   ≈ id₁ ▷ α⇒         ⇒⟨ id₁ ⊚₀ (id₁ ⊚₀ (f ⊚₀ g)) ⟩
                     id₁ ▷ λ⇒
                   ⟩
  id▷λ-coherence {f = f} {g = g} = begin
      id₁ ▷ (λ⇒ ◁ g)
    ≈⟨ switch-fromtoʳ associator (⟺ (⊚-assoc.⇒.commute _)) ⟩
      (α⇒ ∘ᵥ (id₁ ▷ λ⇒) ◁ g) ∘ᵥ α⇐
    ≈⟨ (refl⟩∘⟨ switch-fromtoʳ associator triangle ⟩⊚⟨refl) ⟩∘⟨refl ⟩
      (α⇒ ∘ᵥ ((ρ⇒ ◁ f ∘ᵥ α⇐) ◁ g)) ∘ᵥ α⇐
    ≈⟨ pushˡ (pushʳ (Functor.homomorphism (-⊚ g))) ⟩
      (α⇒ ∘ᵥ ρ⇒ ◁ f ◁ g) ∘ᵥ (α⇐ ◁ g ∘ᵥ α⇐)
    ≈˘⟨ switch-fromtoʳ (associator ∘ᵢ (associator ⊚ᵢ idᵢ))
                       (hom.assoc ○ id▷λ-perimeter) ⟩
      id₁ ▷ λ⇒ ∘ᵥ id₁ ▷ α⇒
    ∎

  ρ◁id-coherence : [ ((f ⊚₀ g) ⊚₀ id₁) ⊚₀ id₁ ⇒ (f ⊚₀ g) ⊚₀ id₁ ]⟨
                     ρ⇒ ◁ id₁
                   ≈ α⇒ ◁ id₁          ⇒⟨ (f ⊚₀ (g ⊚₀ id₁)) ⊚₀ id₁ ⟩
                     (f ▷ ρ⇒) ◁ id₁
                   ⟩
  ρ◁id-coherence {f = f} {g = g} = begin
      ρ⇒ ◁ id₁
    ≈⟨ switch-fromtoˡ associator (⟺ ρ◁id-perimeter) ⟩
      α⇐ ∘ᵥ f ▷ g ▷ λ⇒ ∘ᵥ f ▷ α⇒ ∘ᵥ α⇒ ∘ᵥ α⇒ ◁ id₁
    ≈˘⟨ pullʳ (pushˡ (Functor.homomorphism (f ⊚-))) ⟩
      (α⇐ ∘ᵥ f ▷ (g ▷ λ⇒ ∘ᵥ α⇒)) ∘ᵥ α⇒ ∘ᵥ α⇒ ◁ id₁
    ≈⟨ pullˡ (pushˡ (refl⟩∘⟨ refl⟩⊚⟨ triangle)) ⟩
      (α⇐ ∘ᵥ f ▷ (ρ⇒ ◁ id₁) ∘ᵥ α⇒) ∘ᵥ α⇒ ◁ id₁
    ≈˘⟨ switch-fromtoˡ associator (⊚-assoc.⇒.commute _) ⟩∘⟨refl ⟩
      (f ▷ ρ⇒) ◁ id₁ ∘ᵥ α⇒ ◁ id₁
    ∎

  -- ... which are the results modulo (id₁ ⊚-) and (-⊚ id₁).

  unitorˡ-coherence : [ (id₁ ⊚₀ f) ⊚₀ g ⇒ f ⊚₀ g ]⟨
                        λ⇒ ◁ g
                      ≈ α⇒         ⇒⟨ id₁ ⊚₀ (f ⊚₀ g) ⟩
                        λ⇒
                      ⟩
  unitorˡ-coherence {f = f} {g = g} = push-eq unitˡ (begin
    id.F₁ _ ⊚₁ (λ⇒ ◁ g)     ≈⟨ id.identity ⟩⊚⟨refl ⟩
    id₁ ▷ (λ⇒ ◁ g)          ≈⟨ id▷λ-coherence ⟩
    id₁ ▷ λ⇒ ∘ᵥ id₁ ▷ α⇒    ≈˘⟨ Functor.homomorphism (id₁ ⊚-) ⟩
    id₁ ▷ (λ⇒ ∘ᵥ α⇒)        ≈˘⟨ id.identity ⟩⊚⟨refl ⟩
    id.F₁ _ ⊚₁ (λ⇒ ∘ᵥ α⇒)   ∎)

  unitorʳ-coherence : [ (f ⊚₀ g) ⊚₀ id₁ ⇒ f ⊚₀ g ]⟨
                        ρ⇒
                      ≈ α⇒         ⇒⟨ f ⊚₀ (g ⊚₀ id₁) ⟩
                        f ▷ ρ⇒
                      ⟩
  unitorʳ-coherence {f = f} {g = g} = push-eq unitʳ (begin
    ρ⇒ ⊚₁ id.F₁ _                ≈⟨ refl⟩⊚⟨ id.identity ⟩
    ρ⇒ ◁ id₁                     ≈⟨ ρ◁id-coherence ⟩
    (f ▷ ρ⇒) ◁ id₁ ∘ᵥ α⇒ ◁ id₁   ≈˘⟨ Functor.homomorphism (-⊚ id₁) ⟩
    (f ▷ ρ⇒ ∘ᵥ α⇒) ◁ id₁         ≈˘⟨ refl⟩⊚⟨ id.identity ⟩
    (f ▷ ρ⇒ ∘ᵥ α⇒) ⊚₁ id.F₁ _    ∎)

open UnitorCoherence public using (unitorˡ-coherence; unitorʳ-coherence)
