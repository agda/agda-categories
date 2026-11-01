{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Interchange using (HasInterchange)

-- Tensor products of enriched natural transformations.

module Categories.Enriched.NaturalTransformation.TensorProduct
  {o ℓ e} {V : Category o ℓ e} {M : Monoidal V} (I : HasInterchange M) where

open import Data.Product using (_,_)

import Categories.Enriched.Category as Enriched
open import Categories.Enriched.Category M using (_[_,_])

open Category V
open Monoidal M
open HasInterchange I using (module swapInner)
  renaming (natural to interchange-natural; unitˡ to interchange-unitˡ;
            unitʳ to interchange-unitʳ)
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Utilities M
open import Categories.Enriched.Category.TensorProduct I using (_⊠_)
open import Categories.Enriched.Functor M using (Functor)
open import Categories.Enriched.Functor.TensorProduct I using (_⊠F_)
open import Categories.Enriched.NaturalTransformation M using (NaturalTransformation)
open import Categories.Enriched.NaturalTransformation.NaturalIsomorphism M
  using (NaturalIsomorphism; _ᵢ[_])
open import Categories.Morphism.Reasoning V
open Shorthands
open NaturalIsomorphism

private
  variable
    P Q R S : Obj

  open swapInner using () renaming (from to i⇒)

  i⇒λ : i⇒ ∘ (λ⇐ ⊗₁ id) ≈ (λ⇐ {P} ⊗₁ λ⇐ {Q}) ∘ λ⇒
  i⇒λ = switch-fromtoˡ (unitorˡ ⊗ᵢ unitorˡ) interchange-unitˡ

  i⇒ρ : i⇒ ∘ (id ⊗₁ λ⇐) ≈ (ρ⇐ {P} ⊗₁ ρ⇐ {Q}) ∘ ρ⇒
  i⇒ρ = switch-fromtoˡ (unitorʳ ⊗ᵢ unitorʳ) interchange-unitʳ

  iλ² : i⇒ ∘ (λ⇐ ⊗₁ id) ∘ λ⇐ ≈ λ⇐ {P} ⊗₁ λ⇐ {Q}
  iλ² = begin
    i⇒ ∘ (λ⇐ ⊗₁ id) ∘ λ⇐        ≈⟨ pullˡ i⇒λ ⟩
    ((λ⇐ ⊗₁ λ⇐) ∘ λ⇒) ∘ λ⇐      ≈⟨ cancelʳ unitorˡ.isoʳ ⟩
    λ⇐ ⊗₁ λ⇐                    ∎

  iρ² : i⇒ ∘ (id ⊗₁ λ⇐) ∘ ρ⇐ ≈ ρ⇐ {P} ⊗₁ ρ⇐ {Q}
  iρ² = begin
    i⇒ ∘ (id ⊗₁ λ⇐) ∘ ρ⇐        ≈⟨ pullˡ i⇒ρ ⟩
    ((ρ⇐ ⊗₁ ρ⇐) ∘ ρ⇒) ∘ ρ⇐      ≈⟨ cancelʳ unitorʳ.isoʳ ⟩
    ρ⇐ ⊗₁ ρ⇐                    ∎

module _ {a b c d}
  {𝒜 : Enriched.Category M a} {ℬ : Enriched.Category M b}
  {𝒞 : Enriched.Category M c} {𝒟 : Enriched.Category M d} where

  private
    module 𝒜 = Enriched.Category 𝒜
    module ℬ = Enriched.Category ℬ
    module 𝒞 = Enriched.Category 𝒞
    module 𝒟 = Enriched.Category 𝒟
    module 𝒞⊠𝒟 = Enriched.Category (𝒞 ⊠ 𝒟)

    variable
      A B C : 𝒞.Obj
      X Y Z : 𝒟.Obj

  private abstract
    ⊚⊠ˡ : {p : unit ⇒ 𝒞 [ B , C ]} {q : unit ⇒ 𝒟 [ Y , Z ]}
      {f : R ⇒ 𝒞 [ A , B ]} {g : S ⇒ 𝒟 [ X , Y ]} →
      𝒞⊠𝒟.⊚ ∘ (((p ⊗₁ q) ∘ λ⇐) ⊗₁ (f ⊗₁ g)) ∘ λ⇐
      ≈ (𝒞.⊚ ∘ (p ⊗₁ f) ∘ λ⇐) ⊗₁ (𝒟.⊚ ∘ (q ⊗₁ g) ∘ λ⇐)
    ⊚⊠ˡ {p = p} {q} {f} {g} = begin
      𝒞⊠𝒟.⊚ ∘ (((p ⊗₁ q) ∘ λ⇐) ⊗₁ (f ⊗₁ g)) ∘ λ⇐
        ≈⟨ pullʳ (refl⟩∘⟨ pushˡ split₁ʳ) ⟩
      (𝒞.⊚ ⊗₁ 𝒟.⊚) ∘ i⇒ ∘ ((p ⊗₁ q) ⊗₁ (f ⊗₁ g)) ∘
        (λ⇐ ⊗₁ id) ∘ λ⇐
        ≈⟨ refl⟩∘⟨ extendʳ interchange-natural ⟩
      (𝒞.⊚ ⊗₁ 𝒟.⊚) ∘ ((p ⊗₁ f) ⊗₁ (q ⊗₁ g)) ∘ i⇒ ∘
        (λ⇐ ⊗₁ id) ∘ λ⇐
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ iλ² ⟩
      (𝒞.⊚ ⊗₁ 𝒟.⊚) ∘ ((p ⊗₁ f) ⊗₁ (q ⊗₁ g)) ∘ (λ⇐ ⊗₁ λ⇐)
        ≈⟨ refl⟩∘⟨ ⊗.homomorphism ⟨
      (𝒞.⊚ ⊗₁ 𝒟.⊚) ∘ ((p ⊗₁ f ∘ λ⇐) ⊗₁ (q ⊗₁ g ∘ λ⇐))
        ≈⟨ ⊗.homomorphism ⟨
      (𝒞.⊚ ∘ (p ⊗₁ f) ∘ λ⇐) ⊗₁ (𝒟.⊚ ∘ (q ⊗₁ g) ∘ λ⇐) ∎

    ⊚⊠ʳ : {p : P ⇒ 𝒞 [ B , C ]} {q : Q ⇒ 𝒟 [ Y , Z ]}
      {f : unit ⇒ 𝒞 [ A , B ]} {g : unit ⇒ 𝒟 [ X , Y ]} →
      𝒞⊠𝒟.⊚ ∘ ((p ⊗₁ q) ⊗₁ ((f ⊗₁ g) ∘ λ⇐)) ∘ ρ⇐
      ≈ (𝒞.⊚ ∘ (p ⊗₁ f) ∘ ρ⇐) ⊗₁ (𝒟.⊚ ∘ (q ⊗₁ g) ∘ ρ⇐)
    ⊚⊠ʳ {p = p} {q} {f} {g} = begin
      𝒞⊠𝒟.⊚ ∘ ((p ⊗₁ q) ⊗₁ ((f ⊗₁ g) ∘ λ⇐)) ∘ ρ⇐
        ≈⟨ pullʳ (refl⟩∘⟨ pushˡ split₂ʳ) ⟩
      (𝒞.⊚ ⊗₁ 𝒟.⊚) ∘ i⇒ ∘ ((p ⊗₁ q) ⊗₁ (f ⊗₁ g)) ∘
        (id ⊗₁ λ⇐) ∘ ρ⇐
        ≈⟨ refl⟩∘⟨ extendʳ interchange-natural ⟩
      (𝒞.⊚ ⊗₁ 𝒟.⊚) ∘ ((p ⊗₁ f) ⊗₁ (q ⊗₁ g)) ∘ i⇒ ∘
        (id ⊗₁ λ⇐) ∘ ρ⇐
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ iρ² ⟩
      (𝒞.⊚ ⊗₁ 𝒟.⊚) ∘ ((p ⊗₁ f) ⊗₁ (q ⊗₁ g)) ∘ (ρ⇐ ⊗₁ ρ⇐)
        ≈⟨ refl⟩∘⟨ ⊗.homomorphism ⟨
      (𝒞.⊚ ⊗₁ 𝒟.⊚) ∘ ((p ⊗₁ f ∘ ρ⇐) ⊗₁ (q ⊗₁ g ∘ ρ⇐))
        ≈⟨ ⊗.homomorphism ⟨
      (𝒞.⊚ ∘ (p ⊗₁ f) ∘ ρ⇐) ⊗₁ (𝒟.⊚ ∘ (q ⊗₁ g) ∘ ρ⇐) ∎

    ⊚⊠ : {p : unit ⇒ 𝒞 [ B , C ]} {q : unit ⇒ 𝒟 [ Y , Z ]}
      {f : unit ⇒ 𝒞 [ A , B ]} {g : unit ⇒ 𝒟 [ X , Y ]} →
      𝒞⊠𝒟.⊚ ∘ (((p ⊗₁ q) ∘ λ⇐) ⊗₁ ((f ⊗₁ g) ∘ λ⇐)) ∘ λ⇐
      ≈ ((𝒞.⊚ ∘ (p ⊗₁ f) ∘ λ⇐) ⊗₁ (𝒟.⊚ ∘ (q ⊗₁ g) ∘ λ⇐)) ∘ λ⇐
    ⊚⊠ {p = p} {q} {f} {g} = begin
      𝒞⊠𝒟.⊚ ∘ ((p ⊗₁ q) ∘ λ⇐) ⊗₁ ((f ⊗₁ g) ∘ λ⇐) ∘ λ⇐       ≈⟨ refl⟩∘⟨ pushˡ split₂ʳ ⟩
      𝒞⊠𝒟.⊚ ∘ ((p ⊗₁ q) ∘ λ⇐) ⊗₁ (f ⊗₁ g) ∘ (id ⊗₁ λ⇐) ∘ λ⇐ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ unitorˡ-commute-to ⟨
      𝒞⊠𝒟.⊚ ∘ (((p ⊗₁ q) ∘ λ⇐) ⊗₁ (f ⊗₁ g)) ∘ λ⇐ ∘ λ⇐       ≈⟨ assoc²εβ ⟩
      (𝒞⊠𝒟.⊚ ∘ (((p ⊗₁ q) ∘ λ⇐) ⊗₁ (f ⊗₁ g)) ∘ λ⇐) ∘ λ⇐     ≈⟨ ⊚⊠ˡ ⟩∘⟨refl ⟩
      ((𝒞.⊚ ∘ (p ⊗₁ f) ∘ λ⇐) ⊗₁ (𝒟.⊚ ∘ (q ⊗₁ g) ∘ λ⇐)) ∘ λ⇐ ∎

  infixr 7 _⊠NT_ _⊠NI_
  open NaturalTransformation

  private abstract
    ⊠-commute : {F G : Functor 𝒜 𝒞} {H K : Functor ℬ 𝒟}
      (α : NaturalTransformation F G) (β : NaturalTransformation H K) →
      {A₁ A₂ : 𝒜.Obj} {B₁ B₂ : ℬ.Obj} →
        𝒞⊠𝒟.⊚ ∘ (((α [ A₂ ] ⊗₁ β [ B₂ ]) ∘ λ⇐) ⊗₁ (Functor.₁ F ⊗₁ Functor.₁ H))  ∘ λ⇐
      ≈ 𝒞⊠𝒟.⊚ ∘ ((Functor.₁ G ⊗₁ Functor.₁ K)  ⊗₁ ((α [ A₁ ] ⊗₁ β [ B₁ ]) ∘ λ⇐)) ∘ ρ⇐
    ⊠-commute {F = F} {G} {H} {K} α β {A₁} {A₂} {B₁} {B₂} = begin
      𝒞⊠𝒟.⊚ ∘
        (((α [ A₂ ] ⊗₁ β [ B₂ ]) ∘ λ⇐) ⊗₁ (F.₁ ⊗₁ H.₁)) ∘ λ⇐            ≈⟨ ⊚⊠ˡ ⟩
      (𝒞.⊚ ∘ (α [ A₂ ] ⊗₁ F.₁) ∘ λ⇐) ⊗₁ (𝒟.⊚ ∘ (β [ B₂ ] ⊗₁ H.₁) ∘ λ⇐)  ≈⟨ α.commute ⟩⊗⟨ β.commute ⟩
      (𝒞.⊚ ∘ (G.₁ ⊗₁ α [ A₁ ]) ∘ ρ⇐) ⊗₁ (𝒟.⊚ ∘ (K.₁ ⊗₁ β [ B₁ ]) ∘ ρ⇐)  ≈⟨ ⊚⊠ʳ ⟨
      𝒞⊠𝒟.⊚ ∘ ((G.₁ ⊗₁ K.₁) ⊗₁ ((α [ A₁ ] ⊗₁ β [ B₁ ]) ∘ λ⇐)) ∘ ρ⇐      ∎
      where
        module F = Functor F
        module G = Functor G
        module H = Functor H
        module K = Functor K
        module α = NaturalTransformation α
        module β = NaturalTransformation β

  _⊠NT_ : {F G : Functor 𝒜 𝒞} {H K : Functor ℬ 𝒟} →
    NaturalTransformation F G → NaturalTransformation H K →
    NaturalTransformation (F ⊠F H) (G ⊠F K)
  α ⊠NT β = record
    { comp = λ (A , X) → (α [ A ] ⊗₁ β [ X ]) ∘ λ⇐
    ; commute = ⊠-commute α β
    }

  private abstract
    ⊠-isoˡ : {F G : Functor 𝒜 𝒞} {H K : Functor ℬ 𝒟}
      (α : NaturalIsomorphism F G) (β : NaturalIsomorphism H K) →
      {A₁ : 𝒜.Obj} {B₁ : ℬ.Obj} →
      𝒞⊠𝒟.⊚ ∘ (((to α [ A₁ ] ⊗₁ to β [ B₁ ]) ∘ λ⇐) ⊗₁
        ((from α [ A₁ ] ⊗₁ from β [ B₁ ]) ∘ λ⇐)) ∘ λ⇐
      ≈ (𝒞.id ⊗₁ 𝒟.id) ∘ λ⇐
    ⊠-isoˡ α β = ⊚⊠ ○ (isoˡ α ⟩⊗⟨ isoˡ β ⟩∘⟨refl)

    ⊠-isoʳ : {F G : Functor 𝒜 𝒞} {H K : Functor ℬ 𝒟}
      (α : NaturalIsomorphism F G) (β : NaturalIsomorphism H K) →
      {A₁ : 𝒜.Obj} {B₁ : ℬ.Obj} →
      𝒞⊠𝒟.⊚ ∘ (((from α [ A₁ ] ⊗₁ from β [ B₁ ]) ∘ λ⇐) ⊗₁
        ((to α [ A₁ ] ⊗₁ to β [ B₁ ]) ∘ λ⇐)) ∘ λ⇐
      ≈ (𝒞.id ⊗₁ 𝒟.id) ∘ λ⇐
    ⊠-isoʳ α β = ⊚⊠ ○ (isoʳ α ⟩⊗⟨ isoʳ β ⟩∘⟨refl)

  _⊠NI_ : {F G : Functor 𝒜 𝒞} {H K : Functor ℬ 𝒟} →
    NaturalIsomorphism F G → NaturalIsomorphism H K →
    NaturalIsomorphism (F ⊠F H) (G ⊠F K)
  α ⊠NI β = record
    { from = from α ⊠NT from β
    ; to = to α ⊠NT to β
    ; iso = record
      { isoˡ = ⊠-isoˡ α β
      ; isoʳ = ⊠-isoʳ α β
      }
    }
