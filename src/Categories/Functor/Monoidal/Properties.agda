{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Monoidal.Properties where

import Categories.Category.Monoidal.Reasoning as ⊗-Reasoning
import Categories.Category.Monoidal.Utilities as ⊗-Util

open import Level
open import Data.Product using (_,_)
open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)
open import Categories.Category.Cartesian.Bundle using (CartesianCategory)
open import Categories.Category.Cartesian.Monoidal using (module CartesianMonoidal)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Category.Product using (_⁂_)
open import Categories.Functor.Properties using ([_]-resp-square; [_]-resp-∘; [_]-resp-≅; [_]-resp-Iso)
open import Categories.Functor.Cartesian using (CartesianF)
open import Categories.Functor.Monoidal
  using (IsMonoidalFunctor; IsStrongMonoidalFunctor; StrongMonoidalFunctor; MonoidalFunctor)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_; niHelper)

import Categories.Object.Terminal as ⊤
import Categories.Morphism as M
import Categories.Morphism.Reasoning as MR
import Categories.Morphism.Properties as MP

private
  variable
    o o′ o″ ℓ ℓ′ ℓ″ e e′ e″ : Level
    A B C : MonoidalCategory o ℓ e

private

  module WithShorthands (C : MonoidalCategory o ℓ e) where
    open MonoidalCategory C public
    open ⊗-Util monoidal using (module Shorthands)
    open Shorthands public

  module FunctorShorthands
    {C : MonoidalCategory o ℓ e}
    {D : MonoidalCategory o′ ℓ′ e′}
    (let module C = MonoidalCategory C)
    (let module D = MonoidalCategory D)
    {F : Functor C.U D.U}
    where

    module Lax (F-IsMonoidal : IsMonoidalFunctor C D F) where
      open Functor F public
      open IsMonoidalFunctor F-IsMonoidal public
      open MonoidalCategory D
      φ : {X Y : C.Obj} → F₀ X ⊗₀ F₀ Y ⇒ F₀ (X C.⊗₀ Y)
      φ {X} {Y} = ⊗-homo.η (X , Y)

    module Strong (F-IsStrongMonoidal : IsStrongMonoidalFunctor C D F) where
      open Functor F public
      open IsStrongMonoidalFunctor F-IsStrongMonoidal public
      open MonoidalCategory D
      ε⇒ : unit ⇒ F₀ C.unit
      ε⇒ = ε.from
      ε⇐ : F₀ C.unit ⇒ unit
      ε⇐ = ε.to
      φ⇒ : {X Y : C.Obj} → F₀ X ⊗₀ F₀ Y ⇒ F₀ (X C.⊗₀ Y)
      φ⇒ {X} {Y} = ⊗-homo.⇒.η (X , Y)
      φ⇐ : {X Y : C.Obj} → F₀ (X C.⊗₀ Y) ⇒ F₀ X ⊗₀ F₀ Y
      φ⇐ {X} {Y} = ⊗-homo.⇐.η (X , Y)

-- The identity functor is monoidal

module _ (C : MonoidalCategory o ℓ e) where

  open WithShorthands C
  open HomReasoning
  open M U
  open MR U
  open MP U

  idF-IsStrongMonoidal : IsStrongMonoidalFunctor C C idF
  idF-IsStrongMonoidal = record
    { ε             = ≅.refl
    ; ⊗-homo        = ⊗-homomorphism
    ; associativity = λ {X} {Y} {Z} → associativity X Y Z
    ; unitaryˡ      = elimʳ (elimʳ ⊗.identity)
    ; unitaryʳ      = elimʳ (elimʳ ⊗.identity)
    }
    where
      ⊗-homomorphism : ⊗ ∘F (idF ⁂ idF) ≃ idF ∘F ⊗
      ⊗-homomorphism = niHelper record
        { η   = λ _ → id
        ; η⁻¹ = λ _ → id
        ; commute = λ _ → id-comm-sym
        ; iso = λ (X , Y) → id-iso {X ⊗₀ Y}
        }
      associativity : (X Y Z : Obj) → α⇒ {X} {Y} {Z} ∘ id ∘ id ⊗₁ id ≈ id ∘ id ⊗₁ id ∘ α⇒
      associativity X Y Z = begin
        α⇒ ∘ id ∘ id ⊗₁ id  ≈⟨ refl⟩∘⟨ elimʳ ⊗.identity ⟩
        α⇒ ∘ id             ≈⟨ id-comm ⟩
        id ∘ α⇒             ≈⟨ refl⟩∘⟨ introˡ ⊗.identity ⟩
        id ∘ id ⊗₁ id ∘ α⇒  ∎

  idF-IsMonoidal : IsMonoidalFunctor C C idF
  idF-IsMonoidal = IsStrongMonoidalFunctor.isLaxMonoidal idF-IsStrongMonoidal

  idF-Monoidal : MonoidalFunctor C C
  idF-Monoidal = record { isMonoidal = idF-IsMonoidal }

  idF-StrongMonoidal : StrongMonoidalFunctor C C
  idF-StrongMonoidal = record { isStrongMonoidal = idF-IsStrongMonoidal }

-- Functor composition preserves monoidality

module _ (A : MonoidalCategory o ℓ e) (B : MonoidalCategory o′ ℓ′ e′) (C : MonoidalCategory o″ ℓ″ e″) where

  private
    module A = WithShorthands A
    module B = WithShorthands B
    module C = WithShorthands C
    open M C.U
    open MR C.U

  ∘-IsMonoidal : ∀ {F : Functor A.U B.U} {G : Functor B.U C.U} →
                    IsMonoidalFunctor B C G → IsMonoidalFunctor A B F →
                    IsMonoidalFunctor A C (G ∘F F)
  ∘-IsMonoidal {F} {G} CG CF = record
    { ε             = G.₁ F.ε ∘ G.ε
    ; ⊗-homo        = ⊗-homo
    ; associativity = associativity
    ; unitaryˡ      = unitaryˡ
    ; unitaryʳ      = unitaryʳ
    }
    where
      module F = FunctorShorthands.Lax CF
      module G = FunctorShorthands.Lax CG
      open C
      open ⊗-Reasoning C.monoidal
      commute
          : {X X′ Y Y′ : A.Obj}
            (f : X A.⇒ X′)
            (g : Y A.⇒ Y′)
          → (G.₁ F.φ ∘ G.φ) ∘ G.F₁ (F.₁ f) ⊗₁ G.₁ (F.₁ g)
            ≈ G.₁ (F.₁ (f A.⊗₁ g)) ∘ G.₁ F.φ ∘ G.φ
      commute f g = begin
        (G.₁ F.φ ∘ G.φ) ∘ G.₁ (F.₁ f) ⊗₁ G.₁ (F.₁ g)  ≈⟨ pullʳ (G.⊗-homo.commute _) ⟩
        G.₁ F.φ ∘ G.₁ (F.₁ f B.⊗₁ F.₁ g) ∘ G.φ        ≈⟨ extendʳ ([ G ]-resp-square (F.⊗-homo.commute _)) ⟩
        G.₁ (F.₁ (f A.⊗₁ g)) ∘ G.₁ F.φ ∘ G.φ          ∎
      ⊗-homo : NaturalTransformation (C.⊗ ∘F ((G ∘F F) ⁂ (G ∘F F))) ((G ∘F F) ∘F A.⊗)
      ⊗-homo = ntHelper record
        { η       = λ (X , Y) → G.₁ F.φ ∘ G.φ
        ; commute = λ (f , g) → commute f g
        }
      associativity
        : {X Y Z : A.Obj}
        → G.F₁ (F.F₁ (A.α⇒ {X} {Y} {Z})) ∘ (G.F₁ F.φ ∘ G.φ) ∘ (G.F₁ F.φ ∘ G.φ) ⊗₁ id
        ≈ (G.F₁ F.φ ∘ G.φ) ∘ id ⊗₁ (G.F₁ F.φ ∘ G.φ) ∘ α⇒
      associativity = begin
        G.₁ (F.₁ A.α⇒) ∘ (G.₁ F.φ ∘ G.φ) ∘ (G.₁ F.φ ∘ G.φ) ⊗₁ id          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ G.identity ⟨
        G.₁ (F.₁ A.α⇒) ∘ (G.₁ F.φ ∘ G.φ) ∘ (G.₁ F.φ ∘ G.φ) ⊗₁ G.₁ B.id    ≈⟨ refl⟩∘⟨ pullʳ (refl⟩∘⟨ split₁ʳ) ⟩
        G.₁ (F.₁ A.α⇒) ∘ G.₁ F.φ ∘ G.φ ∘ G.₁ F.φ ⊗₁ G.₁ B.id ∘ G.φ ⊗₁ id  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (G.⊗-homo.commute _) ⟩
        G.₁ (F.₁ A.α⇒) ∘ G.₁ F.φ ∘ G.₁ (F.φ B.⊗₁ B.id) ∘ G.φ ∘ G.φ ⊗₁ id  ≈⟨ pull-center (⟺ G.homomorphism) ⟩
        G.₁ (F.₁ A.α⇒) ∘ G.₁ (F.φ B.∘ F.φ B.⊗₁ B.id) ∘ G.φ ∘ G.φ ⊗₁ id    ≈⟨ extendʳ ([ G ]-resp-square F.associativity) ⟩
        G.₁ F.φ ∘ G.₁ (B.id B.⊗₁ F.φ B.∘ B.α⇒) ∘ G.φ ∘ G.φ ⊗₁ id          ≈⟨ push-center G.homomorphism ⟩
        G.₁ F.φ ∘ G.₁ (B.id B.⊗₁ F.φ) ∘ G.₁ B.α⇒ ∘ G.φ ∘ G.φ ⊗₁ id        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ G.associativity ⟩
        G.₁ F.φ ∘ G.₁ (B.id B.⊗₁ F.φ) ∘ G.φ ∘ id ⊗₁ G.φ ∘ α⇒              ≈⟨ pushʳ (extendʳ (G.⊗-homo.sym-commute _)) ⟩
        (G.₁ F.φ ∘ G.φ) ∘ G.₁ B.id ⊗₁ G.₁ F.φ ∘ id ⊗₁ G.φ ∘ α⇒            ≈⟨ refl⟩∘⟨ pullˡ merge₂ʳ ⟩
        (G.₁ F.φ ∘ G.φ) ∘ G.₁ B.id ⊗₁ (G.₁ F.φ ∘ G.φ) ∘ α⇒                ≈⟨ refl⟩∘⟨ G.identity ⟩⊗⟨refl ⟩∘⟨refl ⟩
        (G.₁ F.φ ∘ G.φ) ∘ id ⊗₁ (G.F₁ F.φ ∘ G.φ) ∘ α⇒                     ∎
      unitaryˡ : {X : A.Obj} → G.₁ (F.₁ (A.λ⇒ {X})) ∘ (G.₁ F.φ ∘ G.φ) ∘ (G.₁ F.ε ∘ G.ε) ⊗₁ id ≈ λ⇒
      unitaryˡ = begin
        G.₁ (F.₁ A.λ⇒) ∘ (G.₁ F.φ ∘ G.φ) ∘ (G.₁ F.ε ∘ G.ε) ⊗₁ id            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ G.identity ⟨
        G.₁ (F.₁ A.λ⇒) ∘ (G.₁ F.φ ∘ G.φ) ∘ (G.₁ F.ε ∘ G.ε) ⊗₁ G.₁ B.id      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ʳ ⟩
        G.₁ (F.₁ A.λ⇒) ∘ (G.₁ F.φ ∘ G.φ) ∘ G.₁ F.ε ⊗₁ G.₁ B.id ∘ G.ε ⊗₁ id  ≈⟨ refl⟩∘⟨ pullʳ (extendʳ (G.⊗-homo.commute _)) ⟩
        G.₁ (F.₁ A.λ⇒) ∘ G.₁ F.φ ∘ G.₁ (F.ε B.⊗₁ B.id) ∘ G.φ ∘ G.ε ⊗₁ id    ≈⟨ refl⟩∘⟨ pullˡ (⟺ G.homomorphism) ⟩
        G.₁ (F.₁ A.λ⇒) ∘ G.₁ (F.φ B.∘ F.ε B.⊗₁ B.id) ∘ G.φ ∘ G.ε ⊗₁ id      ≈⟨ pullˡ ([ G ]-resp-∘ F.unitaryˡ) ⟩
        G.₁ B.λ⇒ ∘ G.φ ∘ G.ε ⊗₁ id                                          ≈⟨ G.unitaryˡ ⟩
        λ⇒                                                                  ∎
      unitaryʳ : {X : A.Obj} → G.F₁ (F.F₁ (A.ρ⇒ {X})) ∘ (G.F₁ F.φ ∘ G.φ) ∘ id ⊗₁ (G.F₁ F.ε ∘ G.ε) ≈ ρ⇒
      unitaryʳ = begin
        G.₁ (F.₁ A.ρ⇒) ∘ (G.₁ F.φ ∘ G.φ) ∘ id ⊗₁ (G.₁ F.ε ∘ G.ε)            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ G.identity ⟩⊗⟨refl ⟨
        G.₁ (F.₁ A.ρ⇒) ∘ (G.₁ F.φ ∘ G.φ) ∘ G.₁ B.id ⊗₁ (G.₁ F.ε ∘ G.ε)      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₂ʳ ⟩
        G.₁ (F.₁ A.ρ⇒) ∘ (G.₁ F.φ ∘ G.φ) ∘ G.₁ B.id ⊗₁ G.₁ F.ε ∘ id ⊗₁ G.ε  ≈⟨ refl⟩∘⟨ pullʳ (extendʳ (G.⊗-homo.commute _)) ⟩
        G.₁ (F.₁ A.ρ⇒) ∘ G.₁ F.φ ∘ G.₁ (B.id B.⊗₁ F.ε) ∘ G.φ ∘ id ⊗₁ G.ε    ≈⟨ refl⟩∘⟨ pullˡ (⟺ G.homomorphism) ⟩
        G.₁ (F.₁ A.ρ⇒) ∘ G.F₁ (F.φ B.∘ (B.id B.⊗₁ F.ε)) ∘ G.φ ∘ id ⊗₁ G.ε   ≈⟨ pullˡ ([ G ]-resp-∘ F.unitaryʳ) ⟩
        G.F₁ B.ρ⇒ ∘ G.φ ∘ id ⊗₁ G.ε                                         ≈⟨ G.unitaryʳ ⟩
        ρ⇒                                                                  ∎

module _ (A : MonoidalCategory o ℓ e) (B : MonoidalCategory o′ ℓ′ e′) (C : MonoidalCategory o″ ℓ″ e″) where

  private
    module A = WithShorthands A
    module B = WithShorthands B
    module C = WithShorthands C
    open M C.U
    open MR C.U

  ∘-IsStrongMonoidal : ∀ {F : Functor A.U B.U} {G : Functor B.U C.U} →
                    IsStrongMonoidalFunctor B C G → IsStrongMonoidalFunctor A B F →
                    IsStrongMonoidalFunctor A C (G ∘F F)
  ∘-IsStrongMonoidal {F} {G} CG CF = record
    { ε             = ε
    ; ⊗-homo        = ⊗-homo
    ; associativity = G∘F.associativity
    ; unitaryˡ      = G∘F.unitaryˡ
    ; unitaryʳ      = G∘F.unitaryʳ
    }
    where
      module F = FunctorShorthands.Strong CF
      module G = FunctorShorthands.Strong CG
      module G∘F = FunctorShorthands.Lax (∘-IsMonoidal A B C G.isLaxMonoidal F.isLaxMonoidal)
      module G∘F-op = FunctorShorthands.Lax (∘-IsMonoidal A.op B.op C.op G.isOplaxMonoidal F.isOplaxMonoidal)
      open MP C.U
      ε : C.unit ≅ Functor.F₀ (G ∘F F) A.unit
      ε = ≅.trans G.ε ([ G ]-resp-≅ F.ε) 
      ⊗-homo : C.⊗ ∘F (G ∘F F ⁂ G ∘F F) ≃ (G ∘F F) ∘F A.⊗
      ⊗-homo = record
        { F⇒G = G∘F.⊗-homo
        ; F⇐G = G∘F-op.⊗-homo.op
        ; iso = λ (X , Y) → Iso-∘ (G.⊗-homo.iso (F.₀ X , F.₀ Y)) ([ G ]-resp-Iso (F.⊗-homo.iso (X  , Y)))
        }

module _ {A : MonoidalCategory o ℓ e} {B : MonoidalCategory o′ ℓ′ e′} {C : MonoidalCategory o″ ℓ″ e″} where

  ∘-StrongMonoidal : StrongMonoidalFunctor B C → StrongMonoidalFunctor A B → StrongMonoidalFunctor A C
  ∘-StrongMonoidal G F = record
    { isStrongMonoidal = ∘-IsStrongMonoidal A B C (isStrongMonoidal G) (isStrongMonoidal F)
    }
    where
      open StrongMonoidalFunctor using (isStrongMonoidal)

  ∘-Monoidal : MonoidalFunctor B C → MonoidalFunctor A B → MonoidalFunctor A C
  ∘-Monoidal G F = record { isMonoidal = ∘-IsMonoidal A B C (isMonoidal G) (isMonoidal F) }
    where
      open MonoidalFunctor using (isMonoidal)

private

  module WithCartesianShorthands (C : CartesianCategory o ℓ e) where
    open CartesianCategory C public
    open BinaryProducts products public renaming (_⁂_ to infixr 10 _×₁_)
    open CartesianMonoidal cartesian using (monoidal)
    open ⊗-Reasoning monoidal public
    open ⊤.Terminal terminal public

module _ (C : CartesianCategory o ℓ e) (D : CartesianCategory o′ ℓ′ e′) where

  private

    module C = WithCartesianShorthands C
    module D = WithCartesianShorthands D
    open D hiding (project₁; project₂; unique)
    open MR U

  module _ (F : StrongMonoidalFunctor C.monoidalCategory D.monoidalCategory) where

    private

      module F = StrongMonoidalFunctor F
      open FunctorShorthands.Strong F.isStrongMonoidal

      F-resp-⊤ : ⊤.IsTerminal U (F₀ C.⊤)
      F-resp-⊤ = ⊤.Terminal.⊤-is-terminal (⊤.transport-by-iso D.U D.terminal ε)
      module F-resp-⊤ = ⊤.IsTerminal F-resp-⊤

      lemma₁ : ∀ {X} → F₁ (C.! {X}) ≈ ε⇒ ∘ !
      lemma₁ = Equiv.sym (F-resp-⊤.!-unique _)

      π₁-comm : ∀ {X Y} → F₁ C.π₁ ∘ φ⇒ {X} {Y} ≈ π₁
      π₁-comm = begin
        F₁ C.π₁ ∘ φ⇒                        ≈⟨ pullˡ ([ F.F ]-resp-∘ (C.project₁ C.○ C.identityˡ)) ⟨
        F₁ C.π₁ ∘ F₁ (C.id C.×₁ C.!) ∘ φ⇒   ≈⟨ refl⟩∘⟨ ⊗-homo.⇒.sym-commute _  ⟩
        F₁ C.π₁ ∘ φ⇒ ∘ F₁ C.id ×₁ F₁ C.!    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ identity ⟩⊗⟨ lemma₁ ⟩
        F₁ C.π₁ ∘ φ⇒ ∘ id ×₁ (ε⇒ ∘ !)       ≈⟨ refl⟩∘⟨ pushʳ split₂ʳ ⟩
        F₁ C.π₁ ∘ (φ⇒ ∘ id ×₁ ε⇒) ∘ id ×₁ ! ≈⟨ pullˡ unitaryʳ ⟩
        π₁ ∘ id ×₁ !                        ≈⟨ D.project₁ ○ identityˡ ⟩
        π₁                                  ∎

      π₂-comm : ∀ {X Y} → F₁ C.π₂ ∘ φ⇒ {X} {Y} ≈ π₂
      π₂-comm {X} {Y} = begin
        F₁ C.π₂ ∘ φ⇒                        ≈⟨ pullˡ ([ F.F ]-resp-∘ (C.project₂ C.○ C.identityˡ)) ⟨
        F₁ C.π₂ ∘ F₁ (C.! C.×₁ C.id) ∘ φ⇒   ≈⟨ refl⟩∘⟨ ⊗-homo.⇒.sym-commute _ ⟩
        F₁ C.π₂ ∘ φ⇒ ∘ F₁ C.! ×₁ F₁ C.id    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ lemma₁ ⟩⊗⟨ identity ⟩
        F₁ C.π₂ ∘ φ⇒ ∘ (ε⇒ ∘ !) ×₁ id       ≈⟨ refl⟩∘⟨ pushʳ split₁ʳ ⟩
        F₁ C.π₂ ∘ (φ⇒ ∘ ε⇒ ×₁ id) ∘ ! ×₁ id ≈⟨ pullˡ unitaryˡ ⟩
        π₂ ∘ ! ×₁ id                        ≈⟨ D.project₂ ○ identityˡ ⟩
        π₂                                  ∎

      unique : ∀ {X A B} {h : X ⇒ F₀ (A C.× B)} {i : X ⇒ F₀ A} {j : X ⇒ F₀ B} →
                 F₁ C.π₁ ∘ h ≈ i →
                 F₁ C.π₂ ∘ h ≈ j →
                 φ⇒ ∘ ⟨ i , j ⟩ ≈ h
      unique {h = h} {i} {j} eq₁ eq₂ = ⟺ (switch-tofromˡ ⊗-homo.FX≅GX (⟺ (D.unique eq₁′ eq₂′)))
        where
          eq₁′ : π₁ ∘ φ⇐ ∘ h ≈ i
          eq₁′ = pullˡ (⟺ (switch-fromtoʳ ⊗-homo.FX≅GX π₁-comm)) ○ eq₁
          eq₂′ : π₂ ∘ φ⇐ ∘ h ≈ j
          eq₂′ = pullˡ (⟺ (switch-fromtoʳ ⊗-homo.FX≅GX π₂-comm)) ○ eq₂

      project₁ : {A B : C.Obj} {iA : D.Obj} {h : iA D.⇒ F₀ A} {i : iA ⇒ F₀ B} →
                 F₁ C.π₁ ∘ φ⇒ ∘ ⟨ h , i ⟩ ≈ h
      project₁ {h = h} {i} = begin
        F.₁ C.π₁ ∘ φ⇒ ∘ ⟨ h , i ⟩ ≈⟨ pullˡ π₁-comm ⟩
        π₁ ∘ ⟨ h , i ⟩            ≈⟨ D.project₁ ⟩
        h                         ∎
      project₂ : {A B : C.Obj} {iA : Obj} {h : iA ⇒ F₀ A} {i : iA ⇒ F₀ B} →
                 F₁ C.π₂ ∘ φ⇒ ∘ ⟨  h , i ⟩ ≈ i
      project₂ {h = h} {i} = begin
        F₁ C.π₂ ∘ φ⇒ ∘ ⟨ h , i ⟩  ≈⟨ pullˡ π₂-comm ⟩
        π₂ ∘ ⟨ h , i ⟩            ≈⟨ D.project₂ ⟩
        i                         ∎

    StrongMonoidal⇒Cartesian : CartesianF C D
    StrongMonoidal⇒Cartesian = record
      { F           = F.F
      ; isCartesian = record
        { F-resp-⊤ = F-resp-⊤
        ; F-resp-× = λ {A B} → record
          { ⟨_,_⟩    = λ f g → φ⇒ ∘ ⟨ f , g ⟩
          ; project₁ = project₁ {A} {B}
          ; project₂ = project₂ {A} {B}
          ; unique   = unique
          }
        }
      }
