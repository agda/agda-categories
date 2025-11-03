{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Monoidal.Properties where

open import Level
open import Data.Product using (_,_)

open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Bundle
  using (MonoidalCategory; BraidedMonoidalCategory; SymmetricMonoidalCategory)
open import Categories.Category.Cartesian.Bundle using (CartesianCategory)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Category.Product using (_⁂_)
open import Categories.Functor.Properties using ([_]-resp-square; [_]-resp-∘; [_]-resp-≅; [_]-resp-Iso)
open import Categories.Functor.Cartesian using (CartesianF)
open import Categories.Functor.Monoidal
  using (IsMonoidalFunctor; IsStrongMonoidalFunctor; StrongMonoidalFunctor;
    MonoidalFunctor)
import Categories.Functor.Monoidal.Braided as Braided
import Categories.Functor.Monoidal.Symmetric as Symmetric
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_; niHelper; Functor-NI-setoid; _ⓘˡ_; sym-associator; associator; _ⓘʳ_)

import Categories.Object.Terminal as ⊤
import Categories.Object.Product as P
import Categories.Morphism as M
import Categories.Morphism.Reasoning as MR
import Categories.Morphism.Properties as MP

private
  variable
    o o′ o″ ℓ ℓ′ ℓ″ e e′ e″ : Level

-- The identity functor is monoidal

private

  module WithShorthands (C : MonoidalCategory o ℓ e) where
    import Categories.Category.Monoidal.Utilities as ⊗-Util
    open MonoidalCategory C public
    open ⊗-Util monoidal using (module Shorthands) public
    open Shorthands public

  module FunctorShorthands {C : MonoidalCategory o ℓ e} {D : MonoidalCategory o′ ℓ′ e′} where
   
    module C = MonoidalCategory C
    module D = MonoidalCategory D

    module _ {F : Functor C.U D.U} where

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
        φ⇒ : {X Y : C.Obj} → F₀ X ⊗₀ F₀ Y ⇒ F₀ (X C.⊗₀ Y)
        φ⇒ {X} {Y} = ⊗-homo.⇒.η (X , Y)
        φ⇐ : {X Y : C.Obj} → F₀ (X C.⊗₀ Y) ⇒ F₀ X ⊗₀ F₀ Y
        φ⇐ {X} {Y} = ⊗-homo.⇐.η (X , Y)

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

  idF-StrongMonoidal : StrongMonoidalFunctor C C
  idF-StrongMonoidal = record { isStrongMonoidal = idF-IsStrongMonoidal }

  idF-Monoidal : MonoidalFunctor C C
  idF-Monoidal = record { isMonoidal = idF-IsMonoidal }

-- The identity functor is braided monoidal

module _ (C : BraidedMonoidalCategory o ℓ e) where
  open Braided

  idF-IsStrongBraidedMonoidal : Strong.IsBraidedMonoidalFunctor C C idF
  idF-IsStrongBraidedMonoidal = record
    { isStrongMonoidal = idF-IsStrongMonoidal monoidalCategory
    ; braiding-compat  = MR.id-comm U
    }
    where open BraidedMonoidalCategory C

  idF-IsBraidedMonoidal : Lax.IsBraidedMonoidalFunctor C C idF
  idF-IsBraidedMonoidal =
    Strong.IsBraidedMonoidalFunctor.isLaxBraidedMonoidal idF-IsStrongBraidedMonoidal

  idF-StrongBraidedMonoidal : Strong.BraidedMonoidalFunctor C C
  idF-StrongBraidedMonoidal = record { isBraidedMonoidal = idF-IsStrongBraidedMonoidal }

  idF-BraidedMonoidal : Lax.BraidedMonoidalFunctor C C
  idF-BraidedMonoidal = record { isBraidedMonoidal = idF-IsBraidedMonoidal }

-- The identity functor is symmetric monoidal

module _ (C : SymmetricMonoidalCategory o ℓ e) where
  open Symmetric
  open SymmetricMonoidalCategory C using (braidedMonoidalCategory)

  idF-StrongSymmetricMonoidal : Strong.SymmetricMonoidalFunctor C C
  idF-StrongSymmetricMonoidal = record
    { isBraidedMonoidal = idF-IsStrongBraidedMonoidal braidedMonoidalCategory }

  idF-SymmetricMonoidal : Lax.SymmetricMonoidalFunctor C C
  idF-SymmetricMonoidal = record
    { isBraidedMonoidal = idF-IsBraidedMonoidal braidedMonoidalCategory }

-- Functor composition preserves monoidality

module _ (A : MonoidalCategory o ℓ e) (B : MonoidalCategory o′ ℓ′ e′) (C : MonoidalCategory o″ ℓ″ e″) where
  private
    module A = WithShorthands A
    module B = WithShorthands B
    module C = WithShorthands C
    open P C.U
    open M C.U
    import Categories.Category.Monoidal.Reasoning as ⊗-Reasoning
    open MR C.U

  ∘-IsMonoidal : ∀ {F : Functor A.U B.U} {G : Functor B.U C.U} →
                    IsMonoidalFunctor B C G → IsMonoidalFunctor A B F →
                    IsMonoidalFunctor A C (G ∘F F)
  ∘-IsMonoidal {F} {G} CG CF = record
    { ε             = G.₁ F.ε C.∘ G.ε
    ; ⊗-homo        = ⊗-homo
    ; associativity = associativity
    ; unitaryˡ      = unitaryˡ
    ; unitaryʳ      = unitaryʳ
    }
    where

      module F  = FunctorShorthands.Lax CF
      module G  = FunctorShorthands.Lax CG

      open C
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
        where
          open ⊗-Reasoning C.monoidal

      η : (X  Y : A.Obj) → G.F₀ (F.F₀ X) C.⊗₀ G.F₀ (F.F₀ Y) C.⇒ G.F₀ (F.F₀ (A.⊗.F₀ (X , Y)))
      η X Y = G.₁ F.φ ∘ G.φ

      ⊗-homo : NaturalTransformation (C.⊗ ∘F ((G ∘F F) ⁂ (G ∘F F))) ((G ∘F F) ∘F A.⊗)
      ⊗-homo = ntHelper record
        { η       = λ (X , Y) → η X Y
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
        where
          open ⊗-Reasoning C.monoidal

      unitaryˡ : {X : A.Obj} → G.₁ (F.₁ (A.λ⇒ {X})) ∘ (G.₁ F.φ ∘ G.φ) ∘ (G.₁ F.ε ∘ G.ε) ⊗₁ id ≈ λ⇒
      unitaryˡ = begin
        G.₁ (F.₁ A.λ⇒) ∘ (G.₁ F.φ ∘ G.φ) ∘ (G.₁ F.ε ∘ G.ε) ⊗₁ id            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ G.identity ⟨
        G.₁ (F.₁ A.λ⇒) ∘ (G.₁ F.φ ∘ G.φ) ∘ (G.₁ F.ε ∘ G.ε) ⊗₁ G.₁ B.id      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ʳ ⟩
        G.₁ (F.₁ A.λ⇒) ∘ (G.₁ F.φ ∘ G.φ) ∘ G.₁ F.ε ⊗₁ G.₁ B.id ∘ G.ε ⊗₁ id  ≈⟨ refl⟩∘⟨ pullʳ (extendʳ (G.⊗-homo.commute _)) ⟩
        G.₁ (F.₁ A.λ⇒) ∘ G.₁ F.φ ∘ G.₁ (F.ε B.⊗₁ B.id) ∘ G.φ ∘ G.ε ⊗₁ id    ≈⟨ refl⟩∘⟨ pullˡ (⟺ G.homomorphism) ⟩
        G.₁ (F.₁ A.λ⇒) ∘ G.₁ (F.φ B.∘ F.ε B.⊗₁ B.id) ∘ G.φ ∘ G.ε ⊗₁ id      ≈⟨ pullˡ ([ G ]-resp-∘ F.unitaryˡ) ⟩
        G.₁ B.λ⇒ ∘ G.φ ∘ G.ε ⊗₁ id                                          ≈⟨ G.unitaryˡ ⟩
        λ⇒                                                                  ∎
        where
          open ⊗-Reasoning C.monoidal

      unitaryʳ : {X : A.Obj} → G.F₁ (F.F₁ (A.ρ⇒ {X})) ∘ (G.F₁ F.φ ∘ G.φ) ∘ id ⊗₁ (G.F₁ F.ε ∘ G.ε) ≈ ρ⇒
      unitaryʳ = begin
        G.₁ (F.₁ A.ρ⇒) ∘ (G.₁ F.φ ∘ G.φ) ∘ id ⊗₁ (G.₁ F.ε ∘ G.ε)            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ G.identity ⟩⊗⟨refl ⟨
        G.₁ (F.₁ A.ρ⇒) ∘ (G.₁ F.φ ∘ G.φ) ∘ G.₁ B.id ⊗₁ (G.₁ F.ε ∘ G.ε)      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₂ʳ ⟩
        G.₁ (F.₁ A.ρ⇒) ∘ (G.₁ F.φ ∘ G.φ) ∘ G.₁ B.id ⊗₁ G.₁ F.ε ∘ id ⊗₁ G.ε  ≈⟨ refl⟩∘⟨ pullʳ (extendʳ (G.⊗-homo.commute _)) ⟩
        G.₁ (F.₁ A.ρ⇒) ∘ G.₁ F.φ ∘ G.₁ (B.id B.⊗₁ F.ε) ∘ G.φ ∘ id ⊗₁ G.ε    ≈⟨ refl⟩∘⟨ pullˡ (⟺ G.homomorphism) ⟩
        G.₁ (F.₁ A.ρ⇒) ∘ G.F₁ (F.φ B.∘ (B.id B.⊗₁ F.ε)) ∘ G.φ ∘ id ⊗₁ G.ε   ≈⟨ pullˡ ([ G ]-resp-∘ F.unitaryʳ) ⟩
        G.F₁ B.ρ⇒ ∘ G.φ ∘ id ⊗₁ G.ε                                         ≈⟨ G.unitaryʳ ⟩
        ρ⇒                                                                  ∎
        where
          open ⊗-Reasoning C.monoidal

module _ (A : MonoidalCategory o ℓ e) (B : MonoidalCategory o′ ℓ′ e′) (C : MonoidalCategory o″ ℓ″ e″) where
  private
    module A = WithShorthands A
    module B = WithShorthands B
    module C = WithShorthands C
    open P C.U
    open M C.U
    import Categories.Category.Monoidal.Reasoning as ⊗-Reasoning
    open MR C.U

  ∘-IsStrongMonoidal : ∀ {F : Functor A.U B.U} {G : Functor B.U C.U} →
                    IsStrongMonoidalFunctor B C G → IsStrongMonoidalFunctor A B F →
                    IsStrongMonoidalFunctor A C (G ∘F F)
  ∘-IsStrongMonoidal {F} {G} CG CF = record
    { ε             = ≅.trans G.ε ([ G ]-resp-≅ F.ε)
    ; ⊗-homo        = ⊗-homo
    ; associativity = G∘F.associativity
    ; unitaryˡ      = G∘F.unitaryˡ
    ; unitaryʳ      = G∘F.unitaryʳ
    }
    where
      module F = FunctorShorthands.Strong CF
      module G = FunctorShorthands.Strong CG
      module G∘F = FunctorShorthands.Lax (∘-IsMonoidal A B C G.isLaxMonoidal F.isLaxMonoidal)
      module G∘F′ = FunctorShorthands.Lax (∘-IsMonoidal A.op B.op C.op G.isOplaxMonoidal F.isOplaxMonoidal)
      open MP C.U
      ⊗-homo : C.⊗ ∘F (G ∘F F ⁂ G ∘F F) ≃ (G ∘F F) ∘F A.⊗
      ⊗-homo = record
        { F⇒G = G∘F.⊗-homo
        ; F⇐G = G∘F′.⊗-homo.op
        ; iso = λ { (X , Y) → Iso-∘ (G.⊗-homo.iso (F.₀ X , F.₀ Y)) ([ G ]-resp-Iso (F.⊗-homo.iso (X  , Y))) }
        }

module _ {A : MonoidalCategory o ℓ e} {B : MonoidalCategory o′ ℓ′ e′} {C : MonoidalCategory o″ ℓ″ e″} where

    ∘-StrongMonoidal : StrongMonoidalFunctor B C → StrongMonoidalFunctor A B → StrongMonoidalFunctor A C
    ∘-StrongMonoidal G F = record { isStrongMonoidal = ∘-IsStrongMonoidal _ _ _ (StrongMonoidalFunctor.isStrongMonoidal G) (StrongMonoidalFunctor.isStrongMonoidal F) }

    ∘-Monoidal : MonoidalFunctor B C → MonoidalFunctor A B → MonoidalFunctor A C
    ∘-Monoidal G F = record { isMonoidal = ∘-IsMonoidal _ _ _ (MonoidalFunctor.isMonoidal G) (MonoidalFunctor.isMonoidal F) }

-- Functor composition preserves braided monoidality

module _ {A : BraidedMonoidalCategory o ℓ e}
         {B : BraidedMonoidalCategory o′ ℓ′ e′}
         {C : BraidedMonoidalCategory o″ ℓ″ e″} where

  private
    module A = BraidedMonoidalCategory A
    module B = BraidedMonoidalCategory B
    module C = BraidedMonoidalCategory C
  open Braided

  ∘-IsBraidedMonoidal : ∀ {G : Functor B.U C.U} {F : Functor A.U B.U} →
                        Lax.IsBraidedMonoidalFunctor B C G →
                        Lax.IsBraidedMonoidalFunctor A B F →
                        Lax.IsBraidedMonoidalFunctor A C (G ∘F F)
  ∘-IsBraidedMonoidal {G} {F} GB FB = record
    { isMonoidal      = ∘-IsMonoidal _ _ _ (isMonoidal GB) (isMonoidal FB)
    ; braiding-compat = σ-compat
    }
    where
      open C
      open HomReasoning
      open MR C.U
      open Functor hiding (F₁)
      open Functor F using (F₁)
      open Functor G using () renaming (F₁ to G₁)
      open Lax.IsBraidedMonoidalFunctor

      FH  = λ {X Y} → ⊗-homo.η FB (X , Y)
      GH  = λ {X Y} → ⊗-homo.η GB (X , Y)
      AB = λ {X Y} → A.braiding.⇒.η (X , Y)
      BB = λ {X Y} → B.braiding.⇒.η (X , Y)
      CB = λ {X Y} → C.braiding.⇒.η (X , Y)

      σ-compat : {X Y : A.Obj} → G₁ (F₁ (AB {X} {Y})) ∘ G₁ FH ∘ GH ≈ (G₁ FH ∘ GH) ∘ CB
      σ-compat = begin
            G₁ (F₁ AB) ∘ G₁ FH ∘ GH   ≈˘⟨ pushˡ (homomorphism G) ⟩
            G₁ (F₁ AB B.∘ FH) ∘ GH    ≈⟨ F-resp-≈ G (braiding-compat FB) ⟩∘⟨refl ⟩
            G₁ (FH B.∘ BB) ∘ GH       ≈⟨ pushˡ (homomorphism G) ⟩
            G₁ FH ∘ G₁ BB ∘ GH        ≈⟨ pushʳ (braiding-compat GB) ⟩
            (G₁ FH ∘ GH) ∘ CB         ∎

  ∘-IsStrongBraidedMonoidal : ∀ {G : Functor B.U C.U} {F : Functor A.U B.U} →
                              Strong.IsBraidedMonoidalFunctor B C G →
                              Strong.IsBraidedMonoidalFunctor A B F →
                              Strong.IsBraidedMonoidalFunctor A C (G ∘F F)
  ∘-IsStrongBraidedMonoidal {G} {F} GB FB = record
    { isStrongMonoidal =
      ∘-IsStrongMonoidal _ _ _ (isStrongMonoidal GB) (isStrongMonoidal FB)
    ; braiding-compat =
      Lax.IsBraidedMonoidalFunctor.braiding-compat
        (∘-IsBraidedMonoidal (isLaxBraidedMonoidal GB) (isLaxBraidedMonoidal FB))
    }
    where open Strong.IsBraidedMonoidalFunctor

  ∘-BraidedMonoidal : Lax.BraidedMonoidalFunctor B C →
                      Lax.BraidedMonoidalFunctor A B →
                      Lax.BraidedMonoidalFunctor A C
  ∘-BraidedMonoidal G F = record
    { isBraidedMonoidal =
      ∘-IsBraidedMonoidal (isBraidedMonoidal G) (isBraidedMonoidal F)
    }
    where open Lax.BraidedMonoidalFunctor hiding (F)

  ∘-StrongBraidedMonoidal : Strong.BraidedMonoidalFunctor B C →
                            Strong.BraidedMonoidalFunctor A B →
                            Strong.BraidedMonoidalFunctor A C
  ∘-StrongBraidedMonoidal G F = record
    { isBraidedMonoidal =
      ∘-IsStrongBraidedMonoidal (isBraidedMonoidal G) (isBraidedMonoidal F)
    }
    where open Strong.BraidedMonoidalFunctor hiding (F)

-- Functor composition preserves symmetric monoidality

module _ {A : SymmetricMonoidalCategory o ℓ e}
         {B : SymmetricMonoidalCategory o′ ℓ′ e′}
         {C : SymmetricMonoidalCategory o″ ℓ″ e″} where
  open Symmetric

  ∘-SymmetricMonoidal : Lax.SymmetricMonoidalFunctor B C →
                        Lax.SymmetricMonoidalFunctor A B →
                        Lax.SymmetricMonoidalFunctor A C
  ∘-SymmetricMonoidal G F = record
    { isBraidedMonoidal =
      ∘-IsBraidedMonoidal (isBraidedMonoidal G) (isBraidedMonoidal F)
    }
    where open Lax.SymmetricMonoidalFunctor hiding (F)

  ∘-StrongSymmetricMonoidal : Strong.SymmetricMonoidalFunctor B C →
                              Strong.SymmetricMonoidalFunctor A B →
                              Strong.SymmetricMonoidalFunctor A C
  ∘-StrongSymmetricMonoidal G F = record
    { isBraidedMonoidal =
      ∘-IsStrongBraidedMonoidal (isBraidedMonoidal G) (isBraidedMonoidal F)
    }
    where open Strong.SymmetricMonoidalFunctor hiding (F)

module _ (C : CartesianCategory o ℓ e) (D : CartesianCategory o′ ℓ′ e′) where
  private
    module C = CartesianCategory C
    module D = CartesianCategory D
    module PC = BinaryProducts C.products
    module PD = BinaryProducts D.products
    module TC = ⊤.Terminal C.terminal
    module TD = ⊤.Terminal D.terminal
    open D.HomReasoning
    open MR D.U

  module _ (F : StrongMonoidalFunctor C.monoidalCategory D.monoidalCategory) where
    private
      module F = StrongMonoidalFunctor F

      F-resp-⊤ : ⊤.IsTerminal D.U (F.F₀ TC.⊤)
      F-resp-⊤ = ⊤.Terminal.⊤-is-terminal (⊤.transport-by-iso D.U D.terminal F.ε)
      module F-resp-⊤ = ⊤.IsTerminal F-resp-⊤

      lemma₁ : ∀ {X} → F.ε.from D.∘ TD.! {F.₀ X} D.≈ F.₁ (TC.! {X})
      lemma₁ = F-resp-⊤.!-unique _

      π₁-comm : ∀ {X Y} → F.F₁ PC.π₁ D.∘ F.⊗-homo.⇒.η (X , Y) D.≈ PD.π₁
      π₁-comm {X} {Y} = begin
        F.F₁ PC.π₁ D.∘ F.⊗-homo.⇒.η (X , Y)                                                    ≈˘⟨ [ F.F ]-resp-∘ (C.Equiv.trans PC.project₁ C.identityˡ) ⟩∘⟨refl ⟩
        (F.F₁ PC.π₁ D.∘ F.F₁ (C.id PC.⁂ TC.!)) D.∘ F.⊗-homo.⇒.η (X , Y)                        ≈⟨ pullʳ (F.⊗-homo.⇒.sym-commute _) ⟩
        F.F₁ PC.π₁ D.∘ F.⊗-homo.⇒.η (X , TC.⊤) D.∘ (F.F₁ C.id PD.⁂ F.F₁ TC.!)                  ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ ([ F.₀ X PD.×- ]-resp-∘ lemma₁ ○ Functor.F-resp-≈ PD.-×- (⟺ F.identity , D.Equiv.refl)) ⟩
        F.F₁ PC.π₁ D.∘ F.⊗-homo.⇒.η (X , TC.⊤) D.∘ (D.id PD.⁂ F.ε.from) D.∘ (D.id PD.⁂ TD.!)   ≈⟨ D.∘-resp-≈ʳ D.sym-assoc ○ D.sym-assoc ⟩
        (F.F₁ PC.π₁ D.∘ F.⊗-homo.⇒.η (X , TC.⊤) D.∘ (D.id PD.⁂ F.ε.from)) D.∘ (D.id PD.⁂ TD.!) ≈⟨ F.unitaryʳ ⟩∘⟨refl ⟩
        PD.π₁ D.∘ (D.id PD.⁂ TD.!)                                                              ≈⟨ PD.project₁ ○ D.identityˡ ⟩
        PD.π₁                                                                                   ∎

      π₂-comm : ∀ {X Y} → F.F₁ PC.π₂ D.∘ F.⊗-homo.⇒.η (X , Y) D.≈ PD.π₂
      π₂-comm {X} {Y} = begin
        F.F₁ PC.π₂ D.∘ F.⊗-homo.⇒.η (X , Y)                                                ≈˘⟨ [ F.F ]-resp-∘ (C.Equiv.trans PC.project₂ C.identityˡ) ⟩∘⟨refl ⟩
        (F.F₁ PC.π₂ D.∘ F.F₁ (TC.! PC.⁂ C.id)) D.∘ F.⊗-homo.⇒.η (X , Y)                      ≈⟨ pullʳ (F.⊗-homo.⇒.sym-commute _) ⟩
        F.F₁ PC.π₂ D.∘ F.⊗-homo.⇒.η (TC.⊤ , Y) D.∘ (F.F₁ TC.! PD.⁂ F.F₁ C.id)                 ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ ([ PD.-× F.₀ Y ]-resp-∘ lemma₁ ○ Functor.F-resp-≈ PD.-×- (D.Equiv.refl , ⟺ F.identity)) ⟩
        F.F₁ PC.π₂ D.∘ F.⊗-homo.⇒.η (TC.⊤ , Y) D.∘ (F.ε.from PD.⁂ D.id) D.∘ (TD.! PD.⁂ D.id)   ≈⟨ D.∘-resp-≈ʳ D.sym-assoc ○ D.sym-assoc ⟩
        (F.F₁ PC.π₂ D.∘ F.⊗-homo.⇒.η (TC.⊤ , Y) D.∘ (F.ε.from PD.⁂ D.id)) D.∘ (TD.! PD.⁂ D.id) ≈⟨ F.unitaryˡ ⟩∘⟨refl ⟩
        PD.π₂ D.∘ (TD.! PD.⁂ D.id)                                                           ≈⟨ PD.project₂ ○ D.identityˡ ⟩
        PD.π₂                                                                              ∎

      unique : ∀ {X A B} {h : X D.⇒ F.₀ (A PC.× B)} {i : X D.⇒ F.₀ A} {j : X D.⇒ F.₀ B} →
                 F.₁ PC.π₁ D.∘ h D.≈ i →
                 F.₁ PC.π₂ D.∘ h D.≈ j →
                 F.⊗-homo.⇒.η (A , B) D.∘ PD.⟨ i , j ⟩ D.≈ h
      unique  eq₁ eq₂ = ⟺ (switch-tofromˡ F.⊗-homo.FX≅GX (⟺ (PD.unique (pullˡ (⟺ (switch-fromtoʳ F.⊗-homo.FX≅GX π₁-comm)) ○ eq₁)
                                                                      (pullˡ (⟺ (switch-fromtoʳ F.⊗-homo.FX≅GX π₂-comm)) ○ eq₂))))

    StrongMonoidal⇒Cartesian : CartesianF C D
    StrongMonoidal⇒Cartesian = record
      { F           = F.F
      ; isCartesian = record
        { F-resp-⊤ = F-resp-⊤
        ; F-resp-× = λ {A B} → record
          { ⟨_,_⟩    = λ f g → F.⊗-homo.⇒.η _ D.∘ PD.⟨ f , g ⟩
          ; project₁ = project₁ {A} {B}
          ; project₂ = project₂ {A} {B}
          ; unique   = unique
          }
        }
      }
      where
        import Categories.Object.Product.Core
        project₁ : {A B : C.Obj} {iA : D.Obj} {h : iA D.⇒ F.F₀ A} {i : iA D.⇒ F.F₀ B} →
                    F.F₁ PC.π₁ D.∘
                    F.⊗-homo.⇒.η (A , B) D.∘
                    Categories.Object.Product.Core.Product.⟨ PD.product , h ⟩ i
                    D.≈ h
        project₁ {A} {B} {_} {h} {i} = begin
            F.₁ PC.π₁ D.∘ F.⊗-homo.⇒.η _ D.∘ PD.⟨ h , i ⟩ ≈⟨ pullˡ π₁-comm ⟩
            PD.π₁ D.∘ PD.⟨ h , i ⟩                         ≈⟨ PD.project₁ ⟩
            h                                            ∎
        project₂ : {A B : C.Obj} {iA : D.Obj} {h : iA D.⇒ F.F₀ A} {i : iA D.⇒ F.F₀ B} →
            F.F₁ PC.π₂ D.∘
            F.⊗-homo.⇒.η (A , B) D.∘
            Categories.Object.Product.Core.Product.⟨ PD.product , h ⟩ i
            D.≈ i
        project₂ {_} {_} {_} {h} {i} = begin
            F.₁ PC.π₂ D.∘ F.⊗-homo.⇒.η _ D.∘ PD.⟨ h , i ⟩ ≈⟨ pullˡ π₂-comm ⟩
            PD.π₂ D.∘ PD.⟨ h , i ⟩                        ≈⟨ PD.project₂ ⟩
            i                                           ∎
