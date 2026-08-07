{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Monoidal.GSMonoidal.Properties where

open import Level
open import Data.Product using (_,_)

open import Categories.Category.Monoidal.GSMonoidal.Bundle using (GSMonoidalCategory)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Properties using ([_]-resp-∘)
open import Categories.Functor.Monoidal.GSMonoidal using (module Lax; module Strong)
open import Categories.Functor.Monoidal.Braided.Properties
  using (idF-IsStrongBraidedMonoidal; ∘-IsBraidedMonoidal; ∘-IsStrongBraidedMonoidal)
import Categories.Morphism.Reasoning as MR

private
  variable
    o o′ o″ ℓ ℓ′ ℓ″ e e′ e″ : Level

private

  module _
    {C : GSMonoidalCategory o ℓ e}
    {D : GSMonoidalCategory o′ ℓ′ e′}
    (let module C = GSMonoidalCategory C)
    (let module D = GSMonoidalCategory D)
    {F : Functor C.U D.U}
    where

    module LaxShorthands (F-IsGSMonoidal : Lax.IsGSMonoidalFunctor C D F) where
      open Functor F public
      open Lax.IsGSMonoidalFunctor F-IsGSMonoidal public
      open GSMonoidalCategory D
      φ : {X Y : C.Obj} → F₀ X ⊗₀ F₀ Y ⇒ F₀ (X C.⊗₀ Y)
      φ {X} {Y} = ⊗-homo.η (X , Y)

-- The identity functor is gs-monoidal

module _ (C : GSMonoidalCategory o ℓ e) where

  idF-IsStrongGSMonoidal : Strong.IsGSMonoidalFunctor C C idF
  idF-IsStrongGSMonoidal = record
    { isBraidedMonoidal = idF-IsStrongBraidedMonoidal braidedMonoidalCategory
    ; copy              = identityˡ
    ; discard           = identityˡ
    }
    where open GSMonoidalCategory C

  idF-IsGSMonoidal : Lax.IsGSMonoidalFunctor C C idF
  idF-IsGSMonoidal =
    Strong.IsGSMonoidalFunctor.isLaxGSMonoidal idF-IsStrongGSMonoidal

  idF-StrongGSMonoidal : Strong.GSMonoidalFunctor C C
  idF-StrongGSMonoidal = record { isGSMonoidal = idF-IsStrongGSMonoidal }

  idF-GSMonoidal : Lax.GSMonoidalFunctor C C
  idF-GSMonoidal = record { isGSMonoidal = idF-IsGSMonoidal }

-- Functor composition preserves gs-monoidality

module _ {A : GSMonoidalCategory o ℓ e}
         {B : GSMonoidalCategory o′ ℓ′ e′}
         {C : GSMonoidalCategory o″ ℓ″ e″} where

  private
    module A = GSMonoidalCategory A
    module B = GSMonoidalCategory B
    module C = GSMonoidalCategory C

  ∘-IsGSMonoidal : ∀ {G : Functor B.U C.U} {F : Functor A.U B.U} →
                   Lax.IsGSMonoidalFunctor B C G →
                   Lax.IsGSMonoidalFunctor A B F →
                   Lax.IsGSMonoidalFunctor A C (G ∘F F)
  ∘-IsGSMonoidal {G} {F} GG FG = record
    { isBraidedMonoidal = ∘-IsBraidedMonoidal G.isBraidedMonoidal F.isBraidedMonoidal
    ; copy              = copy
    ; discard           = discard
    }
    where
      open C
      open HomReasoning
      open MR C.U
      module F = LaxShorthands FG
      module G = LaxShorthands GG

      copy : {X : A.Obj} → (G.₁ F.φ ∘ G.φ) ∘ Δ ≈ G.₁ (F.₁ (A.Δ {X}))
      copy = begin
        (G.₁ F.φ ∘ G.φ) ∘ Δ ≈⟨ pullʳ G.copy ⟩
        G.₁ F.φ ∘ G.₁ B.Δ   ≈⟨ [ G ]-resp-∘ F.copy ⟩
        G.₁ (F.₁ A.Δ)       ∎

      discard : {X : A.Obj} → (G.₁ F.ε ∘ G.ε) ∘ δ ≈ G.₁ (F.₁ (A.δ {X}))
      discard = begin
        (G.₁ F.ε ∘ G.ε) ∘ δ ≈⟨ pullʳ G.discard ⟩
        G.₁ F.ε ∘ G.₁ B.δ   ≈⟨ [ G ]-resp-∘ F.discard ⟩
        G.₁ (F.₁ A.δ)       ∎

  ∘-IsStrongGSMonoidal : ∀ {G : Functor B.U C.U} {F : Functor A.U B.U} →
                         Strong.IsGSMonoidalFunctor B C G →
                         Strong.IsGSMonoidalFunctor A B F →
                         Strong.IsGSMonoidalFunctor A C (G ∘F F)
  ∘-IsStrongGSMonoidal GG FG = record
    { isBraidedMonoidal =
      ∘-IsStrongBraidedMonoidal (isBraidedMonoidal GG) (isBraidedMonoidal FG)
    ; copy    = Lax.IsGSMonoidalFunctor.copy    laxComposite
    ; discard = Lax.IsGSMonoidalFunctor.discard laxComposite
    }
    where
      open Strong.IsGSMonoidalFunctor
      laxComposite =
        ∘-IsGSMonoidal (isLaxGSMonoidal GG) (isLaxGSMonoidal FG)

  ∘-GSMonoidal : Lax.GSMonoidalFunctor B C →
                 Lax.GSMonoidalFunctor A B →
                 Lax.GSMonoidalFunctor A C
  ∘-GSMonoidal G F = record
    { isGSMonoidal = ∘-IsGSMonoidal (isGSMonoidal G) (isGSMonoidal F)
    }
    where open Lax.GSMonoidalFunctor hiding (F)

  ∘-StrongGSMonoidal : Strong.GSMonoidalFunctor B C →
                       Strong.GSMonoidalFunctor A B →
                       Strong.GSMonoidalFunctor A C
  ∘-StrongGSMonoidal G F = record
    { isGSMonoidal = ∘-IsStrongGSMonoidal (isGSMonoidal G) (isGSMonoidal F)
    }
    where open Strong.GSMonoidalFunctor hiding (F)
