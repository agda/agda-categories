{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Monoidal.Braided.Properties where

open import Categories.Functor.Monoidal.Braided using (module Lax; module Strong)
import Categories.Category.Monoidal.Utilities as ⊗-Util
import Categories.Category.Monoidal.Braided.Properties as B-Properties

open import Level
open import Data.Product using (_,_)
open import Categories.Functor.Monoidal.Properties using (idF-IsStrongMonoidal; ∘-IsMonoidal; ∘-IsStrongMonoidal)
open import Categories.Category.Monoidal.Bundle using (BraidedMonoidalCategory)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Properties using ([_]-resp-square)
import Categories.Morphism.Reasoning as MR

private
  variable
    o o′ o″ ℓ ℓ′ ℓ″ e e′ e″ : Level

private

  module WithShorthands (C : BraidedMonoidalCategory o ℓ e) where
    open BraidedMonoidalCategory C public
    open B-Properties braided using (module Shorthands)
    open Shorthands public

  module _
    {C : BraidedMonoidalCategory o ℓ e}
    {D : BraidedMonoidalCategory o′ ℓ′ e′}
    (let module C = BraidedMonoidalCategory C)
    (let module D = BraidedMonoidalCategory D)
    {F : Functor C.U D.U}
    where

    module LaxShorthands (F-IsMonoidal : Lax.IsBraidedMonoidalFunctor C D F) where
      open Functor F public
      open Lax.IsBraidedMonoidalFunctor F-IsMonoidal public
      open BraidedMonoidalCategory D
      φ : {X Y : C.Obj} → F₀ X ⊗₀ F₀ Y ⇒ F₀ (X C.⊗₀ Y)
      φ {X} {Y} = ⊗-homo.η (X , Y)

    module StrongShorthands (F-IsStrongMonoidal : Strong.IsBraidedMonoidalFunctor C D F) where
      open Functor F public
      open Strong.IsBraidedMonoidalFunctor F-IsStrongMonoidal public
      open BraidedMonoidalCategory D
      φ⇒ : {X Y : C.Obj} → F₀ X ⊗₀ F₀ Y ⇒ F₀ (X C.⊗₀ Y)
      φ⇒ {X} {Y} = ⊗-homo.⇒.η (X , Y)
      φ⇐ : {X Y : C.Obj} → F₀ (X C.⊗₀ Y) ⇒ F₀ X ⊗₀ F₀ Y
      φ⇐ {X} {Y} = ⊗-homo.⇐.η (X , Y)

-- The identity functor is braided monoidal

module _ (C : BraidedMonoidalCategory o ℓ e) where

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

-- Functor composition preserves braided monoidality

module _ {A : BraidedMonoidalCategory o ℓ e}
         {B : BraidedMonoidalCategory o′ ℓ′ e′}
         {C : BraidedMonoidalCategory o″ ℓ″ e″} where

  private
    module A = WithShorthands A
    module B = WithShorthands B
    module C = WithShorthands C

  ∘-IsBraidedMonoidal : ∀ {G : Functor B.U C.U} {F : Functor A.U B.U} →
                        Lax.IsBraidedMonoidalFunctor B C G →
                        Lax.IsBraidedMonoidalFunctor A B F →
                        Lax.IsBraidedMonoidalFunctor A C (G ∘F F)
  ∘-IsBraidedMonoidal {G} {F} GB FB = record
    { isMonoidal      = ∘-IsMonoidal _ _ _ G.isMonoidal F.isMonoidal
    ; braiding-compat = B-compat
    }
    where
      open C
      open HomReasoning
      open MR C.U
      module F = LaxShorthands FB
      module G = LaxShorthands GB
      B-compat : {X Y : A.Obj} → G.₁ (F.₁ (A.σ⇒ {X} {Y})) ∘ G.₁ F.φ ∘ G.φ ≈ (G.₁ F.φ ∘ G.φ) ∘ σ⇒
      B-compat = begin
        G.₁ (F.₁ A.σ⇒) ∘ G.₁ F.φ ∘ G.φ  ≈⟨ extendʳ ([ G ]-resp-square F.braiding-compat) ⟩
        G.₁ F.φ ∘ G.₁ B.σ⇒ ∘ G.φ        ≈⟨ pushʳ G.braiding-compat ⟩
        (G.₁ F.φ ∘ G.φ) ∘ σ⇒            ∎

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
