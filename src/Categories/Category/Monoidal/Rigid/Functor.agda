{-# OPTIONS --without-K --safe --lossy-unification #-}
-- --lossy-unification makes this typecheck in ~3s instead of ~25s

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Rigid using (LeftRigid)

module Categories.Category.Monoidal.Rigid.Functor
    {o ℓ e} {C : Category o ℓ e} (M : Monoidal C) (L : LeftRigid M) where

open import Data.Product using (_,_)

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)
open import Categories.Category.Monoidal.Construction.Reverse
  using (Reverse-MonoidalCategory)
open import Categories.Category.Product using (_⁂_)
open import Categories.Functor using (_∘F_)
open import Categories.Functor.Monoidal
  using (IsStrongMonoidalFunctor; StrongMonoidalFunctor)
open import Categories.Morphism C using (_≅_)
open import Categories.Morphism.Duality C using (Iso⇒op-Iso; ≅⇒op-≅)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (_≃_; niHelper)

open Category C
open HomReasoning
open Monoidal M
open LeftRigid L using (_⁻¹; dual₁)
open import Categories.Category.Monoidal.Rigid.Dual M L
  using (dualFunctor)
open import Categories.Category.Monoidal.Rigid.Properties M
open Left L
  using ( ⁻¹-unit-iso; ⁻¹-flip-⊗; ⁻¹-flip-⊗⁻¹; ⁻¹-flip-⊗⁻¹-assoc
        ; ⁻¹-flip-⊗⁻¹-natural; ⁻¹-flip-⊗⁻¹-unitaryˡ; ⁻¹-flip-⊗⁻¹-unitaryʳ
        ; ⁻¹-flip-⊗-iso )

private
  C-monoidal : MonoidalCategory o ℓ e
  C-monoidal = record { monoidal = M }

  C-op-reverse : MonoidalCategory o ℓ e
  C-op-reverse = Reverse-MonoidalCategory (MonoidalCategory.op C-monoidal)

  variable
    X Y : Obj

  ⊗-homo :
    MonoidalCategory.⊗ C-op-reverse ∘F (dualFunctor ⁂ dualFunctor)
    ≃ dualFunctor ∘F MonoidalCategory.⊗ C-monoidal
  ⊗-homo = niHelper record
    { η       = λ (X , Y) → ⁻¹-flip-⊗⁻¹ {X} {Y}
    ; η⁻¹     = λ (X , Y) → ⁻¹-flip-⊗ {X} {Y}
    ; commute = λ _ → ⁻¹-flip-⊗⁻¹-natural
    ; iso     = λ _ → Iso⇒op-Iso (_≅_.iso ⁻¹-flip-⊗-iso)
    }

dual-IsStrongMonoidalFunctor :
  IsStrongMonoidalFunctor C-monoidal C-op-reverse dualFunctor
dual-IsStrongMonoidalFunctor = record
  { ε             = ≅⇒op-≅ ⁻¹-unit-iso
  ; ⊗-homo        = ⊗-homo
  ; associativity = assoc ○ ⁻¹-flip-⊗⁻¹-assoc ○ sym-assoc
  ; unitaryˡ      = assoc ○ ⁻¹-flip-⊗⁻¹-unitaryˡ
  ; unitaryʳ      = assoc ○ ⁻¹-flip-⊗⁻¹-unitaryʳ
  }

dual-StrongMonoidalFunctor : StrongMonoidalFunctor C-monoidal C-op-reverse
dual-StrongMonoidalFunctor = record
  { F = dualFunctor
  ; isStrongMonoidal = dual-IsStrongMonoidalFunctor
  }
