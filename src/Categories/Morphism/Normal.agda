{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core
open import Categories.Object.Zero

-- Normal Mono and Epimorphisms
-- https://ncatlab.org/nlab/show/normal+monomorphism
module Categories.Morphism.Normal {o ℓ e} (𝒞 : Category o ℓ e) (𝒞-Zero : Zero 𝒞) where

open import Level

open import Categories.Object.Kernel 𝒞-Zero
open import Categories.Object.Cokernel 𝒞-Zero
open import Categories.Object.Kernel.Properties 𝒞-Zero
open import Categories.Morphism 𝒞

open Category 𝒞

record IsNormalMonomorphism {A K : Obj} (k : K ⇒ A) : Set (o ⊔ ℓ ⊔ e) where
  field
    {B} : Obj
    arr : A ⇒ B
    isKernel : IsKernel k arr

  open IsKernel isKernel public

  mono : Mono k
  mono = Kernel-Mono (IsKernel⇒Kernel isKernel)

record NormalMonomorphism (K A : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    mor : K ⇒ A
    isNormalMonomorphism : IsNormalMonomorphism mor

  open IsNormalMonomorphism isNormalMonomorphism public

record IsNormalEpimorphism {B K : Obj} (k : B ⇒ K) : Set (o ⊔ ℓ ⊔ e) where
  field
    {A} : Obj
    arr : A ⇒ B
    isCokernel : IsCokernel arr k

  open IsCokernel isCokernel public

record NormalEpimorphism (B K : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    mor : B ⇒ K
    isNormalEpimorphism : IsNormalEpimorphism mor

  open IsNormalEpimorphism isNormalEpimorphism public
