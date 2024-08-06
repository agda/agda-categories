{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Object.Zero

-- Kernels of morphisms.
-- https://ncatlab.org/nlab/show/kernel
module Categories.Object.Kernel {o ℓ e} {𝒞 : Category o ℓ e} (zero : Zero 𝒞) where

open import Level using (_⊔_)

open import Categories.Morphism 𝒞
open import Categories.Morphism.Reasoning 𝒞
  hiding (glue)

open Category 𝒞
open Zero zero

open HomReasoning

private
  variable
    A B X : Obj
    f h i j k : A ⇒ B

-- Note: We could define Kernels directly as equalizers or as pullbacks, but it seems somewhat
-- cleaner to just define them "as is" to avoid mucking about with extra morphisms that can
-- get in the way. For example, if we defined them as 'Pullback f !' then our 'p₂' projection
-- would _always_ be trivially equal to '¡ : K ⇒ zero'.

record IsKernel {A B K} (k : K ⇒ A) (f : A ⇒ B) : Set (o ⊔ ℓ ⊔ e) where
  field
    commute : f ∘ k ≈ zero⇒
    universal : ∀ {X} {h : X ⇒ A} → f ∘ h ≈ zero⇒ → X ⇒ K 
    factors : ∀ {eq : f ∘ h ≈ zero⇒} → h ≈ k ∘ universal eq
    unique : ∀ {eq : f ∘ h ≈ zero⇒} → h ≈ k ∘ i → i ≈ universal eq

  unique-diagram : k ∘ h ≈ k ∘ i → h ≈ i
  unique-diagram {_} {h} {i} k∘h≈k∘i = begin
    h            ≈⟨ unique Equiv.refl ⟩
    universal eq ≈⟨ unique k∘h≈k∘i ⟨
    i            ∎
    where
      eq : f ∘ k ∘ h ≈ zero⇒
      eq = begin
        f ∘ k ∘ h ≈⟨ glue′ commute Equiv.refl ⟩
        zero⇒ ∘ h ≈⟨ zero-∘ʳ h ⟩
        zero⇒ ∎

  universal-resp-≈ : ∀ {eq : f ∘ h ≈ zero⇒} {eq′ : f ∘ i ≈ zero⇒} →
    h ≈ i → universal eq ≈ universal eq′
  universal-resp-≈ h≈i = unique (⟺ h≈i ○ factors)

  universal-∘ : f ∘ k ∘ h ≈ zero⇒ 
  universal-∘ {h = h} = begin
    f ∘ k ∘ h ≈⟨ pullˡ commute ⟩
    zero⇒ ∘ h ≈⟨ zero-∘ʳ h ⟩
    zero⇒ ∎

record Kernel {A B} (f : A ⇒ B) : Set (o ⊔ ℓ ⊔ e) where
  field
     {kernel} : Obj
     kernel⇒ : kernel ⇒ A
     isKernel : IsKernel kernel⇒ f

  open IsKernel isKernel public

IsKernel⇒Kernel : IsKernel k f → Kernel f
IsKernel⇒Kernel {k = k} isKernel = record
  { kernel⇒ = k
  ; isKernel = isKernel
  }
