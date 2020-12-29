{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Object.Zero

module Categories.Object.Kernel.Properties {o ℓ e} {𝒞 : Category o ℓ e} (𝒞-Zero : Zero 𝒞) where

open import Function using (_$_)

open import Categories.Diagram.Equalizer 𝒞
open import Categories.Diagram.Pullback 𝒞 renaming (glue to glue-pullback; up-to-iso to pullback-up-to-iso)
open import Categories.Diagram.Pullback.Properties 𝒞
open import Categories.Object.Kernel 𝒞-Zero
open import Categories.Object.Terminal 𝒞

open import Categories.Morphism 𝒞
open import Categories.Morphism.Reasoning 𝒞

open Category 𝒞
open HomReasoning
open Equiv

open Zero 𝒞-Zero

private
  variable
    A B : Obj
    f : A ⇒ B

-- We can express kernels as pullbacks along the morphism '! : ⊥ ⇒ A'.
Kernel⇒Pullback : Kernel f → Pullback f !
Kernel⇒Pullback {f = f} kernel = record
  { p₁ = kernel⇒
  ; p₂ = ¡
  ; isPullback = record
    { commute = commute
    ; universal = λ {C} {h₁} {h₂} eq → universal {h = h₁} $ begin
      f ∘ h₁ ≈⟨ eq ⟩
      ! ∘ h₂ ≈˘⟨ refl⟩∘⟨ ¡-unique h₂ ⟩
      zero⇒ ∎
    ; unique = λ {C} {h₁} {h₂} {i} k-eq h-eq → unique $ begin
      h₁ ≈˘⟨ k-eq ⟩
      kernel⇒ ∘ i ∎
    ; p₁∘universal≈h₁ = ⟺ factors
    ; p₂∘universal≈h₂ = ¡-unique₂ _ _
    }
  }
  where
    open Kernel kernel

-- All pullbacks along the morphism '! : ⊥ ⇒ A' are also kernels.
Pullback⇒Kernel : Pullback f ! → Kernel f
Pullback⇒Kernel {f = f} pullback = record
  { kernel⇒ = p₁
  ; isKernel = record
    { commute = begin
      f ∘ p₁ ≈⟨ commute ⟩
      ! ∘ p₂ ≈˘⟨ refl⟩∘⟨ ¡-unique p₂ ⟩
      zero⇒ ∎
    ; universal = λ eq → universal eq
    ; factors = ⟺ p₁∘universal≈h₁
    ; unique = λ eq → unique (⟺ eq) (⟺ (¡-unique _))
    }
  }
  where
    open Pullback pullback

-- We can also express kernels as the equalizer of 'f' and the zero morphism.
Kernel⇒Equalizer : Kernel f → Equalizer f zero⇒
Kernel⇒Equalizer {f = f} kernel = record
  { arr = kernel⇒
  ; isEqualizer = record
    { equality = begin
      f ∘ kernel⇒ ≈⟨ commute ⟩
      zero⇒       ≈⟨ pushʳ (¡-unique (¡ ∘ kernel⇒)) ⟩
      zero⇒ ∘ kernel⇒ ∎
    ; equalize = λ {_} {h} eq → universal (eq ○ pullʳ (⟺ (¡-unique (¡ ∘ h))))
    ; universal = factors
    ; unique = unique
    }
  }
  where
    open Kernel kernel

-- Furthermore, all equalizers of 'f' and the zero morphism are equalizers
Equalizer⇒Kernel : Equalizer f zero⇒ → Kernel f
Equalizer⇒Kernel {f = f} equalizer = record
  { kernel⇒ = arr
  ; isKernel = record
    { commute = begin
      f ∘ arr      ≈⟨ equality ⟩
      zero⇒ ∘ arr ≈⟨ pullʳ (⟺ (¡-unique (¡ ∘ arr))) ⟩
      zero⇒ ∎
    ; universal = λ {_} {h} eq → equalize (eq ○ pushʳ (¡-unique (¡ ∘ h)))
    ; factors = universal
    ; unique = unique
    }
  }
  where
    open Equalizer equalizer

module _ (K : Kernel f) where
  open Kernel K

  Kernel-Mono : Mono kernel⇒
  Kernel-Mono g₁ g₂ eq = begin
    g₁ ≈⟨ unique refl ⟩
    universal universal-∘ ≈˘⟨ unique eq ⟩
    g₂ ∎

module _ (has-kernels : ∀ {A B} → (f : A ⇒ B) → Kernel f) where

  -- The kernel of a kernel is isomorphic to the zero object.
  kernel²-zero : ∀ {A B} {f : A ⇒ B} → Kernel.kernel (has-kernels (Kernel.kernel⇒ (has-kernels f))) ≅ zero
  kernel²-zero {B = B} {f = f} = pullback-up-to-iso kernel-pullback (pullback-mono-mono !-Mono)
    where
      K : Kernel f
      K = has-kernels f

      module K = Kernel K

      K′ : Kernel K.kernel⇒
      K′ = has-kernels K.kernel⇒

      kernel-pullback : Pullback ! !
      kernel-pullback = Pullback-resp-≈ (glue-pullback (Kernel⇒Pullback K) (swap (Kernel⇒Pullback K′))) (!-unique (f ∘ !)) refl

      pullback-mono-mono : ∀ {A B} {f : A ⇒ B} → Mono f → Pullback f f
      pullback-mono-mono mono = record
        { p₁ = id
        ; p₂ = id
        ; isPullback = pullback-self-mono mono
        }
