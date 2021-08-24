{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Monoidal.Bundle
  using (SymmetricMonoidalCategory)

module Categories.Category.Construction.SymmetricMonoidalFunctors
  {o ℓ e o′ ℓ′ e′}
  (C : SymmetricMonoidalCategory o ℓ e)
  (D : SymmetricMonoidalCategory o′ ℓ′ e′) where

-- The symmetric monoidal category [C , D] of symmetric monoidal
-- functors between the symmetric monoidal categories C and D.

open import Level
open import Data.Product using (_,_; uncurry′)

open import Categories.Category using (Category)
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Braided using (Braided)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
import Categories.Functor.Monoidal.Symmetric as SMF
import Categories.Functor.Monoidal.PointwiseTensor as PT
import Categories.NaturalTransformation.Monoidal.Symmetric as SMNT
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)
import Categories.NaturalTransformation.NaturalIsomorphism.Monoidal.Symmetric as SMNI
open import Categories.Functor.Bifunctor using (Bifunctor)

import Categories.Morphism as Morphism
open SymmetricMonoidalCategory D

module Lax where
  open SMF.Lax
  open SMNT.Lax renaming (id to idNT)

  -- The category of symmetric monoidal functors.

  MonoidalFunctorsU : Category (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) (o ⊔ ℓ ⊔ ℓ′ ⊔ e′)
                               (o ⊔ e′)
  MonoidalFunctorsU = record
    { Obj = SymmetricMonoidalFunctor C D
    ; _⇒_ = SymmetricMonoidalNaturalTransformation
    ; _≈_ = λ α β → ∀ {X} → η α X ≈ η β X
    ; id  = idNT
    ; _∘_ = _∘ᵥ_
    ; assoc     = assoc
    ; sym-assoc = sym-assoc
    ; identityˡ = identityˡ
    ; identityʳ = identityʳ
    ; identity² = identity²
    ; equiv     = record
      { refl  = Equiv.refl
      ; sym   = λ α≈β → Equiv.sym α≈β
      ; trans = λ α≈β β≈γ → Equiv.trans α≈β β≈γ
      }
    ; ∘-resp-≈ = λ α₁≈β₁ α₂≈β₂ → ∘-resp-≈ α₁≈β₁ α₂≈β₂
    }
    where open SymmetricMonoidalNaturalTransformation using (η)

  open SMNI.Lax using (_≃_)
  open Morphism MonoidalFunctorsU using (_≅_)

  -- Symmetric natural isos are isos in the functor category.

  ≃⇒≅ : ∀ {F G : SymmetricMonoidalFunctor C D} → F ≃ G → F ≅ G
  ≃⇒≅ ni = record
    { from = ni.F⇒G-monoidal
    ; to   = ni.F⇐G-monoidal
    ; iso  = record
      { isoˡ = λ {X} → ni.iso.isoˡ X
      ; isoʳ = λ {X} → ni.iso.isoʳ X
      }
    }
    where module ni = SMNI.Lax.SymmetricMonoidalNaturalIsomorphism ni

  open PT.Lax

  MonoidalFunctorsU-monoidal : Monoidal MonoidalFunctorsU
  MonoidalFunctorsU-monoidal = monoidalHelper MonoidalFunctorsU (record
    { ⊗ = record
      { F₀            = uncurry′ _⊗̇₀_
      ; F₁            = uncurry′ _⊗̇₁_
      ; identity      = ⊗.identity
      ; homomorphism  = ⊗.homomorphism
      ; F-resp-≈      = λ{ (eq₁ , eq₂) → ⊗.F-resp-≈ (eq₁ , eq₂) }
      }
    ; unit            = unitF
    ; unitorˡ         = λ {F} → ≃⇒≅ (⊗̇-unitorˡ {F = F})
    ; unitorʳ         = λ {F} → ≃⇒≅ (⊗̇-unitorʳ {F = F})
    ; associator      = λ {F G H} → record
      -- NOTE: this is clearly the same as
      --
      --   ≃⇒≅ (⊗̇-associator {F = F} {G} {H})
      --
      -- but the manual expansion seems necessary for Agda to finish
      -- typechecking it.
      { from          = record
        { U           = ⊗̇-associator.F⇒G {F = F} {G} {H}
        ; isMonoidal  = record
          { ε-compat      = ⊗̇-associator.ε-compat {F = F} {G} {H}
          ; ⊗-homo-compat = ⊗̇-associator.⊗-homo-compat {F = F} {G} {H}
          }
        }
      ; to            = record
        { U           = ⊗̇-associator.F⇐G {F = F} {G} {H}
        ; isMonoidal  = record
          { ε-compat      = ⊗̇-associator.⇐.ε-compat {F = F} {G} {H}
          ; ⊗-homo-compat = ⊗̇-associator.⇐.⊗-homo-compat {F = F} {G} {H}
          }
        }
      ; iso           = record
        { isoˡ        = associator.isoˡ
        ; isoʳ        = associator.isoʳ
        }
      }
    ; unitorˡ-commute = unitorˡ-commute-from
    ; unitorʳ-commute = unitorʳ-commute-from
    ; assoc-commute   = assoc-commute-from
    ; triangle        = triangle
    ; pentagon        = pentagon
    })

  MonoidalFunctorsU-braided : Braided MonoidalFunctorsU-monoidal
  MonoidalFunctorsU-braided = record
    { braiding            = niHelper (record
      { η                 = λ{ (F , G) → record
        { U               = ⊗̇-braiding.F⇒G {F = F} {G}
        ; isMonoidal      = record
          { ε-compat      = ⊗̇-braiding.ε-compat {F = F} {G}
          ; ⊗-homo-compat = ⊗̇-braiding.⊗-homo-compat {F = F} {G}
          }
        } }
      ; η⁻¹               = λ{ (F , G) → record
        { U               = ⊗̇-braiding.F⇐G {F = F} {G}
        ; isMonoidal      = record
          { ε-compat      = ⊗̇-braiding.⇐.ε-compat {F = F} {G}
          ; ⊗-homo-compat = ⊗̇-braiding.⇐.⊗-homo-compat {F = F} {G}
          }
        } }
      ; commute = λ{ (β , γ) {X} →
                     let module β = SymmetricMonoidalNaturalTransformation β
                         module γ = SymmetricMonoidalNaturalTransformation γ
                     in braiding.⇒.commute (β.η X , γ.η X) }
      ; iso     = λ _ → record
        { isoˡ  = braiding.iso.isoˡ _
        ; isoʳ  = braiding.iso.isoʳ _ }
      })
    ; hexagon₁  = hexagon₁
    ; hexagon₂  = hexagon₂
    }

  MonoidalFunctorsU-symmetric : Symmetric MonoidalFunctorsU-monoidal
  MonoidalFunctorsU-symmetric = record
    { braided     = MonoidalFunctorsU-braided
    ; commutative = commutative
    }

  MonoidalFunctors : SymmetricMonoidalCategory (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′)
                                               (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) (o ⊔ e′)
  MonoidalFunctors = record
    { U         = MonoidalFunctorsU
    ; monoidal  = MonoidalFunctorsU-monoidal
    ; symmetric = MonoidalFunctorsU-symmetric
    }

module Strong where
  open SMF.Strong
  open SMNT.Strong renaming (id to idNT)

  -- The category of symmetric monoidal functors.

  MonoidalFunctorsU : Category (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) (o ⊔ ℓ ⊔ ℓ′ ⊔ e′)
                               (o ⊔ e′)
  MonoidalFunctorsU = record
    { Obj = SymmetricMonoidalFunctor C D
    ; _⇒_ = SymmetricMonoidalNaturalTransformation
    ; _≈_ = λ α β → ∀ {X} → η α X ≈ η β X
    ; id  = idNT
    ; _∘_ = _∘ᵥ_
    ; assoc     = assoc
    ; sym-assoc = sym-assoc
    ; identityˡ = identityˡ
    ; identityʳ = identityʳ
    ; identity² = identity²
    ; equiv     = record
      { refl  = Equiv.refl
      ; sym   = λ α≈β → Equiv.sym α≈β
      ; trans = λ α≈β β≈γ → Equiv.trans α≈β β≈γ
      }
    ; ∘-resp-≈ = λ α₁≈β₁ α₂≈β₂ → ∘-resp-≈ α₁≈β₁ α₂≈β₂
    }
    where open SymmetricMonoidalNaturalTransformation using (η)

  open SMNI.Strong using (_≃_)
  open Morphism MonoidalFunctorsU using (_≅_)

  -- Symmetric natural isos are isos in the functor category.

  ≃⇒≅ : ∀ {F G : SymmetricMonoidalFunctor C D} → F ≃ G → F ≅ G
  ≃⇒≅ ni = record
    { from = ni.F⇒G-monoidal
    ; to   = ni.F⇐G-monoidal
    ; iso  = record
      { isoˡ = λ {X} → ni.iso.isoˡ X
      ; isoʳ = λ {X} → ni.iso.isoʳ X
      }
    }
    where module ni = SMNI.Strong.SymmetricMonoidalNaturalIsomorphism ni

  open PT.Strong

  MonoidalFunctorsU-monoidal : Monoidal MonoidalFunctorsU
  MonoidalFunctorsU-monoidal = monoidalHelper MonoidalFunctorsU (record
    { ⊗ = record
      { F₀            = uncurry′ _⊗̇₀_
      ; F₁            = uncurry′ _⊗̇₁_
      ; identity      = ⊗.identity
      ; homomorphism  = ⊗.homomorphism
      ; F-resp-≈      = λ{ (eq₁ , eq₂) → ⊗.F-resp-≈ (eq₁ , eq₂) }
      }
    ; unit            = unitF
    ; unitorˡ         = λ {F} → ≃⇒≅ (⊗̇-unitorˡ {F = F})
    ; unitorʳ         = λ {F} → ≃⇒≅ (⊗̇-unitorʳ {F = F})
    ; associator      = λ {F G H} → record
      -- NOTE: this is clearly the same as
      --
      --   ≃⇒≅ (⊗̇-associator {F = F} {G} {H})
      --
      -- but the manual expansion seems necessary for Agda to finish
      -- typechecking it.
      { from          = record
        { U           = ⊗̇-associator.F⇒G {F = F} {G} {H}
        ; isMonoidal  = record
          { ε-compat      = ⊗̇-associator.ε-compat {F = F} {G} {H}
          ; ⊗-homo-compat = ⊗̇-associator.⊗-homo-compat {F = F} {G} {H}
          }
        }
      ; to            = record
        { U           = ⊗̇-associator.F⇐G {F = F} {G} {H}
        ; isMonoidal  = record
          { ε-compat      = ⊗̇-associator.⇐.ε-compat {F = F} {G} {H}
          ; ⊗-homo-compat = ⊗̇-associator.⇐.⊗-homo-compat {F = F} {G} {H}
          }
        }
      ; iso           = record
        { isoˡ        = associator.isoˡ
        ; isoʳ        = associator.isoʳ
        }
      }
    ; unitorˡ-commute = unitorˡ-commute-from
    ; unitorʳ-commute = unitorʳ-commute-from
    ; assoc-commute   = assoc-commute-from
    ; triangle        = triangle
    ; pentagon        = pentagon
    })

  MonoidalFunctorsU-braided : Braided MonoidalFunctorsU-monoidal
  MonoidalFunctorsU-braided = record
    { braiding            = niHelper (record
      { η                 = λ{ (F , G) → record
        { U               = ⊗̇-braiding.F⇒G {F = F} {G}
        ; isMonoidal      = record
          { ε-compat      = ⊗̇-braiding.ε-compat {F = F} {G}
          ; ⊗-homo-compat = ⊗̇-braiding.⊗-homo-compat {F = F} {G}
          }
        } }
      ; η⁻¹               = λ{ (F , G) → record
        { U               = ⊗̇-braiding.F⇐G {F = F} {G}
        ; isMonoidal      = record
          { ε-compat      = ⊗̇-braiding.⇐.ε-compat {F = F} {G}
          ; ⊗-homo-compat = ⊗̇-braiding.⇐.⊗-homo-compat {F = F} {G}
          }
        } }
      ; commute = λ{ (β , γ) {X} →
                     let module β = SymmetricMonoidalNaturalTransformation β
                         module γ = SymmetricMonoidalNaturalTransformation γ
                     in braiding.⇒.commute (β.η X , γ.η X) }
      ; iso     = λ _ → record
        { isoˡ  = braiding.iso.isoˡ _
        ; isoʳ  = braiding.iso.isoʳ _ }
      })
    ; hexagon₁  = hexagon₁
    ; hexagon₂  = hexagon₂
    }

  MonoidalFunctorsU-symmetric : Symmetric MonoidalFunctorsU-monoidal
  MonoidalFunctorsU-symmetric = record
    { braided     = MonoidalFunctorsU-braided
    ; commutative = commutative
    }

  MonoidalFunctors : SymmetricMonoidalCategory (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′)
                                               (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) (o ⊔ e′)
  MonoidalFunctors = record
    { U         = MonoidalFunctorsU
    ; monoidal  = MonoidalFunctorsU-monoidal
    ; symmetric = MonoidalFunctorsU-symmetric
    }
