{-# OPTIONS --without-K --safe #-}

-- Monoidal natural isomorphisms between lax and strong symmetric
-- monoidal functors.
--
-- NOTE. Symmetric monoidal natural isomorphisms are really just
-- monoidal natural isomorphisms that happen to go between symmetric
-- monoidal functors.  No additional conditions are necessary.
-- Nevertheless, the definitions in this module are useful when one is
-- working in a symmetric monoidal setting.  They also help Agda's
-- type checker by bundling the (symmetric monoidal) categories and
-- functors involved.

module Categories.NaturalTransformation.NaturalIsomorphism.Monoidal.Symmetric
  where

open import Level
open import Relation.Binary using (IsEquivalence)

open import Categories.Category.Monoidal using (SymmetricMonoidalCategory)
import Categories.Functor.Monoidal.Symmetric as SMF
open import Categories.Functor.Monoidal.Symmetric.Properties using () renaming
  ( idF-SymmetricMonoidal to idFˡ  ; idF-StrongSymmetricMonoidal to idFˢ
  ; ∘-SymmetricMonoidal   to _∘Fˡ_ ; ∘-StrongSymmetricMonoidal   to _∘Fˢ_
  )
import Categories.NaturalTransformation.Monoidal.Symmetric as SMNT
open import Categories.NaturalTransformation.NaturalIsomorphism as NI
  using (NaturalIsomorphism)
import Categories.NaturalTransformation.NaturalIsomorphism.Monoidal as MNI

module Lax where
  open SMF.Lax using (SymmetricMonoidalFunctor)
  open MNI.Lax using (IsMonoidalNaturalIsomorphism)
  open SMNT.Lax using (SymmetricMonoidalNaturalTransformation)
  open SymmetricMonoidalFunctor using ()
    renaming (F to UF; monoidalFunctor to MF)
  private module U = MNI.Lax

  module _ {o ℓ e o′ ℓ′ e′}
           {C : SymmetricMonoidalCategory o ℓ e}
           {D : SymmetricMonoidalCategory o′ ℓ′ e′} where

    -- Monoidal natural isomorphisms between lax symmetric monoidal functors.

    record SymmetricMonoidalNaturalIsomorphism
           (F G : SymmetricMonoidalFunctor C D) : Set (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) where

      field
        U              : NaturalIsomorphism (UF F) (UF G)
        F⇒G-isMonoidal : IsMonoidalNaturalIsomorphism (MF F) (MF G) U

      ⌊_⌋ : U.MonoidalNaturalIsomorphism (MF F) (MF G)
      ⌊_⌋ = record { U = U ; F⇒G-isMonoidal = F⇒G-isMonoidal }

      open U.MonoidalNaturalIsomorphism ⌊_⌋ public
        hiding (U; F⇒G-isMonoidal; F⇒G-monoidal; F⇐G-monoidal)

      F⇒G-monoidal : SymmetricMonoidalNaturalTransformation F G
      F⇒G-monoidal = record { U = F⇒G ; isMonoidal = F⇒G-isMonoidal }

      F⇐G-monoidal : SymmetricMonoidalNaturalTransformation G F
      F⇐G-monoidal = record { U = F⇐G ; isMonoidal = F⇐G-isMonoidal }

    infix 4 _≃_

    _≃_ = SymmetricMonoidalNaturalIsomorphism

    -- "Strengthening"

    ⌈_⌉ : {F G : SymmetricMonoidalFunctor C D} →
          U.MonoidalNaturalIsomorphism (MF F) (MF G) → F ≃ G
    ⌈ α ⌉ = record { U = U ; F⇒G-isMonoidal = F⇒G-isMonoidal }
      where open U.MonoidalNaturalIsomorphism α

    open SymmetricMonoidalNaturalIsomorphism

    -- Identity and compositions

    infixr 9 _ⓘᵥ_

    id : {F : SymmetricMonoidalFunctor C D} → F ≃ F
    id = ⌈ U.id ⌉

    _ⓘᵥ_ : {F G H : SymmetricMonoidalFunctor C D} → G ≃ H → F ≃ G → F ≃ H
    α ⓘᵥ β   = ⌈ ⌊ α ⌋ U.ⓘᵥ ⌊ β ⌋ ⌉

    isEquivalence : IsEquivalence _≃_
    isEquivalence = record
      { refl  = id
      ; sym   = λ α → record
        { U              = NI.sym (U α)
        ; F⇒G-isMonoidal = F⇐G-isMonoidal α
        }
      ; trans = λ α β → β ⓘᵥ α
      }

  open SymmetricMonoidalNaturalIsomorphism

  module _ {o ℓ e o′ ℓ′ e′ o″ ℓ″ e″}
           {C : SymmetricMonoidalCategory o ℓ e}
           {D : SymmetricMonoidalCategory o′ ℓ′ e′}
           {E : SymmetricMonoidalCategory o″ ℓ″ e″} where

    infixr 9 _ⓘₕ_ _ⓘˡ_ _ⓘʳ_

    _ⓘₕ_ : {F G : SymmetricMonoidalFunctor C D}
           {H I : SymmetricMonoidalFunctor D E} →
           H ≃ I → F ≃ G → (H ∘Fˡ F) ≃ (I ∘Fˡ G)
    -- NOTE: this definition is clearly equivalent to
    --
    --   α ⓘₕ β = ⌈ ⌊ α ⌋ U.ⓘₕ ⌊ β ⌋ ⌉
    --
    -- but the latter takes an unreasonably long time to typecheck,
    -- while the unfolded version typechecks almost immediately.
    α ⓘₕ β = record
      { U               = C.U
      ; F⇒G-isMonoidal  = record
        { ε-compat      = C.ε-compat
        ; ⊗-homo-compat = C.⊗-homo-compat }
        }
      where module C = U.MonoidalNaturalIsomorphism (⌊ α ⌋ U.ⓘₕ ⌊ β ⌋)

    _ⓘˡ_ : {F G : SymmetricMonoidalFunctor C D}
           (H : SymmetricMonoidalFunctor D E) → F ≃ G → (H ∘Fˡ F) ≃ (H ∘Fˡ G)
    H ⓘˡ α = id {F = H} ⓘₕ α

    _ⓘʳ_ : {G H : SymmetricMonoidalFunctor D E} →
           G ≃ H → (F : SymmetricMonoidalFunctor C D) → (G ∘Fˡ F) ≃ (H ∘Fˡ F)
    α ⓘʳ F = α ⓘₕ id {F = F}

  -- Left and right unitors.

  module _ {o ℓ e o′ ℓ′ e′}
           {C : SymmetricMonoidalCategory o ℓ e}
           {D : SymmetricMonoidalCategory o′ ℓ′ e′}
           {F : SymmetricMonoidalFunctor C D} where

    -- NOTE: Again, manual expansion seems necessary to type check in
    -- reasonable time.

    unitorˡ : idFˡ D ∘Fˡ F ≃ F
    unitorˡ = record
      { U               = LU.U
      ; F⇒G-isMonoidal  = record
        { ε-compat      = LU.ε-compat
        ; ⊗-homo-compat = LU.⊗-homo-compat
        }
      }
      where module LU = U.MonoidalNaturalIsomorphism (U.unitorˡ {F = MF F})

    unitorʳ : F ∘Fˡ idFˡ C ≃ F
    unitorʳ = record
      { U               = RU.U
      ; F⇒G-isMonoidal  = record
        { ε-compat      = RU.ε-compat
        ; ⊗-homo-compat = RU.⊗-homo-compat
        }
      }
      where module RU = U.MonoidalNaturalIsomorphism (U.unitorʳ {F = MF F})

  -- Associator.

  module _ {o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ o‴ ℓ‴ e‴}
           {B : SymmetricMonoidalCategory o ℓ e}
           {C : SymmetricMonoidalCategory o′ ℓ′ e′}
           {D : SymmetricMonoidalCategory o″ ℓ″ e″}
           {E : SymmetricMonoidalCategory o‴ ℓ‴ e‴}
           {F : SymmetricMonoidalFunctor B C}
           {G : SymmetricMonoidalFunctor C D}
           {H : SymmetricMonoidalFunctor D E} where

    -- NOTE: Again, manual expansion seems necessary to type check in
    -- reasonable time.

    associator : (H ∘Fˡ G) ∘Fˡ F ≃ H ∘Fˡ (G ∘Fˡ F)
    associator = record
      { U               = AU.U
      ; F⇒G-isMonoidal  = record
        { ε-compat      = AU.ε-compat
        ; ⊗-homo-compat = AU.⊗-homo-compat
        }
      }
      where
        module AU =
          U.MonoidalNaturalIsomorphism (U.associator {F = MF F} {MF G} {MF H})

module Strong where
  open SMF.Strong using (SymmetricMonoidalFunctor)
  open MNI.Strong using (IsMonoidalNaturalIsomorphism)
  open SMNT.Strong using (SymmetricMonoidalNaturalTransformation)
  open SymmetricMonoidalFunctor using () renaming
    ( F                         to UF
    ; monoidalFunctor           to MF
    ; laxSymmetricMonoidalFunctor to laxSMF
    )
  private module U = MNI.Strong

  module _ {o ℓ e o′ ℓ′ e′}
           {C : SymmetricMonoidalCategory o ℓ e}
           {D : SymmetricMonoidalCategory o′ ℓ′ e′} where

    -- Monoidal natural isomorphisms between strong symmetric monoidal functors.

    record SymmetricMonoidalNaturalIsomorphism
           (F G : SymmetricMonoidalFunctor C D) : Set (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) where

      field
        U              : NaturalIsomorphism (UF F) (UF G)
        F⇒G-isMonoidal : IsMonoidalNaturalIsomorphism (MF F) (MF G) U

      ⌊_⌋ : U.MonoidalNaturalIsomorphism (MF F) (MF G)
      ⌊_⌋ = record { U = U ; F⇒G-isMonoidal = F⇒G-isMonoidal }

      open U.MonoidalNaturalIsomorphism ⌊_⌋ public
        hiding (U; F⇒G-isMonoidal; F⇒G-monoidal; F⇐G-monoidal)

      F⇒G-monoidal : SymmetricMonoidalNaturalTransformation F G
      F⇒G-monoidal = record { U = F⇒G ; isMonoidal = F⇒G-isMonoidal }

      F⇐G-monoidal : SymmetricMonoidalNaturalTransformation G F
      F⇐G-monoidal = record { U = F⇐G ; isMonoidal = F⇐G-isMonoidal }

      laxSNI : Lax.SymmetricMonoidalNaturalIsomorphism (laxSMF F) (laxSMF G)
      laxSNI = record { U = U ; F⇒G-isMonoidal = F⇒G-isMonoidal }

    infix 4 _≃_

    _≃_ = SymmetricMonoidalNaturalIsomorphism

    -- "Strengthening"

    ⌈_⌉ : {F G : SymmetricMonoidalFunctor C D} →
          U.MonoidalNaturalIsomorphism (MF F) (MF G) → F ≃ G
    ⌈ α ⌉ = record { U = U ; F⇒G-isMonoidal = F⇒G-isMonoidal }
      where open U.MonoidalNaturalIsomorphism α

    open SymmetricMonoidalNaturalIsomorphism

    -- Identity and compositions

    infixr 9 _ⓘᵥ_

    id : {F : SymmetricMonoidalFunctor C D} → F ≃ F
    id = ⌈ U.id ⌉

    _ⓘᵥ_ : {F G H : SymmetricMonoidalFunctor C D} → G ≃ H → F ≃ G → F ≃ H
    α ⓘᵥ β   = ⌈ ⌊ α ⌋ U.ⓘᵥ ⌊ β ⌋ ⌉

    isEquivalence : IsEquivalence _≃_
    isEquivalence = record
      { refl  = id
      ; sym   = λ α → record
        { U              = NI.sym (U α)
        ; F⇒G-isMonoidal = F⇐G-isMonoidal α
        }
      ; trans = λ α β → β ⓘᵥ α
      }

  open SymmetricMonoidalNaturalIsomorphism

  module _ {o ℓ e o′ ℓ′ e′ o″ ℓ″ e″}
           {C : SymmetricMonoidalCategory o ℓ e}
           {D : SymmetricMonoidalCategory o′ ℓ′ e′}
           {E : SymmetricMonoidalCategory o″ ℓ″ e″} where

    infixr 9 _ⓘₕ_ _ⓘˡ_ _ⓘʳ_

    _ⓘₕ_ : {F G : SymmetricMonoidalFunctor C D}
           {H I : SymmetricMonoidalFunctor D E} →
           H ≃ I → F ≃ G → (H ∘Fˢ F) ≃ (I ∘Fˢ G)
    -- NOTE: this definition is clearly equivalent to
    --
    --   α ⓘₕ β = ⌈ ⌊ α ⌋ U.ⓘₕ ⌊ β ⌋ ⌉
    --
    -- but the latter takes an unreasonably long time to typecheck,
    -- while the unfolded version typechecks almost immediately.
    α ⓘₕ β = record
      { U               = C.U
      ; F⇒G-isMonoidal  = record
        { ε-compat      = C.ε-compat
        ; ⊗-homo-compat = C.⊗-homo-compat }
        }
      where module C = U.MonoidalNaturalIsomorphism (⌊ α ⌋ U.ⓘₕ ⌊ β ⌋)

    _ⓘˡ_ : {F G : SymmetricMonoidalFunctor C D}
           (H : SymmetricMonoidalFunctor D E) → F ≃ G → (H ∘Fˢ F) ≃ (H ∘Fˢ G)
    H ⓘˡ α = id {F = H} ⓘₕ α

    _ⓘʳ_ : {G H : SymmetricMonoidalFunctor D E} →
           G ≃ H → (F : SymmetricMonoidalFunctor C D) → (G ∘Fˢ F) ≃ (H ∘Fˢ F)
    α ⓘʳ F = α ⓘₕ id {F = F}

  -- Left and right unitors.

  module _ {o ℓ e o′ ℓ′ e′}
           {C : SymmetricMonoidalCategory o ℓ e}
           {D : SymmetricMonoidalCategory o′ ℓ′ e′}
           {F : SymmetricMonoidalFunctor C D} where

    -- NOTE: Again, manual expansion seems necessary to type check in
    -- reasonable time.

    unitorˡ : idFˢ D ∘Fˢ F ≃ F
    unitorˡ = record
      { U               = LU.U
      ; F⇒G-isMonoidal  = record
        { ε-compat      = LU.ε-compat
        ; ⊗-homo-compat = LU.⊗-homo-compat
        }
      }
      where module LU = U.MonoidalNaturalIsomorphism (U.unitorˡ {F = MF F})

    unitorʳ : F ∘Fˢ idFˢ C ≃ F
    unitorʳ = record
      { U               = RU.U
      ; F⇒G-isMonoidal  = record
        { ε-compat      = RU.ε-compat
        ; ⊗-homo-compat = RU.⊗-homo-compat
        }
      }
      where module RU = U.MonoidalNaturalIsomorphism (U.unitorʳ {F = MF F})

  -- Associator.

  module _ {o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ o‴ ℓ‴ e‴}
           {B : SymmetricMonoidalCategory o ℓ e}
           {C : SymmetricMonoidalCategory o′ ℓ′ e′}
           {D : SymmetricMonoidalCategory o″ ℓ″ e″}
           {E : SymmetricMonoidalCategory o‴ ℓ‴ e‴}
           {F : SymmetricMonoidalFunctor B C}
           {G : SymmetricMonoidalFunctor C D}
           {H : SymmetricMonoidalFunctor D E} where

    -- NOTE: Again, manual expansion seems necessary to type check in
    -- reasonable time.

    associator : (H ∘Fˢ G) ∘Fˢ F ≃ H ∘Fˢ (G ∘Fˢ F)
    associator = record
      { U               = AU.U
      ; F⇒G-isMonoidal  = record
        { ε-compat      = AU.ε-compat
        ; ⊗-homo-compat = AU.⊗-homo-compat
        }
      }
      where
        module AU =
          U.MonoidalNaturalIsomorphism (U.associator {F = MF F} {MF G} {MF H})
