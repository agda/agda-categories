{-# OPTIONS --without-K --safe #-}

-- Monoidal natural isomorphisms between lax and strong braided
-- monoidal functors.
--
-- NOTE. Braided monoidal natural isomorphisms are really just
-- monoidal natural isomorphisms that happen to go between braided
-- monoidal functors.  No additional conditions are necessary.
-- Nevertheless, the definitions in this module are useful when one is
-- working in a braided monoidal setting.  They also help Agda's type
-- checker by bundling the (braided monoidal) categories and functors
-- involved.

module Categories.NaturalTransformation.NaturalIsomorphism.Monoidal.Braided
  where

open import Level
open import Relation.Binary using (IsEquivalence)

open import Categories.Category.Monoidal using (BraidedMonoidalCategory)
import Categories.Functor.Monoidal.Braided as BMF
open import Categories.Functor.Monoidal.Properties using () renaming
  ( idF-BraidedMonoidal to idFˡ  ; idF-StrongBraidedMonoidal to idFˢ
  ; ∘-BraidedMonoidal   to _∘Fˡ_ ; ∘-StrongBraidedMonoidal   to _∘Fˢ_
  )
open import Categories.NaturalTransformation.NaturalIsomorphism as NI
  using (NaturalIsomorphism)
import Categories.NaturalTransformation.NaturalIsomorphism.Monoidal as MNI

module Lax where
  open BMF.Lax using (BraidedMonoidalFunctor)
  open MNI.Lax using (IsMonoidalNaturalIsomorphism)
  open BraidedMonoidalFunctor using () renaming (F to UF; monoidalFunctor to MF)
  private module U = MNI.Lax

  module _ {o ℓ e o′ ℓ′ e′}
           {C : BraidedMonoidalCategory o ℓ e}
           {D : BraidedMonoidalCategory o′ ℓ′ e′} where

    -- Monoidal natural isomorphisms between lax braided monoidal functors.

    record BraidedMonoidalNaturalIsomorphism
           (F G : BraidedMonoidalFunctor C D) : Set (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) where

      field
        U              : NaturalIsomorphism (UF F) (UF G)
        F⇒G-isMonoidal : IsMonoidalNaturalIsomorphism (MF F) (MF G) U

      ⌊_⌋ : U.MonoidalNaturalIsomorphism (MF F) (MF G)
      ⌊_⌋ = record { U = U ; F⇒G-isMonoidal = F⇒G-isMonoidal }

      open U.MonoidalNaturalIsomorphism ⌊_⌋ public hiding (U; F⇒G-isMonoidal)

    infix 4 _≃_

    _≃_ = BraidedMonoidalNaturalIsomorphism

    -- "Strengthening"

    ⌈_⌉ : {F G : BraidedMonoidalFunctor C D} →
          U.MonoidalNaturalIsomorphism (MF F) (MF G) → F ≃ G
    ⌈ α ⌉ = record { U = U ; F⇒G-isMonoidal = F⇒G-isMonoidal }
      where open U.MonoidalNaturalIsomorphism α

    open BraidedMonoidalNaturalIsomorphism

    -- Identity and compositions

    infixr 9 _ⓘᵥ_

    id : {F : BraidedMonoidalFunctor C D} → F ≃ F
    id = ⌈ U.id ⌉

    _ⓘᵥ_ : {F G H : BraidedMonoidalFunctor C D} → G ≃ H → F ≃ G → F ≃ H
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

  open BraidedMonoidalNaturalIsomorphism

  module _ {o ℓ e o′ ℓ′ e′ o″ ℓ″ e″}
           {C : BraidedMonoidalCategory o ℓ e}
           {D : BraidedMonoidalCategory o′ ℓ′ e′}
           {E : BraidedMonoidalCategory o″ ℓ″ e″} where

    infixr 9 _ⓘₕ_ _ⓘˡ_ _ⓘʳ_

    _ⓘₕ_ : {F G : BraidedMonoidalFunctor C D}
           {H I : BraidedMonoidalFunctor D E} →
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

    _ⓘˡ_ : {F G : BraidedMonoidalFunctor C D}
           (H : BraidedMonoidalFunctor D E) → F ≃ G → (H ∘Fˡ F) ≃ (H ∘Fˡ G)
    H ⓘˡ α = id {F = H} ⓘₕ α

    _ⓘʳ_ : {G H : BraidedMonoidalFunctor D E} →
           G ≃ H → (F : BraidedMonoidalFunctor C D) → (G ∘Fˡ F) ≃ (H ∘Fˡ F)
    α ⓘʳ F = α ⓘₕ id {F = F}

  -- Left and right unitors.

  module _ {o ℓ e o′ ℓ′ e′}
           {C : BraidedMonoidalCategory o ℓ e}
           {D : BraidedMonoidalCategory o′ ℓ′ e′}
           {F : BraidedMonoidalFunctor C D} where

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
           {B : BraidedMonoidalCategory o ℓ e}
           {C : BraidedMonoidalCategory o′ ℓ′ e′}
           {D : BraidedMonoidalCategory o″ ℓ″ e″}
           {E : BraidedMonoidalCategory o‴ ℓ‴ e‴}
           {F : BraidedMonoidalFunctor B C} {G : BraidedMonoidalFunctor C D}
           {H : BraidedMonoidalFunctor D E} where

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
  open BMF.Strong using (BraidedMonoidalFunctor)
  open MNI.Strong using (IsMonoidalNaturalIsomorphism)
  open BraidedMonoidalFunctor using () renaming
    ( F                         to UF
    ; monoidalFunctor           to MF
    ; laxBraidedMonoidalFunctor to laxBMF
    )
  private module U = MNI.Strong

  module _ {o ℓ e o′ ℓ′ e′}
           {C : BraidedMonoidalCategory o ℓ e}
           {D : BraidedMonoidalCategory o′ ℓ′ e′} where

    -- Monoidal natural isomorphisms between strong braided monoidal functors.

    record BraidedMonoidalNaturalIsomorphism
           (F G : BraidedMonoidalFunctor C D) : Set (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) where

      field
        U              : NaturalIsomorphism (UF F) (UF G)
        F⇒G-isMonoidal : IsMonoidalNaturalIsomorphism (MF F) (MF G) U

      ⌊_⌋ : U.MonoidalNaturalIsomorphism (MF F) (MF G)
      ⌊_⌋ = record { U = U ; F⇒G-isMonoidal = F⇒G-isMonoidal }

      laxBNI : Lax.BraidedMonoidalNaturalIsomorphism (laxBMF F) (laxBMF G)
      laxBNI = record { U = U ; F⇒G-isMonoidal = F⇒G-isMonoidal }

      open Lax.BraidedMonoidalNaturalIsomorphism laxBNI public
        hiding (U; F⇒G-isMonoidal; ⌊_⌋)

    infix 4 _≃_

    _≃_ = BraidedMonoidalNaturalIsomorphism

    -- "Strengthening"

    ⌈_⌉ : {F G : BraidedMonoidalFunctor C D} →
          U.MonoidalNaturalIsomorphism (MF F) (MF G) → F ≃ G
    ⌈ α ⌉ = record { U = U ; F⇒G-isMonoidal = F⇒G-isMonoidal }
      where open U.MonoidalNaturalIsomorphism α

    open BraidedMonoidalNaturalIsomorphism

    -- Identity and compositions

    infixr 9 _ⓘᵥ_

    id : {F : BraidedMonoidalFunctor C D} → F ≃ F
    id = ⌈ U.id ⌉

    _ⓘᵥ_ : {F G H : BraidedMonoidalFunctor C D} → G ≃ H → F ≃ G → F ≃ H
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

  open BraidedMonoidalNaturalIsomorphism

  module _ {o ℓ e o′ ℓ′ e′ o″ ℓ″ e″}
           {C : BraidedMonoidalCategory o ℓ e}
           {D : BraidedMonoidalCategory o′ ℓ′ e′}
           {E : BraidedMonoidalCategory o″ ℓ″ e″} where

    infixr 9 _ⓘₕ_ _ⓘˡ_ _ⓘʳ_

    _ⓘₕ_ : {F G : BraidedMonoidalFunctor C D}
           {H I : BraidedMonoidalFunctor D E} →
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

    _ⓘˡ_ : {F G : BraidedMonoidalFunctor C D}
           (H : BraidedMonoidalFunctor D E) → F ≃ G → (H ∘Fˢ F) ≃ (H ∘Fˢ G)
    H ⓘˡ α = id {F = H} ⓘₕ α

    _ⓘʳ_ : {G H : BraidedMonoidalFunctor D E} →
           G ≃ H → (F : BraidedMonoidalFunctor C D) → (G ∘Fˢ F) ≃ (H ∘Fˢ F)
    α ⓘʳ F = α ⓘₕ id {F = F}

  -- Left and right unitors.

  module _ {o ℓ e o′ ℓ′ e′}
           {C : BraidedMonoidalCategory o ℓ e}
           {D : BraidedMonoidalCategory o′ ℓ′ e′}
           {F : BraidedMonoidalFunctor C D} where

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
           {B : BraidedMonoidalCategory o ℓ e}
           {C : BraidedMonoidalCategory o′ ℓ′ e′}
           {D : BraidedMonoidalCategory o″ ℓ″ e″}
           {E : BraidedMonoidalCategory o‴ ℓ‴ e‴}
           {F : BraidedMonoidalFunctor B C} {G : BraidedMonoidalFunctor C D}
           {H : BraidedMonoidalFunctor D E} where

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
