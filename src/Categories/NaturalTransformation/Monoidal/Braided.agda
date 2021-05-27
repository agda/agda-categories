{-# OPTIONS --without-K --safe #-}

-- Monoidal natural transformations between lax and strong braided
-- monoidal functors.
--
-- NOTE. Braided monoidal natural transformations are really just
-- monoidal natural transformations that happen to go between braided
-- monoidal functors.  No additional conditions are necessary.
-- Nevertheless, the definitions in this module are useful when one is
-- working in a braided monoidal setting.  They also help Agda's type
-- checker by bundling the (braided monoidal) categories and functors
-- involved.
--
-- See
--  * John Baez, Some definitions everyone should know,
--    https://math.ucr.edu/home/baez/qg-fall2004/definitions.pdf
--  * https://ncatlab.org/nlab/show/monoidal+natural+transformation

module Categories.NaturalTransformation.Monoidal.Braided where

open import Level

open import Categories.Category.Monoidal using (BraidedMonoidalCategory)
import Categories.Functor.Monoidal.Braided as BMF
open import Categories.Functor.Monoidal.Properties using ()
  renaming (∘-BraidedMonoidal to _∘Fˡ_; ∘-StrongBraidedMonoidal to _∘Fˢ_)
open import Categories.NaturalTransformation as NT using (NaturalTransformation)
import Categories.NaturalTransformation.Monoidal as MNT

module Lax where
  open BMF.Lax using (BraidedMonoidalFunctor)
  open MNT.Lax using (IsMonoidalNaturalTransformation)
  open BraidedMonoidalFunctor using () renaming (F to UF; monoidalFunctor to MF)

  module _ {o ℓ e o′ ℓ′ e′}
           {C : BraidedMonoidalCategory o ℓ e}
           {D : BraidedMonoidalCategory o′ ℓ′ e′} where

    -- Monoidal natural transformations between braided monoidal functors.

    record BraidedMonoidalNaturalTransformation
           (F G : BraidedMonoidalFunctor C D) : Set (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) where

      field
        U          : NaturalTransformation (UF F) (UF G)
        isMonoidal : IsMonoidalNaturalTransformation (MF F) (MF G) U

      open NaturalTransformation           U          public
      open IsMonoidalNaturalTransformation isMonoidal public

  -- To shorten some definitions

  private
    _⇛_ = BraidedMonoidalNaturalTransformation
    module U = MNT.Lax

  module _ {o ℓ e o′ ℓ′ e′}
           {C : BraidedMonoidalCategory o ℓ e}
           {D : BraidedMonoidalCategory o′ ℓ′ e′} where

    -- Conversions

    ⌊_⌋ : {F G : BraidedMonoidalFunctor C D} →
          F ⇛ G → U.MonoidalNaturalTransformation (MF F) (MF G)
    ⌊ α ⌋ = record { U = U ; isMonoidal = isMonoidal }
      where open BraidedMonoidalNaturalTransformation α

    ⌈_⌉ : {F G : BraidedMonoidalFunctor C D} →
          U.MonoidalNaturalTransformation (MF F) (MF G) → F ⇛ G
    ⌈ α ⌉ = record { U = U ; isMonoidal = isMonoidal }
      where open U.MonoidalNaturalTransformation α

    -- Identity and compositions

    infixr 9 _∘ᵥ_

    id : {F : BraidedMonoidalFunctor C D} → F ⇛ F
    id = ⌈ U.id ⌉

    _∘ᵥ_ : {F G H : BraidedMonoidalFunctor C D} → G ⇛ H → F ⇛ G → F ⇛ H
    α ∘ᵥ β   = ⌈ ⌊ α ⌋ U.∘ᵥ ⌊ β ⌋ ⌉

  module _ {o ℓ e o′ ℓ′ e′ o″ ℓ″ e″}
           {C : BraidedMonoidalCategory o ℓ e}
           {D : BraidedMonoidalCategory o′ ℓ′ e′}
           {E : BraidedMonoidalCategory o″ ℓ″ e″} where

    infixr 9 _∘ₕ_ _∘ˡ_ _∘ʳ_

    _∘ₕ_ : {F G : BraidedMonoidalFunctor C D}
           {H I : BraidedMonoidalFunctor D E} →
           H ⇛ I → F ⇛ G → (H ∘Fˡ F) ⇛ (I ∘Fˡ G)
    α ∘ₕ β = ⌈ ⌊ α ⌋ U.∘ₕ ⌊ β ⌋ ⌉

    _∘ˡ_ : {F G : BraidedMonoidalFunctor C D}
           (H : BraidedMonoidalFunctor D E) → F ⇛ G → (H ∘Fˡ F) ⇛ (H ∘Fˡ G)
    H ∘ˡ α = id {F = H} ∘ₕ α

    _∘ʳ_ : {G H : BraidedMonoidalFunctor D E} →
           G ⇛ H → (F : BraidedMonoidalFunctor C D) → (G ∘Fˡ F) ⇛ (H ∘Fˡ F)
    α ∘ʳ F = α ∘ₕ id {F = F}

module Strong where
  open BMF.Strong using (BraidedMonoidalFunctor)
  open MNT.Strong using (IsMonoidalNaturalTransformation)
  open BraidedMonoidalFunctor using () renaming
    ( F                         to UF
    ; monoidalFunctor           to MF
    ; laxBraidedMonoidalFunctor to laxBMF
    )

  module _ {o ℓ e o′ ℓ′ e′}
           {C : BraidedMonoidalCategory o ℓ e}
           {D : BraidedMonoidalCategory o′ ℓ′ e′} where

    -- Monoidal natural transformations between braided strong
    -- monoidal functors.

    record BraidedMonoidalNaturalTransformation
           (F G : BraidedMonoidalFunctor C D) : Set (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) where

      field
        U          : NaturalTransformation (UF F) (UF G)
        isMonoidal : IsMonoidalNaturalTransformation (MF F) (MF G) U

      laxBNT : Lax.BraidedMonoidalNaturalTransformation (laxBMF F) (laxBMF G)
      laxBNT = record { U = U ; isMonoidal = isMonoidal }
      open Lax.BraidedMonoidalNaturalTransformation laxBNT public
        hiding (U; isMonoidal)

  -- To shorten some definitions

  private
    _⇛_ = BraidedMonoidalNaturalTransformation
    module U = MNT.Strong

  module _ {o ℓ e o′ ℓ′ e′}
           {C : BraidedMonoidalCategory o ℓ e}
           {D : BraidedMonoidalCategory o′ ℓ′ e′} where

    -- Conversions

    ⌊_⌋ : {F G : BraidedMonoidalFunctor C D} →
          F ⇛ G → U.MonoidalNaturalTransformation (MF F) (MF G)
    ⌊ α ⌋ = record { U = U ; isMonoidal = isMonoidal }
      where open BraidedMonoidalNaturalTransformation α

    ⌈_⌉ : {F G : BraidedMonoidalFunctor C D} →
          U.MonoidalNaturalTransformation (MF F) (MF G) → F ⇛ G
    ⌈ α ⌉ = record { U = U ; isMonoidal = isMonoidal }
      where open U.MonoidalNaturalTransformation α

    -- Identity and compositions

    infixr 9 _∘ᵥ_

    id : {F : BraidedMonoidalFunctor C D} → F ⇛ F
    id = ⌈ U.id ⌉

    _∘ᵥ_ : {F G H : BraidedMonoidalFunctor C D} → G ⇛ H → F ⇛ G → F ⇛ H
    α ∘ᵥ β   = ⌈ ⌊ α ⌋ U.∘ᵥ ⌊ β ⌋ ⌉

  module _ {o ℓ e o′ ℓ′ e′ o″ ℓ″ e″}
           {C : BraidedMonoidalCategory o ℓ e}
           {D : BraidedMonoidalCategory o′ ℓ′ e′}
           {E : BraidedMonoidalCategory o″ ℓ″ e″} where

    infixr 9 _∘ₕ_ _∘ˡ_ _∘ʳ_

    _∘ₕ_ : {F G : BraidedMonoidalFunctor C D}
           {H I : BraidedMonoidalFunctor D E} →
           H ⇛ I → F ⇛ G → (H ∘Fˢ F) ⇛ (I ∘Fˢ G)
    -- NOTE: this definition is clearly equivalent to
    --
    --   α ∘ₕ β = ⌈ ⌊ α ⌋ U.∘ₕ ⌊ β ⌋ ⌉
    --
    -- but the latter takes an unreasonably long time to typecheck,
    -- while the unfolded version typechecks almost immediately.
    α ∘ₕ β = record
      { U               = C.U
      ; isMonoidal      = record
        { ε-compat      = C.ε-compat
        ; ⊗-homo-compat = C.⊗-homo-compat
        }
      }
      where module C = U.MonoidalNaturalTransformation (⌊ α ⌋ U.∘ₕ ⌊ β ⌋)

    _∘ˡ_ : {F G : BraidedMonoidalFunctor C D}
           (H : BraidedMonoidalFunctor D E) → F ⇛ G → (H ∘Fˢ F) ⇛ (H ∘Fˢ G)
    H ∘ˡ α = id {F = H} ∘ₕ α

    _∘ʳ_ : {G H : BraidedMonoidalFunctor D E} →
           G ⇛ H → (F : BraidedMonoidalFunctor C D) → (G ∘Fˢ F) ⇛ (H ∘Fˢ F)
    α ∘ʳ F = α ∘ₕ id {F = F}
