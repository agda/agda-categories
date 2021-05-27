{-# OPTIONS --without-K --safe #-}

-- Monoidal natural transformations between lax and strong symmetric
-- monoidal functors.
--
-- NOTE. Symmetric monoidal natural transformations are really just
-- monoidal natural transformations that happen to go between
-- symmetric monoidal functors.  No additional conditions are
-- necessary.  Nevertheless, the definitions in this module are useful
-- when one is working in a symmetric monoidal setting.  They also
-- help Agda's type checker by bundling the (symmetric monoidal)
-- categories and functors involved.
--
-- See
--  * John Baez, Some definitions everyone should know,
--    https://math.ucr.edu/home/baez/qg-fall2004/definitions.pdf
--  * https://ncatlab.org/nlab/show/monoidal+natural+transformation

module Categories.NaturalTransformation.Monoidal.Symmetric where

open import Level

open import Categories.Category.Monoidal using (SymmetricMonoidalCategory)
import Categories.Functor.Monoidal.Symmetric as BMF
open import Categories.Functor.Monoidal.Properties using ()
  renaming (∘-SymmetricMonoidal to _∘Fˡ_; ∘-StrongSymmetricMonoidal to _∘Fˢ_)
open import Categories.NaturalTransformation as NT using (NaturalTransformation)
import Categories.NaturalTransformation.Monoidal as MNT

module Lax where
  open BMF.Lax using (SymmetricMonoidalFunctor)
  open MNT.Lax using (IsMonoidalNaturalTransformation)
  open SymmetricMonoidalFunctor using ()
    renaming (F to UF; monoidalFunctor to MF)

  module _ {o ℓ e o′ ℓ′ e′}
           {C : SymmetricMonoidalCategory o ℓ e}
           {D : SymmetricMonoidalCategory o′ ℓ′ e′} where

    -- Monoidal natural transformations between symmetric monoidal functors.

    record SymmetricMonoidalNaturalTransformation
           (F G : SymmetricMonoidalFunctor C D) : Set (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) where

      field
        U          : NaturalTransformation (UF F) (UF G)
        isMonoidal : IsMonoidalNaturalTransformation (MF F) (MF G) U

      open NaturalTransformation           U          public
      open IsMonoidalNaturalTransformation isMonoidal public

  -- To shorten some definitions

  private
    _⇛_ = SymmetricMonoidalNaturalTransformation
    module U = MNT.Lax

  module _ {o ℓ e o′ ℓ′ e′}
           {C : SymmetricMonoidalCategory o ℓ e}
           {D : SymmetricMonoidalCategory o′ ℓ′ e′} where

    -- Conversions

    ⌊_⌋ : {F G : SymmetricMonoidalFunctor C D} →
          F ⇛ G → U.MonoidalNaturalTransformation (MF F) (MF G)
    ⌊ α ⌋ = record { U = U ; isMonoidal = isMonoidal }
      where open SymmetricMonoidalNaturalTransformation α

    ⌈_⌉ : {F G : SymmetricMonoidalFunctor C D} →
          U.MonoidalNaturalTransformation (MF F) (MF G) → F ⇛ G
    ⌈ α ⌉ = record { U = U ; isMonoidal = isMonoidal }
      where open U.MonoidalNaturalTransformation α

    -- Identity and compositions

    infixr 9 _∘ᵥ_

    id : {F : SymmetricMonoidalFunctor C D} → F ⇛ F
    id = ⌈ U.id ⌉

    _∘ᵥ_ : {F G H : SymmetricMonoidalFunctor C D} → G ⇛ H → F ⇛ G → F ⇛ H
    α ∘ᵥ β   = ⌈ ⌊ α ⌋ U.∘ᵥ ⌊ β ⌋ ⌉

  module _ {o ℓ e o′ ℓ′ e′ o″ ℓ″ e″}
           {C : SymmetricMonoidalCategory o ℓ e}
           {D : SymmetricMonoidalCategory o′ ℓ′ e′}
           {E : SymmetricMonoidalCategory o″ ℓ″ e″} where

    infixr 9 _∘ₕ_ _∘ˡ_ _∘ʳ_

    _∘ₕ_ : {F G : SymmetricMonoidalFunctor C D}
           {H I : SymmetricMonoidalFunctor D E} →
           H ⇛ I → F ⇛ G → (H ∘Fˡ F) ⇛ (I ∘Fˡ G)
    α ∘ₕ β = ⌈ ⌊ α ⌋ U.∘ₕ ⌊ β ⌋ ⌉

    _∘ˡ_ : {F G : SymmetricMonoidalFunctor C D}
           (H : SymmetricMonoidalFunctor D E) → F ⇛ G → (H ∘Fˡ F) ⇛ (H ∘Fˡ G)
    H ∘ˡ α = id {F = H} ∘ₕ α

    _∘ʳ_ : {G H : SymmetricMonoidalFunctor D E} →
           G ⇛ H → (F : SymmetricMonoidalFunctor C D) → (G ∘Fˡ F) ⇛ (H ∘Fˡ F)
    α ∘ʳ F = α ∘ₕ id {F = F}

module Strong where
  open BMF.Strong using (SymmetricMonoidalFunctor)
  open MNT.Strong using (IsMonoidalNaturalTransformation)
  open SymmetricMonoidalFunctor using () renaming
    ( F                         to UF
    ; monoidalFunctor           to MF
    ; laxSymmetricMonoidalFunctor to laxBMF
    )

  module _ {o ℓ e o′ ℓ′ e′}
           {C : SymmetricMonoidalCategory o ℓ e}
           {D : SymmetricMonoidalCategory o′ ℓ′ e′} where

    -- Monoidal natural transformations between symmetric strong
    -- monoidal functors.

    record SymmetricMonoidalNaturalTransformation
           (F G : SymmetricMonoidalFunctor C D) : Set (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) where

      field
        U          : NaturalTransformation (UF F) (UF G)
        isMonoidal : IsMonoidalNaturalTransformation (MF F) (MF G) U

      laxBNT : Lax.SymmetricMonoidalNaturalTransformation (laxBMF F) (laxBMF G)
      laxBNT = record { U = U ; isMonoidal = isMonoidal }
      open Lax.SymmetricMonoidalNaturalTransformation laxBNT public
        hiding (U; isMonoidal)

  -- To shorten some definitions

  private
    _⇛_ = SymmetricMonoidalNaturalTransformation
    module U = MNT.Strong

  module _ {o ℓ e o′ ℓ′ e′}
           {C : SymmetricMonoidalCategory o ℓ e}
           {D : SymmetricMonoidalCategory o′ ℓ′ e′} where

    -- Conversions

    ⌊_⌋ : {F G : SymmetricMonoidalFunctor C D} →
          F ⇛ G → U.MonoidalNaturalTransformation (MF F) (MF G)
    ⌊ α ⌋ = record { U = U ; isMonoidal = isMonoidal }
      where open SymmetricMonoidalNaturalTransformation α

    ⌈_⌉ : {F G : SymmetricMonoidalFunctor C D} →
          U.MonoidalNaturalTransformation (MF F) (MF G) → F ⇛ G
    ⌈ α ⌉ = record { U = U ; isMonoidal = isMonoidal }
      where open U.MonoidalNaturalTransformation α

    -- Identity and compositions

    infixr 9 _∘ᵥ_

    id : {F : SymmetricMonoidalFunctor C D} → F ⇛ F
    id = ⌈ U.id ⌉

    _∘ᵥ_ : {F G H : SymmetricMonoidalFunctor C D} → G ⇛ H → F ⇛ G → F ⇛ H
    α ∘ᵥ β   = ⌈ ⌊ α ⌋ U.∘ᵥ ⌊ β ⌋ ⌉

  module _ {o ℓ e o′ ℓ′ e′ o″ ℓ″ e″}
           {C : SymmetricMonoidalCategory o ℓ e}
           {D : SymmetricMonoidalCategory o′ ℓ′ e′}
           {E : SymmetricMonoidalCategory o″ ℓ″ e″} where

    infixr 9 _∘ₕ_ _∘ˡ_ _∘ʳ_

    _∘ₕ_ : {F G : SymmetricMonoidalFunctor C D}
           {H I : SymmetricMonoidalFunctor D E} →
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

    _∘ˡ_ : {F G : SymmetricMonoidalFunctor C D}
           (H : SymmetricMonoidalFunctor D E) → F ⇛ G → (H ∘Fˢ F) ⇛ (H ∘Fˢ G)
    H ∘ˡ α = id {F = H} ∘ₕ α

    _∘ʳ_ : {G H : SymmetricMonoidalFunctor D E} →
           G ⇛ H → (F : SymmetricMonoidalFunctor C D) → (G ∘Fˢ F) ⇛ (H ∘Fˢ F)
    α ∘ʳ F = α ∘ₕ id {F = F}
