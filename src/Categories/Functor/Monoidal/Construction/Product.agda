{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Monoidal.Construction.Product where

-- The functors associated with the product A × B of
-- (braided/symmetric) monoidal categories A and B are again
-- (braided/symmetric) monoidal.

open import Level using (Level)
open import Data.Product using (_,_; <_,_>)

open import Categories.Category using (Category)
open import Categories.Category.Product
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Braided using (Braided)
open import Categories.Category.Monoidal.Construction.Product
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Functor.Monoidal
import Categories.Category.Monoidal.Utilities as ⊗-Util
import Categories.Functor.Monoidal.Braided as BMF
import Categories.Functor.Monoidal.Symmetric as SMF
import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning as MorphismReasoning
import Categories.Morphism.Properties as MorphismProperties
open import Categories.NaturalTransformation using (ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)

private

  variable
    o ℓ e o₁ ℓ₁ e₁ o′₁ ℓ′₁ e′₁ o₂ ℓ₂ e₂ o′₂ ℓ′₂ e′₂ : Level

  module WithShorthands (C : MonoidalCategory o ℓ e) where
    open MonoidalCategory C public
    open ⊗-Util monoidal using (module Shorthands)
    open Shorthands public

module MC {D₁ : MonoidalCategory o₁ ℓ₁ e₁}
          {D₂ : MonoidalCategory o₂ ℓ₂ e₂} where

  open MonoidalCategory using (U)
  private D₁×D₂ = Product-MonoidalCategory D₁ D₂

  -- Pairing for monoidal categories is a monoidal functor

  module ※ {C : MonoidalCategory o ℓ e} where

    module _ {F : Functor (U C) (U D₁)} {G : Functor (U C) (U D₂)} where

      ※-IsMonoidalFunctor : IsMonoidalFunctor C D₁ F →
                            IsMonoidalFunctor C D₂ G →
                            IsMonoidalFunctor C D₁×D₂ (F ※ G)
      ※-IsMonoidalFunctor FM GM = record
        { ε         = FM.ε , GM.ε
        ; ⊗-homo    = ntHelper record
          { η       = λ XY → FM.⊗-homo.η XY , GM.⊗-homo.η XY
          ; commute = λ fg → FM.⊗-homo.commute fg , GM.⊗-homo.commute fg
          }
        ; associativity = FM.associativity , GM.associativity
        ; unitaryˡ      = FM.unitaryˡ , GM.unitaryˡ
        ; unitaryʳ      = FM.unitaryʳ , GM.unitaryʳ
        }
        where
          module FM = IsMonoidalFunctor FM
          module GM = IsMonoidalFunctor GM

      ※-IsStrongMonoidalFunctor : IsStrongMonoidalFunctor C D₁ F →
                                  IsStrongMonoidalFunctor C D₂ G →
                                  IsStrongMonoidalFunctor C D₁×D₂ (F ※ G)
      ※-IsStrongMonoidalFunctor FM GM = record
        { ε         = record
          { from    = FM.ε.from , GM.ε.from
          ; to      = FM.ε.to   , GM.ε.to
          ; iso     = record
            { isoˡ  = FM.ε.isoˡ , GM.ε.isoˡ
            ; isoʳ  = FM.ε.isoʳ , GM.ε.isoʳ
            }
          }
        ; ⊗-homo    = niHelper record
          { η       = < FM.⊗-homo.⇒.η , GM.⊗-homo.⇒.η >
          ; η⁻¹     = < FM.⊗-homo.⇐.η , GM.⊗-homo.⇐.η >
          ; commute = < FM.⊗-homo.⇒.commute , GM.⊗-homo.⇒.commute >
          ; iso     = λ XY → record
            { isoˡ  = FM.⊗-homo.iso.isoˡ XY , GM.⊗-homo.iso.isoˡ XY
            ; isoʳ  = FM.⊗-homo.iso.isoʳ XY , GM.⊗-homo.iso.isoʳ XY
            }
          }
        ; associativity = FM.associativity , GM.associativity
        ; unitaryˡ      = FM.unitaryˡ , GM.unitaryˡ
        ; unitaryʳ      = FM.unitaryʳ , GM.unitaryʳ
        }
        where
          module FM = IsStrongMonoidalFunctor FM
          module GM = IsStrongMonoidalFunctor GM

    ※-MonoidalFunctor : MonoidalFunctor C D₁ → MonoidalFunctor C D₂ →
                        MonoidalFunctor C D₁×D₂
    ※-MonoidalFunctor FM GM = record
      { isMonoidal = ※-IsMonoidalFunctor (isMonoidal FM) (isMonoidal GM) }
      where open MonoidalFunctor using (isMonoidal)

    ※-StrongMonoidalFunctor : StrongMonoidalFunctor C D₁ →
                              StrongMonoidalFunctor C D₂ →
                              StrongMonoidalFunctor C D₁×D₂
    ※-StrongMonoidalFunctor FM GM = record
      { isStrongMonoidal =
        ※-IsStrongMonoidalFunctor (isStrongMonoidal FM) (isStrongMonoidal GM)
      }
      where open StrongMonoidalFunctor using (isStrongMonoidal)

  -- The projections out of a product of monoidal categories are
  -- monoidal functors

  πˡ-IsStrongMonoidalFunctor : IsStrongMonoidalFunctor D₁×D₂ D₁ πˡ
  πˡ-IsStrongMonoidalFunctor = record
    { ε             = ≅.refl
    ; ⊗-homo        = niHelper record
      { η           = λ _ → id
      ; η⁻¹         = λ _ → id
      ; commute     = λ _ → id-comm-sym
      ; iso         = λ _ → id-iso
      }
    ; associativity = λ {(X₁ , X₂) (Y₁ , Y₂) (Z₁ , Z₂)} → associativity X₁ Y₁ Z₁ X₂ Y₂ Z₂
    ; unitaryˡ      = λ {(X₁ , X₂)} → unitaryˡ X₁ X₂
    ; unitaryʳ      = λ {(X₁ , X₂)} → unitaryʳ X₁ X₂
    }
    where
      module D₁ = WithShorthands D₁
      module D₂ = WithShorthands D₂
      open D₁.HomReasoning
      open Morphism (U D₁) using (module ≅)
      open MorphismReasoning (U D₁)
      open MorphismProperties (U D₁) using (id-iso)
      open D₁
      associativity
          : (X₁ Y₁ Z₁ : D₁.Obj)
            (X₂ Y₂ Z₂ : D₂.Obj)
          → α⇒ {X₁} {Y₁} {Z₁} ∘ id ∘ id ⊗₁ id ≈ id ∘ id ⊗₁ id ∘ α⇒
      associativity X₁ Y₁ Z₁ X₂ Y₂ Z₂ = begin
        α⇒ ∘ id ∘ id ⊗₁ id   ≈⟨ refl⟩∘⟨ elimʳ ⊗.identity ⟩
        α⇒ ∘ id              ≈⟨ id-comm ⟩
        id ∘ α⇒              ≈⟨ pushˡ (introʳ ⊗.identity) ⟩
        id ∘ id ⊗₁ id ∘ α⇒   ∎
      unitaryˡ
          : (X₁ : D₁.Obj) (X₂ : D₂.Obj)
          → λ⇒ ∘ id ∘ ⊗.F₁ (id , id) ≈ unitorˡ.from
      unitaryˡ X₁ X₂ = begin
        λ⇒ ∘ id ∘ id ⊗₁ id   ≈⟨ refl⟩∘⟨ elimʳ ⊗.identity ⟩
        λ⇒ ∘ id              ≈⟨ identityʳ ⟩
        λ⇒                   ∎
      unitaryʳ
          : (X₁ : D₁.Obj) (X₂ : D₂.Obj)
          → ρ⇒ ∘ id ∘ id ⊗₁ id ≈ unitorʳ.from
      unitaryʳ X₁ X₂ = begin
        ρ⇒ ∘ id ∘ id ⊗₁ id   ≈⟨ refl⟩∘⟨ elimʳ ⊗.identity ⟩
        ρ⇒ ∘ id              ≈⟨ identityʳ ⟩
        ρ⇒                   ∎

  πˡ-IsMonoidalFunctor : IsMonoidalFunctor D₁×D₂ D₁ πˡ
  πˡ-IsMonoidalFunctor =
    IsStrongMonoidalFunctor.isLaxMonoidal πˡ-IsStrongMonoidalFunctor

  πˡ-StrongMonoidalFunctor : StrongMonoidalFunctor D₁×D₂ D₁
  πˡ-StrongMonoidalFunctor = record
    { isStrongMonoidal = πˡ-IsStrongMonoidalFunctor }

  πˡ-MonoidalFunctor : MonoidalFunctor D₁×D₂ D₁
  πˡ-MonoidalFunctor =
    StrongMonoidalFunctor.monoidalFunctor πˡ-StrongMonoidalFunctor

  πʳ-IsStrongMonoidalFunctor : IsStrongMonoidalFunctor D₁×D₂ D₂ πʳ
  πʳ-IsStrongMonoidalFunctor = record
    { ε             = ≅.refl
    ; ⊗-homo        = niHelper record
      { η           = λ _ → id
      ; η⁻¹         = λ _ → id
      ; commute     = λ _ → id-comm-sym
      ; iso         = λ _ → id-iso
      }
    ; associativity = λ {(X₁ , X₂) (Y₁ , Y₂) (Z₁ , Z₂)} → associativity X₁ Y₁ Z₁ X₂ Y₂ Z₂
    ; unitaryˡ      = λ {(X₁ , X₂)} → unitaryˡ X₁ X₂
    ; unitaryʳ      = λ {(X₁ , X₂)} → unitaryʳ X₁ X₂
    }
    where
      module D₁ = WithShorthands D₁
      module D₂ = WithShorthands D₂
      open D₂
      open Morphism (U D₂) using (module ≅)
      open MorphismReasoning (U D₂)
      open MorphismProperties (U D₂) using (id-iso)
      open HomReasoning
      associativity
          : (X₁ Y₁ Z₁ : D₁.Obj)
            (X₂ Y₂ Z₂ : D₂.Obj)
          → α⇒ {X₂} {Y₂} {Z₂} ∘ id ∘ id ⊗₁ id ≈ id ∘ id ⊗₁ id ∘ α⇒
      associativity X₁ Y₁ Z₁ X₂ Y₂ Z₂ = begin
        α⇒ ∘ id ∘ id ⊗₁ id   ≈⟨ refl⟩∘⟨ elimʳ ⊗.identity ⟩
        α⇒ ∘ id              ≈⟨ id-comm ⟩
        id ∘ α⇒              ≈⟨ pushˡ (introʳ ⊗.identity) ⟩
        id ∘ id ⊗₁ id ∘ α⇒   ∎
      unitaryˡ
          : (X₁ : D₁.Obj)
          (X₂ : D₂.Obj)
          → λ⇒ ∘ id ∘ ⊗.F₁ (id , id) ≈ unitorˡ.from
      unitaryˡ X₁ X₂ = begin
        λ⇒ ∘ id ∘ id ⊗₁ id   ≈⟨ refl⟩∘⟨ elimʳ ⊗.identity ⟩
        λ⇒ ∘ id              ≈⟨ identityʳ ⟩
        λ⇒                   ∎
      unitaryʳ
          : (X₁ : D₁.Obj) (X₂ : D₂.Obj)
          → ρ⇒ ∘ id ∘ id ⊗₁ id ≈ unitorʳ.from
      unitaryʳ X₁ X₂ = begin
        ρ⇒ ∘ id ∘ id ⊗₁ id   ≈⟨ refl⟩∘⟨ elimʳ ⊗.identity ⟩
        ρ⇒ ∘ id              ≈⟨ identityʳ ⟩
        ρ⇒                   ∎

  πʳ-IsMonoidalFunctor : IsMonoidalFunctor D₁×D₂ D₂ πʳ
  πʳ-IsMonoidalFunctor =
    IsStrongMonoidalFunctor.isLaxMonoidal πʳ-IsStrongMonoidalFunctor

  πʳ-StrongMonoidalFunctor : StrongMonoidalFunctor D₁×D₂ D₂
  πʳ-StrongMonoidalFunctor = record
    { isStrongMonoidal = πʳ-IsStrongMonoidalFunctor }

  πʳ-MonoidalFunctor : MonoidalFunctor D₁×D₂ D₂
  πʳ-MonoidalFunctor =
    StrongMonoidalFunctor.monoidalFunctor πʳ-StrongMonoidalFunctor

  -- The cartesian product of two monoidal functors is again a
  -- monoidal functor

  module ⁂ {C₁ : MonoidalCategory o′₁ ℓ′₁ e′₁}
           {C₂ : MonoidalCategory o′₂ ℓ′₂ e′₂} where

    private C₁×C₂ = Product-MonoidalCategory C₁ C₂

    module _ {F : Functor (U C₁) (U D₁)} {G : Functor (U C₂) (U D₂)} where

      ⁂-IsMonoidalFunctor : IsMonoidalFunctor C₁ D₁ F →
                            IsMonoidalFunctor C₂ D₂ G →
                            IsMonoidalFunctor C₁×C₂ D₁×D₂ (F ⁂ G)
      ⁂-IsMonoidalFunctor FM GM = record
        { ε         = FM.ε , GM.ε
        ; ⊗-homo    = ntHelper record
          { η       = λ ((X₁ , X₂) , (Y₁ , Y₂)) →
                      FM.⊗-homo.η (X₁ , Y₁) , GM.⊗-homo.η (X₂ , Y₂)
          ; commute = λ ((f₁ , f₂) , (g₁ , g₂)) →
                      FM.⊗-homo.commute (f₁ , g₁) , GM.⊗-homo.commute (f₂ , g₂)
          }
        ; associativity = FM.associativity , GM.associativity
        ; unitaryˡ      = FM.unitaryˡ , GM.unitaryˡ
        ; unitaryʳ      = FM.unitaryʳ , GM.unitaryʳ
        }
        where
          module FM = IsMonoidalFunctor FM
          module GM = IsMonoidalFunctor GM

      ⁂-IsStrongMonoidalFunctor : IsStrongMonoidalFunctor C₁ D₁ F →
                                  IsStrongMonoidalFunctor C₂ D₂ G →
                                  IsStrongMonoidalFunctor C₁×C₂ D₁×D₂ (F ⁂ G)
      ⁂-IsStrongMonoidalFunctor FM GM = record
        { ε         = record
          { from    = FM.ε.from , GM.ε.from
          ; to      = FM.ε.to   , GM.ε.to
          ; iso     = record
            { isoˡ  = FM.ε.isoˡ , GM.ε.isoˡ
            ; isoʳ  = FM.ε.isoʳ , GM.ε.isoʳ
            }
          }
        ; ⊗-homo    = niHelper record
          { η       = λ ((X₁ , X₂) , (Y₁ , Y₂)) →
                      FM.⊗-homo.⇒.η (X₁ , Y₁) , GM.⊗-homo.⇒.η (X₂ , Y₂)
          ; η⁻¹     = λ ((X₁ , X₂) , (Y₁ , Y₂)) →
                      FM.⊗-homo.⇐.η (X₁ , Y₁) , GM.⊗-homo.⇐.η (X₂ , Y₂)
          ; commute = λ ((f₁ , f₂) , (g₁ , g₂)) →
                      FM.⊗-homo.⇒.commute (f₁ , g₁) , GM.⊗-homo.⇒.commute (f₂ , g₂)
          ; iso     = λ ((X₁ , X₂) , (Y₁ , Y₂)) → record
            { isoˡ  = FM.⊗-homo.iso.isoˡ (X₁ , Y₁) , GM.⊗-homo.iso.isoˡ (X₂ , Y₂)
            ; isoʳ  = FM.⊗-homo.iso.isoʳ (X₁ , Y₁) , GM.⊗-homo.iso.isoʳ (X₂ , Y₂)
            }
          }
        ; associativity = FM.associativity , GM.associativity
        ; unitaryˡ      = FM.unitaryˡ , GM.unitaryˡ
        ; unitaryʳ      = FM.unitaryʳ , GM.unitaryʳ
        }
        where
          module FM = IsStrongMonoidalFunctor FM
          module GM = IsStrongMonoidalFunctor GM

    ⁂-MonoidalFunctor : MonoidalFunctor C₁ D₁ → MonoidalFunctor C₂ D₂ →
                        MonoidalFunctor C₁×C₂ D₁×D₂
    ⁂-MonoidalFunctor FM GM = record
      { isMonoidal = ⁂-IsMonoidalFunctor (isMonoidal FM) (isMonoidal GM) }
      where open MonoidalFunctor using (isMonoidal)

    ⁂-StrongMonoidalFunctor : StrongMonoidalFunctor C₁ D₁ →
                              StrongMonoidalFunctor C₂ D₂ →
                              StrongMonoidalFunctor C₁×C₂ D₁×D₂
    ⁂-StrongMonoidalFunctor FM GM = record
      { isStrongMonoidal =
        ⁂-IsStrongMonoidalFunctor (isStrongMonoidal FM) (isStrongMonoidal GM)
      }
      where open StrongMonoidalFunctor using (isStrongMonoidal)

module BMC {D₁ : BraidedMonoidalCategory o₁ ℓ₁ e₁}
           {D₂ : BraidedMonoidalCategory o₂ ℓ₂ e₂} where

  private
    module D₁ = BraidedMonoidalCategory D₁ renaming (monoidalCategory to mc)
    module D₂ = BraidedMonoidalCategory D₂ renaming (monoidalCategory to mc)

  open MC {D₁ = D₁.mc} {D₂.mc} renaming (module ※ to MC-※; module ⁂ to MC-⁂)

  open BMF
  open BraidedMonoidalCategory using (U)
  private D₁×D₂ = Product-BraidedMonoidalCategory D₁ D₂

  -- Pairing for braided monoidal categories is a braided monoidal
  -- functor

  module ※ {C : BraidedMonoidalCategory o ℓ e} where

    private
      module C = BraidedMonoidalCategory C renaming (monoidalCategory to mc)

    open MC-※ {C = C.mc}

    module _ {F : Functor (U C) (U D₁)} {G : Functor (U C) (U D₂)} where

      ※-IsBraidedMonoidalFunctor : Lax.IsBraidedMonoidalFunctor C D₁ F →
                                   Lax.IsBraidedMonoidalFunctor C D₂ G →
                                   Lax.IsBraidedMonoidalFunctor C D₁×D₂ (F ※ G)
      ※-IsBraidedMonoidalFunctor FB GB = record
        { isMonoidal      = ※-IsMonoidalFunctor (isMonoidal FB) (isMonoidal GB)
        ; braiding-compat = (braiding-compat FB) , (braiding-compat GB)
        }
        where open Lax.IsBraidedMonoidalFunctor

      ※-IsStrongBraidedMonoidalFunctor :
        Strong.IsBraidedMonoidalFunctor C D₁ F →
        Strong.IsBraidedMonoidalFunctor C D₂ G →
        Strong.IsBraidedMonoidalFunctor C D₁×D₂ (F ※ G)
      ※-IsStrongBraidedMonoidalFunctor FB GB = record
        { isStrongMonoidal =
          ※-IsStrongMonoidalFunctor (isStrongMonoidal FB) (isStrongMonoidal GB)
        ; braiding-compat  = (braiding-compat FB) , (braiding-compat GB)
        }
        where open Strong.IsBraidedMonoidalFunctor

    ※-BraidedMonoidalFunctor : Lax.BraidedMonoidalFunctor C D₁ →
                               Lax.BraidedMonoidalFunctor C D₂ →
                               Lax.BraidedMonoidalFunctor C D₁×D₂
    ※-BraidedMonoidalFunctor FB GB = record
      { isBraidedMonoidal =
        ※-IsBraidedMonoidalFunctor (isBraidedMonoidal FB) (isBraidedMonoidal GB)
      }
      where open Lax.BraidedMonoidalFunctor

    ※-StrongBraidedMonoidalFunctor : Strong.BraidedMonoidalFunctor C D₁ →
                                     Strong.BraidedMonoidalFunctor C D₂ →
                                     Strong.BraidedMonoidalFunctor C D₁×D₂
    ※-StrongBraidedMonoidalFunctor FB GB = record
      { isBraidedMonoidal =
        ※-IsStrongBraidedMonoidalFunctor (isBraidedMonoidal FB)
                                         (isBraidedMonoidal GB)
      }
      where open Strong.BraidedMonoidalFunctor

  -- The projections out of a product of braided monoidal categories are
  -- braided monoidal functors

  πˡ-IsStrongBraidedMonoidalFunctor : Strong.IsBraidedMonoidalFunctor D₁×D₂ D₁ πˡ
  πˡ-IsStrongBraidedMonoidalFunctor = record
    { isStrongMonoidal = πˡ-IsStrongMonoidalFunctor
    ; braiding-compat  = MorphismReasoning.id-comm  (U D₁)
    }

  πˡ-IsBraidedMonoidalFunctor : Lax.IsBraidedMonoidalFunctor D₁×D₂ D₁ πˡ
  πˡ-IsBraidedMonoidalFunctor =
    Strong.IsBraidedMonoidalFunctor.isLaxBraidedMonoidal
      πˡ-IsStrongBraidedMonoidalFunctor

  πˡ-StrongBraidedMonoidalFunctor : Strong.BraidedMonoidalFunctor D₁×D₂ D₁
  πˡ-StrongBraidedMonoidalFunctor = record
    { isBraidedMonoidal = πˡ-IsStrongBraidedMonoidalFunctor }

  πˡ-BraidedMonoidalFunctor : Lax.BraidedMonoidalFunctor D₁×D₂ D₁
  πˡ-BraidedMonoidalFunctor =
    Strong.BraidedMonoidalFunctor.laxBraidedMonoidalFunctor
      πˡ-StrongBraidedMonoidalFunctor

  πʳ-IsStrongBraidedMonoidalFunctor : Strong.IsBraidedMonoidalFunctor D₁×D₂ D₂ πʳ
  πʳ-IsStrongBraidedMonoidalFunctor = record
    { isStrongMonoidal = πʳ-IsStrongMonoidalFunctor
    ; braiding-compat  = MorphismReasoning.id-comm  (U D₂)
    }

  πʳ-IsBraidedMonoidalFunctor : Lax.IsBraidedMonoidalFunctor D₁×D₂ D₂ πʳ
  πʳ-IsBraidedMonoidalFunctor =
    Strong.IsBraidedMonoidalFunctor.isLaxBraidedMonoidal
      πʳ-IsStrongBraidedMonoidalFunctor

  πʳ-StrongBraidedMonoidalFunctor : Strong.BraidedMonoidalFunctor D₁×D₂ D₂
  πʳ-StrongBraidedMonoidalFunctor = record
    { isBraidedMonoidal = πʳ-IsStrongBraidedMonoidalFunctor }

  πʳ-BraidedMonoidalFunctor : Lax.BraidedMonoidalFunctor D₁×D₂ D₂
  πʳ-BraidedMonoidalFunctor =
    Strong.BraidedMonoidalFunctor.laxBraidedMonoidalFunctor
      πʳ-StrongBraidedMonoidalFunctor


  -- The cartesian product of two braided monoidal functors is again a
  -- braided monoidal functor

  module ⁂ {C₁ : BraidedMonoidalCategory o′₁ ℓ′₁ e′₁}
           {C₂ : BraidedMonoidalCategory o′₂ ℓ′₂ e′₂} where

    private
      module C₁ = BraidedMonoidalCategory C₁ renaming (monoidalCategory to mc)
      module C₂ = BraidedMonoidalCategory C₂ renaming (monoidalCategory to mc)

    open MC-⁂ {C₁ = C₁.mc} {C₂.mc}

    private C₁×C₂ = Product-BraidedMonoidalCategory C₁ C₂

    module _ {F : Functor (U C₁) (U D₁)} {G : Functor (U C₂) (U D₂)} where

      ⁂-IsBraidedMonoidalFunctor : Lax.IsBraidedMonoidalFunctor C₁ D₁ F →
                                   Lax.IsBraidedMonoidalFunctor C₂ D₂ G →
                                   Lax.IsBraidedMonoidalFunctor C₁×C₂ D₁×D₂ (F ⁂ G)
      ⁂-IsBraidedMonoidalFunctor FB GB = record
        { isMonoidal      = ⁂-IsMonoidalFunctor (isMonoidal FB) (isMonoidal GB)
        ; braiding-compat = braiding-compat FB , braiding-compat GB
        }
        where open Lax.IsBraidedMonoidalFunctor

      ⁂-IsStrongBraidedMonoidalFunctor :
        Strong.IsBraidedMonoidalFunctor C₁ D₁ F →
        Strong.IsBraidedMonoidalFunctor C₂ D₂ G →
        Strong.IsBraidedMonoidalFunctor C₁×C₂ D₁×D₂ (F ⁂ G)
      ⁂-IsStrongBraidedMonoidalFunctor FB GB = record
        { isStrongMonoidal =
          ⁂-IsStrongMonoidalFunctor (isStrongMonoidal FB) (isStrongMonoidal GB)
        ; braiding-compat  = braiding-compat FB , braiding-compat GB
        }
        where open Strong.IsBraidedMonoidalFunctor

    ⁂-BraidedMonoidalFunctor : Lax.BraidedMonoidalFunctor C₁ D₁ →
                               Lax.BraidedMonoidalFunctor C₂ D₂ →
                               Lax.BraidedMonoidalFunctor C₁×C₂ D₁×D₂
    ⁂-BraidedMonoidalFunctor FB GB = record
      { isBraidedMonoidal =
        ⁂-IsBraidedMonoidalFunctor (isBraidedMonoidal FB) (isBraidedMonoidal GB)
      }
      where open Lax.BraidedMonoidalFunctor

    ⁂-StrongBraidedMonoidalFunctor : Strong.BraidedMonoidalFunctor C₁ D₁ →
                                     Strong.BraidedMonoidalFunctor C₂ D₂ →
                                     Strong.BraidedMonoidalFunctor C₁×C₂ D₁×D₂
    ⁂-StrongBraidedMonoidalFunctor FB GB = record
      { isBraidedMonoidal =
        ⁂-IsStrongBraidedMonoidalFunctor (isBraidedMonoidal FB)
                                         (isBraidedMonoidal GB)
      }
      where open Strong.BraidedMonoidalFunctor

module SMC {D₁ : SymmetricMonoidalCategory o₁ ℓ₁ e₁}
           {D₂ : SymmetricMonoidalCategory o₂ ℓ₂ e₂} where

  private
    module D₁ = SymmetricMonoidalCategory D₁ renaming (braidedMonoidalCategory to bmc)
    module D₂ = SymmetricMonoidalCategory D₂ renaming (braidedMonoidalCategory to bmc)

  open BMC {D₁ = D₁.bmc} {D₂.bmc} renaming (module ※ to BMC-※; module ⁂ to BMC-⁂)

  open SMF
  private D₁×D₂ = Product-SymmetricMonoidalCategory D₁ D₂

  -- Pairing for symmetric monoidal categories is a symmetric monoidal
  -- functor

  module ※ {C : SymmetricMonoidalCategory o ℓ e} where

    private
      module C = SymmetricMonoidalCategory C renaming (braidedMonoidalCategory to bmc)

    open BMC-※ {C = C.bmc}

    ※-SymmetricMonoidalFunctor : Lax.SymmetricMonoidalFunctor C D₁ →
                                 Lax.SymmetricMonoidalFunctor C D₂ →
                                 Lax.SymmetricMonoidalFunctor C D₁×D₂
    ※-SymmetricMonoidalFunctor FB GB = record
      { isBraidedMonoidal =
        ※-IsBraidedMonoidalFunctor (isBraidedMonoidal FB) (isBraidedMonoidal GB)
      }
      where open Lax.SymmetricMonoidalFunctor

    ※-StrongSymmetricMonoidalFunctor : Strong.SymmetricMonoidalFunctor C D₁ →
                                       Strong.SymmetricMonoidalFunctor C D₂ →
                                       Strong.SymmetricMonoidalFunctor C D₁×D₂
    ※-StrongSymmetricMonoidalFunctor FB GB = record
      { isBraidedMonoidal =
        ※-IsStrongBraidedMonoidalFunctor (isBraidedMonoidal FB)
                                         (isBraidedMonoidal GB)
      }
      where open Strong.SymmetricMonoidalFunctor

  -- The projections out of a product of symmetric monoidal categories are
  -- symmetric monoidal functors

  πˡ-StrongSymmetricMonoidalFunctor : Strong.SymmetricMonoidalFunctor D₁×D₂ D₁
  πˡ-StrongSymmetricMonoidalFunctor = record
    { isBraidedMonoidal = πˡ-IsStrongBraidedMonoidalFunctor }

  πˡ-SymmetricMonoidalFunctor : Lax.SymmetricMonoidalFunctor D₁×D₂ D₁
  πˡ-SymmetricMonoidalFunctor =
    Strong.SymmetricMonoidalFunctor.laxSymmetricMonoidalFunctor
      πˡ-StrongSymmetricMonoidalFunctor

  πʳ-StrongSymmetricMonoidalFunctor : Strong.SymmetricMonoidalFunctor D₁×D₂ D₂
  πʳ-StrongSymmetricMonoidalFunctor = record
    { isBraidedMonoidal = πʳ-IsStrongBraidedMonoidalFunctor }

  πʳ-SymmetricMonoidalFunctor : Lax.SymmetricMonoidalFunctor D₁×D₂ D₂
  πʳ-SymmetricMonoidalFunctor =
    Strong.SymmetricMonoidalFunctor.laxSymmetricMonoidalFunctor
      πʳ-StrongSymmetricMonoidalFunctor

  -- The cartesian product of two symmetric monoidal functors is again a
  -- symmetric monoidal functor

  module ⁂ {C₁ : SymmetricMonoidalCategory o′₁ ℓ′₁ e′₁}
           {C₂ : SymmetricMonoidalCategory o′₂ ℓ′₂ e′₂} where

    private
      module C₁ = SymmetricMonoidalCategory C₁ renaming (braidedMonoidalCategory to bmc)
      module C₂ = SymmetricMonoidalCategory C₂ renaming (braidedMonoidalCategory to bmc)

    open BMC-⁂ {C₁ = C₁.bmc} {C₂.bmc}

    private C₁×C₂ = Product-SymmetricMonoidalCategory C₁ C₂

    ⁂-SymmetricMonoidalFunctor : Lax.SymmetricMonoidalFunctor C₁ D₁ →
                                 Lax.SymmetricMonoidalFunctor C₂ D₂ →
                                 Lax.SymmetricMonoidalFunctor C₁×C₂ D₁×D₂
    ⁂-SymmetricMonoidalFunctor FB GB = record
      { isBraidedMonoidal =
        ⁂-IsBraidedMonoidalFunctor (isBraidedMonoidal FB) (isBraidedMonoidal GB)
      }
      where open Lax.SymmetricMonoidalFunctor

    ⁂-StrongSymmetricMonoidalFunctor : Strong.SymmetricMonoidalFunctor C₁ D₁ →
                                       Strong.SymmetricMonoidalFunctor C₂ D₂ →
                                       Strong.SymmetricMonoidalFunctor C₁×C₂ D₁×D₂
    ⁂-StrongSymmetricMonoidalFunctor FB GB = record
      { isBraidedMonoidal =
        ⁂-IsStrongBraidedMonoidalFunctor (isBraidedMonoidal FB)
                                         (isBraidedMonoidal GB)
      }
      where open Strong.SymmetricMonoidalFunctor

open MC public hiding (module ※; module ⁂)
open BMC public hiding (module ※; module ⁂)
open SMC public hiding (module ※; module ⁂)
open MC.※ public
open BMC.※ public
open SMC.※ public
open MC.⁂ public
open BMC.⁂ public
open SMC.⁂ public
