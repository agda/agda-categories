{-# OPTIONS --without-K --safe #-}

module Categories.Category.Monoidal.Construction.Product where

-- The product A × B of (braided/symmetric) monoidal categories
-- A and B is again (braided/symmetric) monoidal.

open import Level using (_⊔_)
open import Data.Product using (_,_; dmap; zip; curry′; uncurry′)

open import Categories.Category using (Category)
open import Categories.Category.Product using (Product)
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Braided using (Braided)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)

open Category using (Obj)

module _ {o o′ ℓ ℓ′ e e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′}
         (M : Monoidal C) (N : Monoidal D) where

  private
    module M  = Monoidal M
    module N  = Monoidal N
    module ⊗₁ = Functor M.⊗
    module ⊗₂ = Functor N.⊗

  ⊗ : Bifunctor (Product C D) (Product C D) (Product C D)
  ⊗ = record
    { F₀           = uncurry′ (zip (curry′ ⊗₁.₀) (curry′ ⊗₂.₀))
    ; F₁           = uncurry′ (zip (curry′ ⊗₁.₁) (curry′ ⊗₂.₁))
    ; identity     = ⊗₁.identity , ⊗₂.identity
    ; homomorphism = ⊗₁.homomorphism , ⊗₂.homomorphism
    ; F-resp-≈     = uncurry′ (zip (curry′ ⊗₁.F-resp-≈) (curry′ ⊗₂.F-resp-≈))
    }

  unit : Obj (Product C D)
  unit = M.unit , N.unit

  Product-Monoidal : Monoidal (Product C D)
  Product-Monoidal = record
    { ⊗        = ⊗
    ; unit     = unit
    ; unitorˡ  = record
      { from   = M.unitorˡ.from , N.unitorˡ.from
      ; to     = M.unitorˡ.to   , N.unitorˡ.to
      ; iso    = record
        { isoˡ = M.unitorˡ.isoˡ , N.unitorˡ.isoˡ
        ; isoʳ = M.unitorˡ.isoʳ , N.unitorˡ.isoʳ
        }
      }
    ; unitorʳ  = record
      { from   = M.unitorʳ.from , N.unitorʳ.from
      ; to     = M.unitorʳ.to   , N.unitorʳ.to
      ; iso    = record
        { isoˡ = M.unitorʳ.isoˡ , N.unitorʳ.isoˡ
        ; isoʳ = M.unitorʳ.isoʳ , N.unitorʳ.isoʳ
        }
      }
    ; associator = record
      { from     = M.associator.from , N.associator.from
      ; to       = M.associator.to   , N.associator.to
      ; iso      = record
        { isoˡ   = M.associator.isoˡ , N.associator.isoˡ
        ; isoʳ   = M.associator.isoʳ , N.associator.isoʳ
        }
      }
    ; unitorˡ-commute-from = M.unitorˡ-commute-from , N.unitorˡ-commute-from
    ; unitorˡ-commute-to   = M.unitorˡ-commute-to   , N.unitorˡ-commute-to
    ; unitorʳ-commute-from = M.unitorʳ-commute-from , N.unitorʳ-commute-from
    ; unitorʳ-commute-to   = M.unitorʳ-commute-to   , N.unitorʳ-commute-to
    ; assoc-commute-from   = M.assoc-commute-from   , N.assoc-commute-from
    ; assoc-commute-to     = M.assoc-commute-to     , N.assoc-commute-to
    ; triangle             = M.triangle             , N.triangle
    ; pentagon             = M.pentagon             , N.pentagon
    }

module _ {o o′ ℓ ℓ′ e e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′}
         {M : Monoidal C} {N : Monoidal D} where

  Product-Braided : Braided M → Braided N → Braided (Product-Monoidal M N)
  Product-Braided BM BN = record
    { braiding = niHelper (record
      { η       = λ{ ((W , X) , (Y , Z)) →
        BM.braiding.⇒.η (W , Y) , BN.braiding.⇒.η (X , Z) }
      ; η⁻¹     = λ{ ((W , X) , (Y , Z)) →
        BM.braiding.⇐.η (W , Y) , BN.braiding.⇐.η (X , Z) }
      ; commute = λ{ ((f , g) , (h , i)) →
        BM.braiding.⇒.commute (f , h) , BN.braiding.⇒.commute (g , i) }
      ; iso     = λ{ ((W , X) , (Y , Z)) → record
        { isoˡ = BM.braiding.iso.isoˡ (W , Y) , BN.braiding.iso.isoˡ (X , Z)
        ; isoʳ = BM.braiding.iso.isoʳ (W , Y) , BN.braiding.iso.isoʳ (X , Z)
        } }
      })
    ; hexagon₁ = BM.hexagon₁ , BN.hexagon₁
    ; hexagon₂ = BM.hexagon₂ , BN.hexagon₂
    }
    where
      module BM = Braided BM
      module BN = Braided BN

  Product-Symmetric : Symmetric M → Symmetric N → Symmetric (Product-Monoidal M N)
  Product-Symmetric SM SN = record
    { braided     = Product-Braided SM.braided SN.braided
    ; commutative = SM.commutative , SN.commutative
    }
    where
      module SM = Symmetric SM
      module SN = Symmetric SN

Product-MonoidalCategory : ∀ {o o′ ℓ ℓ′ e e′} →
                           MonoidalCategory o ℓ e → MonoidalCategory o′ ℓ′ e′ →
                           MonoidalCategory (o ⊔ o′) (ℓ ⊔ ℓ′) (e ⊔ e′)
Product-MonoidalCategory C D = record
  { U        = Product (C.U) (D.U)
  ; monoidal = Product-Monoidal (C.monoidal) (D.monoidal)
  }
  where
    module C = MonoidalCategory C
    module D = MonoidalCategory D

Product-BraidedMonoidalCategory : ∀ {o o′ ℓ ℓ′ e e′} →
  BraidedMonoidalCategory o ℓ e → BraidedMonoidalCategory o′ ℓ′ e′ →
  BraidedMonoidalCategory (o ⊔ o′) (ℓ ⊔ ℓ′) (e ⊔ e′)
Product-BraidedMonoidalCategory C D = record
  { U        = Product (C.U) (D.U)
  ; monoidal = Product-Monoidal (C.monoidal) (D.monoidal)
  ; braided  = Product-Braided (C.braided) (D.braided)
  }
  where
    module C = BraidedMonoidalCategory C
    module D = BraidedMonoidalCategory D

Product-SymmetricMonoidalCategory : ∀ {o o′ ℓ ℓ′ e e′} →
  SymmetricMonoidalCategory o ℓ e → SymmetricMonoidalCategory o′ ℓ′ e′ →
  SymmetricMonoidalCategory (o ⊔ o′) (ℓ ⊔ ℓ′) (e ⊔ e′)
Product-SymmetricMonoidalCategory C D = record
  { U         = Product (C.U) (D.U)
  ; monoidal  = Product-Monoidal (C.monoidal) (D.monoidal)
  ; symmetric = Product-Symmetric (C.symmetric) (D.symmetric)
  }
  where
    module C = SymmetricMonoidalCategory C
    module D = SymmetricMonoidalCategory D
