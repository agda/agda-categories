{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Monoidal.Properties where

open import Level
open import Data.Product using (_,_)

open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Bundle
  using (MonoidalCategory; BraidedMonoidalCategory; SymmetricMonoidalCategory)
open import Categories.Category.Cartesian.Bundle using (CartesianCategory)
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Properties
open import Categories.Functor.Cartesian using (CartesianF)
open import Categories.Functor.Monoidal
  using (IsMonoidalFunctor; IsStrongMonoidalFunctor; StrongMonoidalFunctor;
    MonoidalFunctor)
open import Categories.Functor.Monoidal.Braided as Braided
open import Categories.Functor.Monoidal.Symmetric as Symmetric
open import Categories.NaturalTransformation

import Categories.Object.Terminal as ⊤
import Categories.Object.Product as P
import Categories.Morphism as M
import Categories.Morphism.Reasoning as MR

private
  variable
    o o′ o″ ℓ ℓ′ ℓ″ e e′ e″ : Level

-- The identity functor is monoidal

module _ (C : MonoidalCategory o ℓ e) where
  private
    module C = MonoidalCategory C
    open C.HomReasoning
    open M C.U
    open MR C.U

  idF-IsStrongMonoidal : IsStrongMonoidalFunctor C C idF
  idF-IsStrongMonoidal = record
    { ε             = ≅.refl
    ; ⊗-homo        = record
      { F⇒G = record
        { η           = λ _ → C.id
        ; commute     = λ _ → id-comm-sym
        ; sym-commute = λ _ → id-comm
        }
      ; F⇐G = record
        { η           = λ _ → C.id
        ; commute     = λ _ → id-comm-sym
        ; sym-commute = λ _ → id-comm
        }
      ; iso = λ _ → record
        { isoˡ = C.identity²
        ; isoʳ = C.identity²
        }
      }
    ; associativity = begin
      C.associator.from C.∘ C.id C.∘ Functor.F₁ C.⊗ (C.id , C.id) ≈⟨ refl⟩∘⟨ elimʳ C.⊗.identity ⟩
      C.associator.from C.∘ C.id                                  ≈⟨ id-comm ⟩
      C.id C.∘ C.associator.from                                  ≈⟨ refl⟩∘⟨ introˡ C.⊗.identity ⟩
      C.id C.∘ Functor.F₁ C.⊗ (C.id , C.id) C.∘ C.associator.from ∎
    ; unitaryˡ      = elimʳ (elimʳ C.⊗.identity)
    ; unitaryʳ      = elimʳ (elimʳ C.⊗.identity)
    }

  idF-IsMonoidal : IsMonoidalFunctor C C idF
  idF-IsMonoidal = IsStrongMonoidalFunctor.isMonoidal idF-IsStrongMonoidal

  idF-StrongMonoidal : StrongMonoidalFunctor C C
  idF-StrongMonoidal = record { isStrongMonoidal = idF-IsStrongMonoidal }

  idF-Monoidal : MonoidalFunctor C C
  idF-Monoidal = record { isMonoidal = idF-IsMonoidal }

-- The identity functor is braided monoidal

module _ (C : BraidedMonoidalCategory o ℓ e) where
  open Braided

  idF-IsStrongBraidedMonoidal : Strong.IsBraidedMonoidalFunctor C C idF
  idF-IsStrongBraidedMonoidal = record
    { isStrongMonoidal = idF-IsStrongMonoidal monoidalCategory
    ; braiding-compat  = MR.id-comm U
    }
    where open BraidedMonoidalCategory C

  idF-IsBraidedMonoidal : Lax.IsBraidedMonoidalFunctor C C idF
  idF-IsBraidedMonoidal =
    Strong.IsBraidedMonoidalFunctor.isLaxBraidedMonoidal idF-IsStrongBraidedMonoidal

  idF-StrongBraidedMonoidal : Strong.BraidedMonoidalFunctor C C
  idF-StrongBraidedMonoidal = record { isBraidedMonoidal = idF-IsStrongBraidedMonoidal }

  idF-BraidedMonoidal : Lax.BraidedMonoidalFunctor C C
  idF-BraidedMonoidal = record { isBraidedMonoidal = idF-IsBraidedMonoidal }

-- The identity functor is symmetric monoidal

module _ (C : SymmetricMonoidalCategory o ℓ e) where
  open Symmetric
  open SymmetricMonoidalCategory C using (braidedMonoidalCategory)

  idF-StrongSymmetricMonoidal : Strong.SymmetricMonoidalFunctor C C
  idF-StrongSymmetricMonoidal = record
    { isBraidedMonoidal = idF-IsStrongBraidedMonoidal braidedMonoidalCategory }

  idF-SymmetricMonoidal : Lax.SymmetricMonoidalFunctor C C
  idF-SymmetricMonoidal = record
    { isBraidedMonoidal = idF-IsBraidedMonoidal braidedMonoidalCategory }

-- Functor composition preserves monoidality

module _ (A : MonoidalCategory o ℓ e) (B : MonoidalCategory o′ ℓ′ e′) (C : MonoidalCategory o″ ℓ″ e″) where
  private
    module A = MonoidalCategory A
    module B = MonoidalCategory B
    module C = MonoidalCategory C
    open P C.U
    open M C.U
    open C.HomReasoning
    open MR C.U

  ∘-IsMonoidal : ∀ {F : Functor A.U B.U} {G : Functor B.U C.U} →
                    IsMonoidalFunctor B C G → IsMonoidalFunctor A B F →
                    IsMonoidalFunctor A C (G ∘F F)
  ∘-IsMonoidal {F} {G} CG CF = record
    { ε             = G.₁ CF.ε C.∘ CG.ε
    ; ⊗-homo        = ntHelper record
      { η       = λ { (X , Y) → G.₁ (CF.⊗-homo.η (X , Y)) C.∘ CG.⊗-homo.η (F.F₀ X , F.F₀ Y) }
      ; commute = λ { (f , g) → begin
        (G.₁ (CF.⊗-homo.η _) C.∘ CG.⊗-homo.η _) C.∘ (G.₁ (F.₁ f) C.⊗₁ G.₁ (F.₁ g)) ≈⟨ C.assoc ⟩
        G.₁ (CF.⊗-homo.η _) C.∘ CG.⊗-homo.η _ C.∘ (G.₁ (F.₁ f) C.⊗₁ G.₁ (F.₁ g))   ≈⟨ pushʳ (CG.⊗-homo.commute _) ⟩
        (G.₁ (CF.⊗-homo.η _) C.∘ G.₁ (F.₁ f B.⊗₁ F.₁ g)) C.∘ CG.⊗-homo.η _         ≈⟨ pushˡ ([ G ]-resp-square (CF.⊗-homo.commute _)) ⟩
        G.₁ (F.₁ (f A.⊗₁ g)) C.∘ G.₁ (CF.⊗-homo.η _) C.∘ CG.⊗-homo.η _             ∎ }
      }
    ; associativity = begin
      G.₁ (F.₁ A.associator.from) C.∘ (G.₁ (CF.⊗-homo.η _) C.∘ CG.⊗-homo.η _) C.∘ ((G.₁ (CF.⊗-homo.η _) C.∘ CG.⊗-homo.η _) C.⊗₁ C.id)
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (Functor.homomorphism (C.-⊗ _) ○ C.∘-resp-≈ˡ (C.⊗.F-resp-≈ (C.Equiv.refl , ⟺ G.identity))) ⟩
      G.₁ (F.₁ A.associator.from) C.∘ (G.₁ (CF.⊗-homo.η _) C.∘ CG.⊗-homo.η _) C.∘ (G.₁ (CF.⊗-homo.η _) C.⊗₁ G.₁ B.id) C.∘ (CG.⊗-homo.η _ C.⊗₁ C.id)
        ≈⟨ refl⟩∘⟨ center (CG.⊗-homo.commute _) ⟩
      G.₁ (F.₁ A.associator.from) C.∘ G.₁ (CF.⊗-homo.η _) C.∘ (G.₁ (CF.⊗-homo.η _ B.⊗₁ B.id) C.∘ CG.⊗-homo.η _) C.∘ (CG.⊗-homo.η _ C.⊗₁ C.id)
        ≈⟨ C.∘-resp-≈ʳ (center⁻¹ C.Equiv.refl C.Equiv.refl) ○ C.sym-assoc ⟩
      (G.₁ (F.₁ A.associator.from) C.∘ G.₁ (CF.⊗-homo.η _) C.∘ G.₁ (CF.⊗-homo.η _ B.⊗₁ B.id)) C.∘ CG.⊗-homo.η _ C.∘ (CG.⊗-homo.η _ C.⊗₁ C.id)
        ≈⟨ C.∘-resp-≈ʳ (⟺ G.homomorphism) ⟩∘⟨refl ⟩
      (G.₁ (F.₁ A.associator.from) C.∘ G.₁ (CF.⊗-homo.η _ B.∘ CF.⊗-homo.η _ B.⊗₁ B.id)) C.∘ CG.⊗-homo.η _ C.∘ (CG.⊗-homo.η _ C.⊗₁ C.id)
        ≈⟨ [ G ]-resp-square CF.associativity ⟩∘⟨refl ⟩
      (G.₁ (CF.⊗-homo.η _) C.∘ G.₁ ((B.id B.⊗₁ CF.⊗-homo.η _) B.∘ B.associator.from)) C.∘ CG.⊗-homo.η _ C.∘ (CG.⊗-homo.η _ C.⊗₁ C.id)
        ≈⟨ C.∘-resp-≈ʳ G.homomorphism ⟩∘⟨refl ⟩
      (G.₁ (CF.⊗-homo.η _) C.∘ G.₁ (B.id B.⊗₁ CF.⊗-homo.η _) C.∘ G.₁ B.associator.from) C.∘ CG.⊗-homo.η _ C.∘ (CG.⊗-homo.η _ C.⊗₁ C.id)
        ≈⟨ C.∘-resp-≈ˡ C.sym-assoc ○ C.assoc ⟩
      (G.₁ (CF.⊗-homo.η _) C.∘ G.₁ (B.id B.⊗₁ CF.⊗-homo.η _)) C.∘ G.₁ B.associator.from C.∘ CG.⊗-homo.η _ C.∘ (CG.⊗-homo.η _ C.⊗₁ C.id)
        ≈⟨ refl⟩∘⟨ CG.associativity ⟩
      (G.₁ (CF.⊗-homo.η _) C.∘ G.₁ (B.id B.⊗₁ CF.⊗-homo.η _)) C.∘ CG.⊗-homo.η _ C.∘ (C.id C.⊗₁ CG.⊗-homo.η _) C.∘ C.associator.from
        ≈⟨ center (CG.⊗-homo.sym-commute _) ⟩
      G.₁ (CF.⊗-homo.η _) C.∘ (CG.⊗-homo.η _ C.∘ (G.₁ B.id C.⊗₁ G.₁ (CF.⊗-homo.η _))) C.∘ (C.id C.⊗₁ CG.⊗-homo.η _) C.∘ C.associator.from
        ≈⟨ pull-first C.Equiv.refl ○ C.∘-resp-≈ʳ (C.∘-resp-≈ˡ (C.⊗.F-resp-≈ (G.identity , C.Equiv.refl))) ⟩
      (G.₁ (CF.⊗-homo.η _) C.∘ CG.⊗-homo.η _) C.∘ (C.id C.⊗₁ G.₁ (CF.⊗-homo.η _)) C.∘ (C.id C.⊗₁ CG.⊗-homo.η _) C.∘ C.associator.from
        ≈˘⟨ refl⟩∘⟨ pushˡ (Functor.homomorphism (_ C.⊗-)) ⟩
      (G.₁ (CF.⊗-homo.η _) C.∘ CG.⊗-homo.η _) C.∘ (C.id C.⊗₁ (G.F₁ (CF.⊗-homo.η _) C.∘ CG.⊗-homo.η _)) C.∘ C.associator.from
        ∎
    ; unitaryˡ      = begin
      G.₁ (F.₁ A.unitorˡ.from) C.∘ (G.₁ (CF.⊗-homo.η _) C.∘ CG.⊗-homo.η _) C.∘ ((G.₁ CF.ε C.∘ CG.ε) C.⊗₁ C.id)
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (Functor.homomorphism (C.-⊗ _) ○ C.∘-resp-≈ˡ (C.⊗.F-resp-≈ (C.Equiv.refl , ⟺ G.identity))) ⟩
      G.₁ (F.₁ A.unitorˡ.from) C.∘ (G.₁ (CF.⊗-homo.η _) C.∘ CG.⊗-homo.η _) C.∘ (G.₁ CF.ε C.⊗₁ G.₁ B.id) C.∘ (CG.ε C.⊗₁ C.id)
        ≈⟨ refl⟩∘⟨ center (CG.⊗-homo.commute _) ⟩
      G.₁ (F.₁ A.unitorˡ.from) C.∘ G.₁ (CF.⊗-homo.η _) C.∘ (G.₁ (CF.ε B.⊗₁ B.id) C.∘ CG.⊗-homo.η _) C.∘ (CG.ε C.⊗₁ C.id)
        ≈⟨ C.∘-resp-≈ʳ (center⁻¹ C.Equiv.refl C.Equiv.refl) ○ C.sym-assoc ⟩
      (G.₁ (F.₁ A.unitorˡ.from) C.∘ G.₁ (CF.⊗-homo.η _) C.∘ G.₁ (CF.ε B.⊗₁ B.id)) C.∘ CG.⊗-homo.η _ C.∘ (CG.ε C.⊗₁ C.id)
        ≈⟨ C.∘-resp-≈ʳ (⟺ G.homomorphism) ⟩∘⟨refl ⟩
      (G.₁ (F.₁ A.unitorˡ.from) C.∘ G.₁ (CF.⊗-homo.η _ B.∘ CF.ε B.⊗₁ B.id)) C.∘ CG.⊗-homo.η _ C.∘ (CG.ε C.⊗₁ C.id)
        ≈⟨ [ G ]-resp-∘ CF.unitaryˡ ⟩∘⟨refl ⟩
      G.₁ B.unitorˡ.from C.∘ CG.⊗-homo.η _ C.∘ (CG.ε C.⊗₁ C.id)
        ≈⟨ CG.unitaryˡ ⟩
      C.unitorˡ.from
        ∎
    ; unitaryʳ      = begin
      G.₁ (F.₁ A.unitorʳ.from) C.∘ (G.₁ (CF.⊗-homo.η _) C.∘ CG.⊗-homo.η _) C.∘ (C.id C.⊗₁ (G.₁ CF.ε C.∘ CG.ε))
        ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ (Functor.homomorphism (_ C.⊗-) ○ C.∘-resp-≈ˡ (C.⊗.F-resp-≈ (⟺ G.identity , C.Equiv.refl)))) ⟩
      G.₁ (F.₁ A.unitorʳ.from) C.∘ (G.₁ (CF.⊗-homo.η _) C.∘ CG.⊗-homo.η _) C.∘ (G.₁ B.id C.⊗₁ G.₁ CF.ε) C.∘ (C.id C.⊗₁ CG.ε)
        ≈⟨ refl⟩∘⟨ center (CG.⊗-homo.commute _) ⟩
      G.₁ (F.₁ A.unitorʳ.from) C.∘ G.₁ (CF.⊗-homo.η _) C.∘ (G.₁ (B.id B.⊗₁ CF.ε) C.∘ CG.⊗-homo.η _) C.∘ (C.id C.⊗₁ CG.ε)
        ≈⟨ C.∘-resp-≈ʳ (center⁻¹ C.Equiv.refl C.Equiv.refl) ○ C.sym-assoc ⟩
      (G.₁ (F.₁ A.unitorʳ.from) C.∘ G.₁ (CF.⊗-homo.η _) C.∘ G.₁ (B.id B.⊗₁ CF.ε)) C.∘ CG.⊗-homo.η _ C.∘ (C.id C.⊗₁ CG.ε)
        ≈⟨ C.∘-resp-≈ʳ (⟺ G.homomorphism) ⟩∘⟨refl ⟩
      (G.₁ (F.₁ A.unitorʳ.from) C.∘ G.F₁ (CF.⊗-homo.η _ B.∘ (B.id B.⊗₁ CF.ε))) C.∘ CG.⊗-homo.η _ C.∘ (C.id C.⊗₁ CG.ε)
        ≈⟨ [ G ]-resp-∘ CF.unitaryʳ ⟩∘⟨refl ⟩
      G.F₁ B.unitorʳ.from C.∘ CG.⊗-homo.η _ C.∘ C.id C.⊗₁ CG.ε
        ≈⟨ CG.unitaryʳ ⟩
      C.unitorʳ.from
        ∎
    }
    where module F  = Functor F
          module G  = Functor G
          module CF = IsMonoidalFunctor CF
          module CG = IsMonoidalFunctor CG


  ∘-IsStrongMonoidal : ∀ {F : Functor A.U B.U} {G : Functor B.U C.U} →
                    IsStrongMonoidalFunctor B C G → IsStrongMonoidalFunctor A B F →
                    IsStrongMonoidalFunctor A C (G ∘F F)
  ∘-IsStrongMonoidal {F} {G} CG CF = record
    { ε             = ≅.trans CG.ε ([ G ]-resp-≅ CF.ε)
    ; ⊗-homo        = record
      { F⇒G = ∘.⊗-homo
      ; F⇐G = ntHelper record
        { η       = λ { (X , Y) → CG.⊗-homo.⇐.η (F.F₀ X , F.F₀ Y) C.∘ G.₁ (CF.⊗-homo.⇐.η (X , Y)) }
        ; commute = λ _ → pullʳ ([ G ]-resp-square (CF.⊗-homo.⇐.commute _)) ○ pullˡ (CG.⊗-homo.⇐.commute _) ○ C.assoc
        }
      ; iso = λ _ → record
        { isoˡ = cancelInner ([ G ]-resp-inverse (CF.⊗-homo.iso.isoˡ _)) ○ CG.⊗-homo.iso.isoˡ _
        ; isoʳ = cancelInner (CG.⊗-homo.iso.isoʳ _) ○ [ G ]-resp-inverse (CF.⊗-homo.iso.isoʳ _)
        }
      }
    ; associativity = ∘.associativity
    ; unitaryˡ      = ∘.unitaryˡ
    ; unitaryʳ      = ∘.unitaryʳ
    }
    where module F  = Functor F
          module G  = Functor G
          module CF = IsStrongMonoidalFunctor CF
          module CG = IsStrongMonoidalFunctor CG
          module ∘  = IsMonoidalFunctor (∘-IsMonoidal CG.isMonoidal CF.isMonoidal)

module _ {A : MonoidalCategory o ℓ e} {B : MonoidalCategory o′ ℓ′ e′} {C : MonoidalCategory o″ ℓ″ e″} where

    ∘-StrongMonoidal : StrongMonoidalFunctor B C → StrongMonoidalFunctor A B → StrongMonoidalFunctor A C
    ∘-StrongMonoidal G F = record { isStrongMonoidal = ∘-IsStrongMonoidal _ _ _ (StrongMonoidalFunctor.isStrongMonoidal G) (StrongMonoidalFunctor.isStrongMonoidal F) }

    ∘-Monoidal : MonoidalFunctor B C → MonoidalFunctor A B → MonoidalFunctor A C
    ∘-Monoidal G F = record { isMonoidal = ∘-IsMonoidal _ _ _ (MonoidalFunctor.isMonoidal G) (MonoidalFunctor.isMonoidal F) }

-- Functor composition preserves braided monoidality

module _ {A : BraidedMonoidalCategory o ℓ e}
         {B : BraidedMonoidalCategory o′ ℓ′ e′}
         {C : BraidedMonoidalCategory o″ ℓ″ e″} where

  private
    module A = BraidedMonoidalCategory A
    module B = BraidedMonoidalCategory B
    module C = BraidedMonoidalCategory C
  open Braided

  ∘-IsBraidedMonoidal : ∀ {G : Functor B.U C.U} {F : Functor A.U B.U} →
                        Lax.IsBraidedMonoidalFunctor B C G →
                        Lax.IsBraidedMonoidalFunctor A B F →
                        Lax.IsBraidedMonoidalFunctor A C (G ∘F F)
  ∘-IsBraidedMonoidal {G} {F} GB FB = record
    { isMonoidal      = ∘-IsMonoidal _ _ _ (isMonoidal GB) (isMonoidal FB)
    ; braiding-compat = begin
        G₁ (F₁ AB) ∘ G₁ FH ∘ GH   ≈˘⟨ pushˡ (homomorphism G) ⟩
        G₁ (F₁ AB B.∘ FH) ∘ GH    ≈⟨ F-resp-≈ G (braiding-compat FB) ⟩∘⟨refl ⟩
        G₁ (FH B.∘ BB) ∘ GH       ≈⟨ pushˡ (homomorphism G) ⟩
        G₁ FH ∘ G₁ BB ∘ GH        ≈⟨ pushʳ (braiding-compat GB) ⟩
        (G₁ FH ∘ GH) ∘ CB         ∎
    }
    where
      open C
      open HomReasoning
      open MR C.U
      open Functor hiding (F₁)
      open Functor F using (F₁)
      open Functor G using () renaming (F₁ to G₁)
      open Lax.IsBraidedMonoidalFunctor

      FH  = λ {X Y} → ⊗-homo.η FB (X , Y)
      GH  = λ {X Y} → ⊗-homo.η GB (X , Y)
      AB = λ {X Y} → A.braiding.⇒.η (X , Y)
      BB = λ {X Y} → B.braiding.⇒.η (X , Y)
      CB = λ {X Y} → C.braiding.⇒.η (X , Y)

  ∘-IsStrongBraidedMonoidal : ∀ {G : Functor B.U C.U} {F : Functor A.U B.U} →
                              Strong.IsBraidedMonoidalFunctor B C G →
                              Strong.IsBraidedMonoidalFunctor A B F →
                              Strong.IsBraidedMonoidalFunctor A C (G ∘F F)
  ∘-IsStrongBraidedMonoidal {G} {F} GB FB = record
    { isStrongMonoidal =
      ∘-IsStrongMonoidal _ _ _ (isStrongMonoidal GB) (isStrongMonoidal FB)
    ; braiding-compat =
      Lax.IsBraidedMonoidalFunctor.braiding-compat
        (∘-IsBraidedMonoidal (isLaxBraidedMonoidal GB) (isLaxBraidedMonoidal FB))
    }
    where open Strong.IsBraidedMonoidalFunctor

  ∘-BraidedMonoidal : Lax.BraidedMonoidalFunctor B C →
                      Lax.BraidedMonoidalFunctor A B →
                      Lax.BraidedMonoidalFunctor A C
  ∘-BraidedMonoidal G F = record
    { isBraidedMonoidal =
      ∘-IsBraidedMonoidal (isBraidedMonoidal G) (isBraidedMonoidal F)
    }
    where open Lax.BraidedMonoidalFunctor hiding (F)

  ∘-StrongBraidedMonoidal : Strong.BraidedMonoidalFunctor B C →
                            Strong.BraidedMonoidalFunctor A B →
                            Strong.BraidedMonoidalFunctor A C
  ∘-StrongBraidedMonoidal G F = record
    { isBraidedMonoidal =
      ∘-IsStrongBraidedMonoidal (isBraidedMonoidal G) (isBraidedMonoidal F)
    }
    where open Strong.BraidedMonoidalFunctor hiding (F)

-- Functor composition preserves symmetric monoidality

module _ {A : SymmetricMonoidalCategory o ℓ e}
         {B : SymmetricMonoidalCategory o′ ℓ′ e′}
         {C : SymmetricMonoidalCategory o″ ℓ″ e″} where
  open Symmetric

  ∘-SymmetricMonoidal : Lax.SymmetricMonoidalFunctor B C →
                        Lax.SymmetricMonoidalFunctor A B →
                        Lax.SymmetricMonoidalFunctor A C
  ∘-SymmetricMonoidal G F = record
    { isBraidedMonoidal =
      ∘-IsBraidedMonoidal (isBraidedMonoidal G) (isBraidedMonoidal F)
    }
    where open Lax.SymmetricMonoidalFunctor hiding (F)

  ∘-StrongSymmetricMonoidal : Strong.SymmetricMonoidalFunctor B C →
                              Strong.SymmetricMonoidalFunctor A B →
                              Strong.SymmetricMonoidalFunctor A C
  ∘-StrongSymmetricMonoidal G F = record
    { isBraidedMonoidal =
      ∘-IsStrongBraidedMonoidal (isBraidedMonoidal G) (isBraidedMonoidal F)
    }
    where open Strong.SymmetricMonoidalFunctor hiding (F)

module _ (C : CartesianCategory o ℓ e) (D : CartesianCategory o′ ℓ′ e′) where
  private
    module C = CartesianCategory C
    module D = CartesianCategory D
    module PC = BinaryProducts C.products
    module PD = BinaryProducts D.products
    module TC = ⊤.Terminal C.terminal
    module TD = ⊤.Terminal D.terminal
    open D.HomReasoning
    open MR D.U

  module _ (F : StrongMonoidalFunctor C.monoidalCategory D.monoidalCategory) where
    private
      module F = StrongMonoidalFunctor F

      F-resp-⊤ : ⊤.IsTerminal D.U (F.F₀ TC.⊤)
      F-resp-⊤ = ⊤.Terminal.⊤-is-terminal (⊤.transport-by-iso D.U D.terminal F.ε)
      module F-resp-⊤ = ⊤.IsTerminal F-resp-⊤

      lemma₁ : ∀ {X} → F.ε.from D.∘ TD.! {F.₀ X} D.≈ F.₁ (TC.! {X})
      lemma₁ = F-resp-⊤.!-unique _

      π₁-comm : ∀ {X Y} → F.F₁ PC.π₁ D.∘ F.⊗-homo.⇒.η (X , Y) D.≈ PD.π₁
      π₁-comm {X} {Y} = begin
        F.F₁ PC.π₁ D.∘ F.⊗-homo.⇒.η (X , Y)                                                    ≈˘⟨ [ F.F ]-resp-∘ (C.Equiv.trans PC.project₁ C.identityˡ) ⟩∘⟨refl ⟩
        (F.F₁ PC.π₁ D.∘ F.F₁ (C.id PC.⁂ TC.!)) D.∘ F.⊗-homo.⇒.η (X , Y)                        ≈⟨ pullʳ (F.⊗-homo.⇒.sym-commute _) ⟩
        F.F₁ PC.π₁ D.∘ F.⊗-homo.⇒.η (X , TC.⊤) D.∘ (F.F₁ C.id PD.⁂ F.F₁ TC.!)                  ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ ([ F.₀ X PD.×- ]-resp-∘ lemma₁ ○ Functor.F-resp-≈ PD.-×- (⟺ F.identity , D.Equiv.refl)) ⟩
        F.F₁ PC.π₁ D.∘ F.⊗-homo.⇒.η (X , TC.⊤) D.∘ (D.id PD.⁂ F.ε.from) D.∘ (D.id PD.⁂ TD.!)   ≈⟨ D.∘-resp-≈ʳ D.sym-assoc ○ D.sym-assoc ⟩
        (F.F₁ PC.π₁ D.∘ F.⊗-homo.⇒.η (X , TC.⊤) D.∘ (D.id PD.⁂ F.ε.from)) D.∘ (D.id PD.⁂ TD.!) ≈⟨ F.unitaryʳ ⟩∘⟨refl ⟩
        PD.π₁ D.∘ (D.id PD.⁂ TD.!)                                                              ≈⟨ PD.project₁ ○ D.identityˡ ⟩
        PD.π₁                                                                                   ∎

      π₂-comm : ∀ {X Y} → F.F₁ PC.π₂ D.∘ F.⊗-homo.⇒.η (X , Y) D.≈ PD.π₂
      π₂-comm {X} {Y} = begin
        F.F₁ PC.π₂ D.∘ F.⊗-homo.⇒.η (X , Y)                                                ≈˘⟨ [ F.F ]-resp-∘ (C.Equiv.trans PC.project₂ C.identityˡ) ⟩∘⟨refl ⟩
        (F.F₁ PC.π₂ D.∘ F.F₁ (TC.! PC.⁂ C.id)) D.∘ F.⊗-homo.⇒.η (X , Y)                      ≈⟨ pullʳ (F.⊗-homo.⇒.sym-commute _) ⟩
        F.F₁ PC.π₂ D.∘ F.⊗-homo.⇒.η (TC.⊤ , Y) D.∘ (F.F₁ TC.! PD.⁂ F.F₁ C.id)                 ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ ([ PD.-× F.₀ Y ]-resp-∘ lemma₁ ○ Functor.F-resp-≈ PD.-×- (D.Equiv.refl , ⟺ F.identity)) ⟩
        F.F₁ PC.π₂ D.∘ F.⊗-homo.⇒.η (TC.⊤ , Y) D.∘ (F.ε.from PD.⁂ D.id) D.∘ (TD.! PD.⁂ D.id)   ≈⟨ D.∘-resp-≈ʳ D.sym-assoc ○ D.sym-assoc ⟩
        (F.F₁ PC.π₂ D.∘ F.⊗-homo.⇒.η (TC.⊤ , Y) D.∘ (F.ε.from PD.⁂ D.id)) D.∘ (TD.! PD.⁂ D.id) ≈⟨ F.unitaryˡ ⟩∘⟨refl ⟩
        PD.π₂ D.∘ (TD.! PD.⁂ D.id)                                                           ≈⟨ PD.project₂ ○ D.identityˡ ⟩
        PD.π₂                                                                              ∎

      unique : ∀ {X A B} {h : X D.⇒ F.₀ (A PC.× B)} {i : X D.⇒ F.₀ A} {j : X D.⇒ F.₀ B} →
                 F.₁ PC.π₁ D.∘ h D.≈ i →
                 F.₁ PC.π₂ D.∘ h D.≈ j →
                 F.⊗-homo.⇒.η (A , B) D.∘ PD.⟨ i , j ⟩ D.≈ h
      unique  eq₁ eq₂ = ⟺ (switch-tofromˡ F.⊗-homo.FX≅GX (⟺ (PD.unique (pullˡ (⟺ (switch-fromtoʳ F.⊗-homo.FX≅GX π₁-comm)) ○ eq₁)
                                                                      (pullˡ (⟺ (switch-fromtoʳ F.⊗-homo.FX≅GX π₂-comm)) ○ eq₂))))

    StrongMonoidal⇒Cartesian : CartesianF C D
    StrongMonoidal⇒Cartesian = record
      { F           = F.F
      ; isCartesian = record
        { F-resp-⊤ = F-resp-⊤
        ; F-resp-× = λ {A B} → record
          { ⟨_,_⟩    = λ f g → F.⊗-homo.⇒.η _ D.∘ PD.⟨ f , g ⟩
          ; project₁ = λ {_ h i} → begin
            F.₁ PC.π₁ D.∘ F.⊗-homo.⇒.η _ D.∘ PD.⟨ h , i ⟩ ≈⟨ pullˡ π₁-comm ⟩
            PD.π₁ D.∘ PD.⟨ h , i ⟩                         ≈⟨ PD.project₁ ⟩
            h                                            ∎
          ; project₂ = λ {_ h i} → begin
            F.₁ PC.π₂ D.∘ F.⊗-homo.⇒.η _ D.∘ PD.⟨ h , i ⟩ ≈⟨ pullˡ π₂-comm ⟩
            PD.π₂ D.∘ PD.⟨ h , i ⟩                        ≈⟨ PD.project₂ ⟩
            i                                           ∎
          ; unique   = unique
          }
        }
      }
