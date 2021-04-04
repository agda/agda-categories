{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Monoidal.Properties where

open import Level
open import Data.Product using (_,_)

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Cartesian.Structure
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Properties
open import Categories.Functor.Cartesian
open import Categories.Functor.Monoidal
open import Categories.NaturalTransformation

import Categories.Object.Terminal as ⊤
import Categories.Object.Product as P
import Categories.Morphism as M
import Categories.Morphism.Reasoning as MR

private
  variable
    o o′ o″ ℓ ℓ′ ℓ″ e e′ e″ : Level

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
        { isoˡ = cancelInner ([ G ]-resp-∘ (CF.⊗-homo.iso.isoˡ _) ○ G.identity) ○ CG.⊗-homo.iso.isoˡ _
        ; isoʳ = cancelInner (CG.⊗-homo.iso.isoʳ _) ○ [ G ]-resp-∘ (CF.⊗-homo.iso.isoʳ _) ○ G.identity
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

module _ (C : CartesianCategory o ℓ e) (D : CartesianCategory o′ ℓ′ e′) where
  private
    module C = CartesianCategory C
    module D = CartesianCategory D
    open D.HomReasoning
    open MR D.U

  module _ (F : StrongMonoidalFunctor C.monoidalCategory D.monoidalCategory) where
    private
      module F = StrongMonoidalFunctor F

      F-resp-⊤ : ⊤.IsTerminal D.U (F.F₀ C.⊤)
      F-resp-⊤ = ⊤.Terminal.⊤-is-terminal (⊤.transport-by-iso D.U D.terminal F.ε)
      module F-resp-⊤ = ⊤.IsTerminal F-resp-⊤

      lemma₁ : ∀ {X} → F.ε.from D.∘ D.! {F.₀ X} D.≈ F.₁ (C.! {X})
      lemma₁ = F-resp-⊤.!-unique _

      π₁-comm : ∀ {X Y} → F.F₁ C.π₁ D.∘ F.⊗-homo.⇒.η (X , Y) D.≈ D.π₁
      π₁-comm {X} {Y} = begin
        F.F₁ C.π₁ D.∘ F.⊗-homo.⇒.η (X , Y)                                                ≈˘⟨ [ F.F ]-resp-∘ (C.Equiv.trans C.project₁ C.identityˡ) ⟩∘⟨refl ⟩
        (F.F₁ C.π₁ D.∘ F.F₁ (C.id C.⁂ C.!)) D.∘ F.⊗-homo.⇒.η (X , Y)                      ≈⟨ pullʳ (F.⊗-homo.⇒.sym-commute _) ⟩
        F.F₁ C.π₁ D.∘ F.⊗-homo.⇒.η (X , C.⊤) D.∘ (F.F₁ C.id D.⁂ F.F₁ C.!)                 ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ ([ F.₀ X D.×- ]-resp-∘ lemma₁ ○ Functor.F-resp-≈ D.-×- (⟺ F.identity , D.Equiv.refl)) ⟩
        F.F₁ C.π₁ D.∘ F.⊗-homo.⇒.η (X , C.⊤) D.∘ (D.id D.⁂ F.ε.from) D.∘ (D.id D.⁂ D.!)   ≈⟨ D.∘-resp-≈ʳ D.sym-assoc ○ D.sym-assoc ⟩
        (F.F₁ C.π₁ D.∘ F.⊗-homo.⇒.η (X , C.⊤) D.∘ (D.id D.⁂ F.ε.from)) D.∘ (D.id D.⁂ D.!) ≈⟨ F.unitaryʳ ⟩∘⟨refl ⟩
        D.π₁ D.∘ (D.id D.⁂ D.!)                                                           ≈⟨ D.project₁ ○ D.identityˡ ⟩
        D.π₁                                                                              ∎

      π₂-comm : ∀ {X Y} → F.F₁ C.π₂ D.∘ F.⊗-homo.⇒.η (X , Y) D.≈ D.π₂
      π₂-comm {X} {Y} = begin
        F.F₁ C.π₂ D.∘ F.⊗-homo.⇒.η (X , Y)                                                ≈˘⟨ [ F.F ]-resp-∘ (C.Equiv.trans C.project₂ C.identityˡ) ⟩∘⟨refl ⟩
        (F.F₁ C.π₂ D.∘ F.F₁ (C.! C.⁂ C.id)) D.∘ F.⊗-homo.⇒.η (X , Y)                      ≈⟨ pullʳ (F.⊗-homo.⇒.sym-commute _) ⟩
        F.F₁ C.π₂ D.∘ F.⊗-homo.⇒.η (C.⊤ , Y) D.∘ (F.F₁ C.! D.⁂ F.F₁ C.id)                 ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ ([ D.-× F.₀ Y ]-resp-∘ lemma₁ ○ Functor.F-resp-≈ D.-×- (D.Equiv.refl , ⟺ F.identity)) ⟩
        F.F₁ C.π₂ D.∘ F.⊗-homo.⇒.η (C.⊤ , Y) D.∘ (F.ε.from D.⁂ D.id) D.∘ (D.! D.⁂ D.id)   ≈⟨ D.∘-resp-≈ʳ D.sym-assoc ○ D.sym-assoc ⟩
        (F.F₁ C.π₂ D.∘ F.⊗-homo.⇒.η (C.⊤ , Y) D.∘ (F.ε.from D.⁂ D.id)) D.∘ (D.! D.⁂ D.id) ≈⟨ F.unitaryˡ ⟩∘⟨refl ⟩
        D.π₂ D.∘ (D.! D.⁂ D.id)                                                           ≈⟨ D.project₂ ○ D.identityˡ ⟩
        D.π₂                                                                              ∎

      unique : ∀ {X A B} {h : X D.⇒ F.₀ (A C.× B)} {i : X D.⇒ F.₀ A} {j : X D.⇒ F.₀ B} →
                 F.₁ C.π₁ D.∘ h D.≈ i →
                 F.₁ C.π₂ D.∘ h D.≈ j →
                 F.⊗-homo.⇒.η (A , B) D.∘ D.product.⟨ i , j ⟩ D.≈ h
      unique  eq₁ eq₂ = ⟺ (switch-tofromˡ F.⊗-homo.FX≅GX (⟺ (D.unique (pullˡ (⟺ (switch-fromtoʳ F.⊗-homo.FX≅GX π₁-comm)) ○ eq₁)
                                                                      (pullˡ (⟺ (switch-fromtoʳ F.⊗-homo.FX≅GX π₂-comm)) ○ eq₂))))

    StrongMonoidal⇒Cartesian : CartesianF C D
    StrongMonoidal⇒Cartesian = record
      { F           = F.F
      ; isCartesian = record
        { F-resp-⊤ = F-resp-⊤
        ; F-resp-× = λ {A B} → record
          { ⟨_,_⟩    = λ f g → F.⊗-homo.⇒.η _ D.∘ D.⟨ f , g ⟩
          ; project₁ = λ {_ h i} → begin
            F.₁ C.π₁ D.∘ F.⊗-homo.⇒.η _ D.∘ D.⟨ h , i ⟩ ≈⟨ pullˡ π₁-comm ⟩
            D.π₁ D.∘ D.product.⟨ h , i ⟩                ≈⟨ D.project₁ ⟩
            h                                           ∎
          ; project₂ = λ {_ h i} → begin
            F.₁ C.π₂ D.∘ F.⊗-homo.⇒.η _ D.∘ D.⟨ h , i ⟩ ≈⟨ pullˡ π₂-comm ⟩
            D.π₂ D.∘ D.⟨ h , i ⟩                        ≈⟨ D.project₂ ⟩
            i                                           ∎
          ; unique   = unique
          }
        }
      }
