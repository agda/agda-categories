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
    o o′ ℓ ℓ′ e e′ : Level

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
      C.associator.from C.∘ C.id ≈⟨ id-comm ⟩
      C.id C.∘ C.associator.from ≈⟨ refl⟩∘⟨ introˡ C.⊗.identity ⟩
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
