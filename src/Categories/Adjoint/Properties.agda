{-# OPTIONS --without-K --safe #-}

module Categories.Adjoint.Properties where

open import Level
open import Data.Product using (Σ; _,_; -,_; proj₂; uncurry)
open import Function.Base using (_$_)

open import Categories.Adjoint using (_⊣_; Adjoint)
open import Categories.Adjoint.Equivalents using (Hom-NI′⇒Adjoint)
open import Categories.Category using (Category; _[_,_])
open import Categories.Category.Product using (_⁂_; _⁂ⁿⁱ_)
open import Categories.Category.Construction.Comma using (CommaObj; Comma⇒; _↙_)
open import Categories.Diagram.Limit
open import Categories.Diagram.Colimit
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Hom
open import Categories.Functor.Construction.Constant
open import Categories.Functor.Construction.LiftSetoids
open import Categories.Functor.Properties
open import Categories.Functor.Limits
open import Categories.Functor.Bifunctor
open import Categories.Functor.Bifunctor.Properties
open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.Properties
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; _≃_; _ⓘₕ_; _ⓘˡ_; module ≃)
open import Categories.NaturalTransformation.NaturalIsomorphism.Properties
open import Categories.Monad
open import Categories.Monad.Duality
open import Categories.Comonad
open import Categories.Morphism.Universal
open import Categories.Yoneda
import Categories.Yoneda.Properties as YP

import Categories.Diagram.Colimit as Col
import Categories.Diagram.Duality as Duality

import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR

-- public export
open import Categories.Adjoint.RAPL using (rapl) public
open import Categories.Adjoint.Alternatives using (fromUnit; fromCounit) public

private
  variable
    o ℓ e : Level
    C D E J : Category o ℓ e

-- if the left adjoint functor is a partial application of bifunctor, then it uniquely
-- determines a bifunctor compatible with the right adjoint functor.
module _ {C : Category o ℓ e}
         (L : Bifunctor C E D) {R : ∀ (X : Category.Obj E) → Functor D C}
         (LR : ∀ (X : Category.Obj E) → appʳ L X ⊣ R X) where
  private
    module C    = Category C
    module D    = Category D
    module E    = Category E
    module L    = Functor L
    module R X  = Functor (R X)
    module LR X = Adjoint (LR X)
    open C

    F′ : ∀ {A X B Y} f g → R.F₀ A X ⇒ R.F₀ B Y
    F′ {A} {X} {B} {Y} f g = LR.Ladjunct B (LR.counit.η A Y D.∘ L.F₁ (R.F₁ A g , f))
    --  R.F₁ B (LR.counit.η A Y) ∘ R.F₁ B (L.F₁ (R.F₁ A g , f)) ∘ LR.unit.η B (R.F₀ A X)

    commute′ : ∀ {A B X} (f : A E.⇒ B) → LR.counit.η A X D.∘ L.F₁ (F′ f D.id , E.id) D.≈ LR.counit.η B X D.∘ L.F₁ (C.id , f)
    commute′ {A} {B} {X} f = begin
      LR.counit.η A X D.∘ L.F₁ (F′ f D.id , E.id) ≈⟨ LR.RLadjunct≈id A ⟩
      LR.counit.η B X D.∘ L.F₁ (R.F₁ B D.id , f)  ≈⟨ refl⟩∘⟨ L.F-resp-≈ (R.identity B , E.Equiv.refl) ⟩
      LR.counit.η B X D.∘ L.F₁ (C.id , f)         ∎
      where open D.HomReasoning

    open HomReasoning

    decompose₁ : ∀ {A B X Y} {f : A E.⇒ B} {g : X D.⇒ Y} → F′ f g ≈ R.F₁ A g ∘ F′ f D.id
    decompose₁ {A} {B} {X} {Y} {f} {g} = begin
      F′ f g
        ≈⟨ R.F-resp-≈ A (D.∘-resp-≈ʳ [ L ]-decompose₁) ⟩∘⟨refl ⟩
      R.F₁ A (LR.counit.η B Y D.∘ L.F₁ (R.F₁ B g , E.id) D.∘ L.F₁ (C.id , f)) ∘ LR.unit.η A (R.F₀ B X)
        ≈⟨ R.F-resp-≈ A (pullˡ (LR.counit.commute B g)) ⟩∘⟨refl ⟩
      R.F₁ A ((g D.∘ LR.counit.η B X) D.∘ L.F₁ (C.id , f)) ∘ LR.unit.η A (R.F₀ B X)
        ≈˘⟨ R.F-resp-≈ A (pushʳ (D.∘-resp-≈ʳ (L.F-resp-≈ (R.identity B , E.Equiv.refl)))) ⟩∘⟨refl ⟩
      R.F₁ A (g D.∘ LR.counit.η B X D.∘ L.F₁ (R.F₁ B D.id , f)) ∘ LR.unit.η A (R.F₀ B X)
        ≈⟨ R.homomorphism A ⟩∘⟨refl ⟩
      (R.F₁ A g ∘ R.F₁ A (LR.counit.η B X D.∘ L.F₁ (R.F₁ B D.id , f))) ∘ LR.unit.η A (R.F₀ B X)
        ≈⟨ assoc ⟩
      R.F₁ A g ∘ F′ f D.id
        ∎
      where open MR D

    decompose₂ : ∀ {A B X Y} {f : A E.⇒ B} {g : X D.⇒ Y} → F′ f g ≈ F′ f D.id ∘ R.F₁ B g
    decompose₂ {A} {B} {X} {Y} {f} {g} = begin
      F′ f g
        ≈⟨ R.F-resp-≈ A (D.∘-resp-≈ʳ [ L ]-decompose₂) ⟩∘⟨refl ⟩
      R.F₁ A (LR.counit.η B Y D.∘ L.F₁ (C.id , f) D.∘ L.F₁ (R.F₁ B g , E.id)) ∘ LR.unit.η A (R.F₀ B X)
        ≈˘⟨ R.F-resp-≈ A (pushˡ (D.∘-resp-≈ʳ (L.F-resp-≈ (R.identity B , E.Equiv.refl)))) ⟩∘⟨refl ⟩
      R.F₁ A ((LR.counit.η B Y D.∘ L.F₁ (R.F₁ B D.id , f)) D.∘ L.F₁ (R.F₁ B g , E.id)) ∘ LR.unit.η A (R.F₀ B X)
        ≈⟨ R.homomorphism A ⟩∘⟨refl ⟩
      (R.F₁ A (LR.counit.η B Y D.∘ L.F₁ (R.F₁ B D.id , f)) ∘ R.F₁ A (L.F₁ (R.F₁ B g , E.id))) ∘ LR.unit.η A (R.F₀ B X)
        ≈˘⟨ MR.pushʳ C (LR.unit.commute A (R.F₁ B g)) ⟩
      R.F₁ A (LR.counit.η B Y D.∘ L.F₁ (R.F₁ B D.id , f)) ∘ LR.unit.η A (R.F₀ B Y) ∘ R.F₁ B g
        ≈⟨ sym-assoc ⟩
      F′ f D.id ∘ R.F₁ B g
        ∎
      where open MR D

    swap : ∀ {A B X Y} {f : A E.⇒ B} {g : X D.⇒ Y} → R.F₁ A g ∘ F′ f D.id ≈ F′ f D.id ∘ R.F₁ B g
    swap = ⟺ decompose₁ ○ decompose₂

    commute″ : ∀ {X Y Z A} {f : Y E.⇒ Z} {g : X E.⇒ Y} → F′ (f E.∘ g) (D.id {A}) ≈ F′ g D.id ∘ F′ f D.id
    commute″ {X} {Y} {Z} {A} {f} {g} = begin
      F′ (f E.∘ g) D.id
        ≈⟨ R.F-resp-≈ X (D.∘-resp-≈ʳ (L.F-resp-≈ (R.identity Z , E.Equiv.refl))) ⟩∘⟨refl ⟩
      R.F₁ X (LR.counit.η Z A D.∘ L.F₁ (C.id , f E.∘ g)) ∘ LR.unit.η X (R.F₀ Z A)
        ≈⟨ R.F-resp-≈ X (D.∘-resp-≈ʳ (Functor.homomorphism (appˡ L (R.F₀ Z A)))) ⟩∘⟨refl ⟩
      R.F₁ X (LR.counit.η Z A D.∘ L.F₁ (C.id , f) D.∘ L.F₁ (C.id , g)) ∘ LR.unit.η X (R.F₀ Z A)
        ≈˘⟨ R.F-resp-≈ X (MR.pushˡ D (commute′ f)) ⟩∘⟨refl ⟩
      R.F₁ X ((LR.counit.η Y A D.∘ L.F₁ (F′ f D.id , E.id)) D.∘ L.F₁ (C.id , g)) ∘ LR.unit.η X (R.F₀ Z A)
        ≈˘⟨ R.F-resp-≈ X (MR.pushʳ D [ L ]-commute) ⟩∘⟨refl ⟩
      R.F₁ X (LR.counit.η Y A D.∘ L.F₁ (C.id , g) D.∘ L.F₁ (F′ f D.id , E.id)) ∘ LR.unit.η X (R.F₀ Z A)
        ≈⟨ R.F-resp-≈ X D.sym-assoc ⟩∘⟨refl ⟩
      R.F₁ X ((LR.counit.η Y A D.∘ L.F₁ (C.id , g)) D.∘ L.F₁ (F′ f D.id , E.id)) ∘ LR.unit.η X (R.F₀ Z A)
        ≈⟨ R.homomorphism X ⟩∘⟨refl ⟩
      (R.F₁ X (LR.counit.η Y A D.∘ L.F₁ (C.id , g)) ∘ R.F₁ X (L.F₁ (F′ f D.id , E.id))) ∘ LR.unit.η X (R.F₀ Z A)
        ≈˘⟨ MR.pushʳ C (LR.unit.commute X (F′ f D.id)) ⟩
      R.F₁ X (LR.counit.η Y A D.∘ L.F₁ (C.id , g)) ∘ LR.unit.η X (R.F₀ Y A) ∘ F′ f D.id
        ≈˘⟨ R.F-resp-≈ X (D.∘-resp-≈ʳ (L.F-resp-≈ (R.identity Y , E.Equiv.refl))) ⟩∘⟨refl ⟩
      R.F₁ X (LR.counit.η Y A D.∘ L.F₁ (R.F₁ Y D.id , g)) ∘ LR.unit.η X (R.F₀ Y A) ∘ F′ f D.id
        ≈⟨ sym-assoc ⟩
      F′ g D.id ∘ F′ f D.id
        ∎

  induced-bifunctorʳ : Bifunctor E.op D C
  induced-bifunctorʳ = record
    { F₀           = uncurry R.F₀
    ; F₁           = uncurry F′
    ; identity     = λ where
      {e , d} →
        let open MR D
        in begin
          F′ E.id D.id
            ≈⟨ R.F-resp-≈ e (D.∘-resp-≈ʳ (L.F-resp-≈ (R.identity e , E.Equiv.refl))) ⟩∘⟨refl ⟩
          R.F₁ e (LR.counit.η e d D.∘ L.F₁ (C.id , E.id)) ∘ LR.unit.η e (R.F₀ e d)
            ≈⟨ R.F-resp-≈ e (elimʳ L.identity) ⟩∘⟨refl ⟩
          R.F₁ e (LR.counit.η e d) ∘ LR.unit.η e (R.F₀ e d)
            ≈⟨ LR.zag e ⟩
          C.id
            ∎
    ; homomorphism = λ where
      {A , X} {B , Y} {W , Z} {f , h} {g , i} →
        let open MR C
        in begin
          F′ (f E.∘ g) (i D.∘ h)
            ≈⟨ decompose₁ ⟩
          R.F₁ W (i D.∘ h) ∘ F′ (f E.∘ g) D.id
            ≈˘⟨ center⁻¹ (⟺ (R.homomorphism W)) (⟺ commute″) ⟩
          R.F₁ W i ∘ (R.F₁ W h ∘ F′ g D.id) ∘ F′ f D.id
            ≈˘⟨ center (⟺ swap) ⟩
          (R.F₁ W i ∘ F′ g D.id) ∘ R.F₁ B h ∘ F′ f D.id
            ≈˘⟨ decompose₁ ⟩∘⟨ decompose₁ ⟩
          F′ g i ∘ F′ f h
            ∎
    ; F-resp-≈     = λ where
      {A , X} {B , Y} (eq , eq′) →
        ∘-resp-≈ˡ (R.F-resp-≈ B (D.∘-resp-≈ʳ (L.F-resp-≈ (R.F-resp-≈ A eq′ , eq))))
    }

-- LAPC: left adjoint preserves colimits.
module _ {L : Functor C D} {R : Functor D C} (L⊣R : L ⊣ R) (F : Functor J C) where
  private
    module F = Functor F
    open Col

  lapc : Colimit F → Colimit (L ∘F F)
  lapc col = Duality.coLimit⇒Colimit D (rapl (Adjoint.op L⊣R) F.op (Duality.Colimit⇒coLimit C col))

-- adjoint functors induce monads and comonads
module _ {L : Functor C D} {R : Functor D C} (L⊣R : L ⊣ R) where
  private
    module C = Category C
    module D = Category D
    module L = Functor L
    module R = Functor R
    open Adjoint L⊣R

  rapl′ : ∀ {o ℓ e} → Continuous o ℓ e R
  rapl′ lim = terminal.⊤-is-terminal
    where open Limit (rapl L⊣R _ lim)

  lapc′ : ∀ {o ℓ e} → Cocontinuous o ℓ e L
  lapc′ col = initial.⊥-is-initial
    where open Colimit (lapc L⊣R _ col)

  adjoint⇒monad : Monad C
  adjoint⇒monad = record
    { F         = R ∘F L
    ; η         = unit
    ; μ         = record
      { η           = μ′.η
      ; commute     = μ′.commute
      ; sym-commute = μ′.sym-commute
      }
    ; assoc     = [ R ]-resp-square (counit.commute _)
    ; sym-assoc = [ R ]-resp-square (counit.sym-commute _)
    ; identityˡ = λ {X} → begin
      μ′.η X ∘ R.F₁ (L.F₁ (unit.η X)) ≈⟨ [ R ]-resp-∘ zig ⟩
      R.F₁ D.id                       ≈⟨ R.identity ⟩
      C.id                            ∎
    ; identityʳ = zag
    }
    where open C
          open HomReasoning
          μ′ : NaturalTransformation (R ∘F (L ∘F R) ∘F L) (R ∘F Categories.Functor.id ∘F L)
          μ′ = R ∘ˡ counit ∘ʳ L
          module μ′ = NaturalTransformation μ′

module _ {L : Functor C D} {R : Functor D C} (L⊣R : L ⊣ R) where
  open Adjoint L⊣R

  adjoint⇒comonad : Comonad D
  adjoint⇒comonad = coMonad⇒Comonad D (adjoint⇒monad op)

-- adjoint functors are the same as universal morphisms
module _ {R : Functor D C} where
  private
    module C = Category C
    module D = Category D
    module R = Functor R

  adjoint⇒universalMorphisms : ∀ {L : Functor C D} → L ⊣ R → ∀ (X : C.Obj) → UniversalMorphism X R
  adjoint⇒universalMorphisms {L} L⊣R X = record
    { initial = record
      { ⊥        = record { f = unit.η X }
      ; ⊥-is-initial = record
        { !        =
          let open C.HomReasoning
          in record { commute = LRadjunct≈id ○ ⟺ C.identityʳ }
        ; !-unique = λ {A} g →
          let open D.HomReasoning
          in -, (begin
            Radjunct (f A)            ≈⟨ Radjunct-resp-≈ (C.Equiv.sym (C.Equiv.trans (commute g) (C.identityʳ {f = f A}))) ⟩
            Radjunct (Ladjunct (h g)) ≈⟨ RLadjunct≈id ⟩
            h g                       ∎)
        }
      }
    }
    where module L = Functor L
          open Adjoint L⊣R
          open Comma⇒
          open CommaObj

  universalMophisms⇒adjoint : (∀ (X : C.Obj) → UniversalMorphism X R) → Σ (Functor C D) (λ L → L ⊣ R)
  universalMophisms⇒adjoint umors = L , record
    { unit   = ntHelper record
      { η       = λ c → f (umors.⊥ c)
      ; commute = λ i → let open C.HomReasoning in ⟺ (commute (⊥X⇒⊥Y i) ○ C.identityʳ )
      }
    ; counit = ntHelper record
      { η       = ε
      ; commute = λ {X Y} i →
        let open C.HomReasoning
            open MR C
        in proj₂ $ umors.!-unique₂ (R.F₀ X)
           {record { f = R.F₁ i }}
           (record
           { h       = ε Y D.∘ L₁ (R.F₁ i)
           ; commute = begin
             R.F₁ (ε Y D.∘ L₁ (R.F₁ i)) C.∘ f (⊥Rd X)          ≈⟨ R.homomorphism ⟩∘⟨refl ⟩
             (R.F₁ (ε Y) C.∘ R.F₁ (L₁ (R.F₁ i))) C.∘ f (⊥Rd X) ≈⟨ pullʳ (commute (⊥X⇒⊥Y (R.F₁ i)) ○ C.identityʳ) ⟩
             R.F₁ (ε Y) C.∘ f (⊥Rd Y) C.∘ R.F₁ i               ≈⟨ cancelˡ (commute (⊥Rd⇒id Y) ○ C.identityˡ) ⟩
             R.F₁ i                                            ≈˘⟨ C.identityʳ ⟩
             R.F₁ i C.∘ C.id                                   ∎
           })
           (record
           { h       = i D.∘ ε X
           ; commute = begin
             R.F₁ (i D.∘ ε X) C.∘ f (⊥Rd X)        ≈⟨ R.homomorphism ⟩∘⟨refl ⟩
             (R.F₁ i C.∘ R.F₁ (ε X)) C.∘ f (⊥Rd X) ≈⟨ cancelʳ (commute (⊥Rd⇒id X) ○ C.identityˡ) ⟩
             R.F₁ i                                ≈˘⟨ C.identityʳ ⟩
             R.F₁ i C.∘ C.id                       ∎
           })
      }
    ; zig    = λ {c} →
      let open C.HomReasoning
          open MR C
          α = f (umors.⊥ c)
      in proj₂ $ umors.!-unique₂ c
         {record { f = α }}
         (record
         { h       = ε (L₀ c) D.∘ L₁ α
         ; commute = begin
           R.F₁ (ε (L₀ c) D.∘ L₁ α) C.∘ α           ≈⟨ R.homomorphism ⟩∘⟨refl ⟩
           (R.F₁ (ε (L₀ c)) C.∘ R.F₁ (L₁ α)) C.∘ α  ≈⟨ pullʳ (commute (⊥X⇒⊥Y α) ○ C.identityʳ) ⟩
           R.F₁ (ε (L₀ c)) C.∘ f (⊥Rd (L₀ c)) C.∘ α ≈⟨ cancelˡ (commute (⊥Rd⇒id (L₀ c)) ○ C.identityˡ) ⟩
           α                                        ≈˘⟨ C.identityʳ ⟩
           α C.∘ C.id                               ∎
         })
         (record
         { h       = D.id
         ; commute = C.∘-resp-≈ˡ R.identity ○ id-comm-sym
         })
    ; zag    = λ {d} → C.Equiv.trans (commute (⊥Rd⇒id d)) C.identityˡ
    }
    where module umors X = UniversalMorphism (umors X)
          open CommaObj
          open Comma⇒

          commaObj∘g : ∀ {X Y} → X C.⇒ Y → CommaObj (const! X) R
          commaObj∘g {X} {Y} g = record { f = f (umors.⊥ Y) C.∘ g }

          ⊥X⇒⊥Y : ∀ {X Y} (g : X C.⇒ Y) → (X ↙ R) [ umors.⊥ X , commaObj∘g g ]
          ⊥X⇒⊥Y {X} {Y} g = umors.! X {commaObj∘g g}

          L₀ : ∀ X → D.Obj
          L₀ X         = β (umors.⊥ X)
          L₁ : ∀ {X Y} → X C.⇒ Y → β (umors.⊥ X) D.⇒ β (umors.⊥ Y)
          L₁ {X} {Y} g = h (⊥X⇒⊥Y g)
          L : Functor C D
          L            = record
            { F₀           = L₀
            ; F₁           = L₁
            ; identity     = λ {X} → proj₂ $ umors.!-unique X $
              record { commute = elimˡ R.identity ○ ⟺ C.identityʳ ○ ⟺ C.identityʳ }
            ; homomorphism = λ {X Y Z} {i j} → proj₂ $ umors.!-unique₂ X (umors.! X) $
              record { commute = begin
                R.F₁ (h (umors.! Y) D.∘ h (umors.! X)) C.∘ f (umors.⊥ X)
                  ≈⟨ (C.∘-resp-≈ˡ R.homomorphism) ○ C.assoc ⟩
                R.F₁ (h (umors.! Y)) C.∘ R.F₁ (h (umors.! X)) C.∘ f (umors.⊥ X)
                  ≈⟨ (C.∘-resp-≈ʳ (commute (⊥X⇒⊥Y i) ○ C.identityʳ)) ○ C.sym-assoc ⟩
                (R.F₁ (h (umors.! Y)) C.∘ f (umors.⊥ Y)) C.∘ i
                  ≈⟨ pushˡ (commute (⊥X⇒⊥Y j) ○ C.identityʳ) ⟩
                f (umors.⊥ Z) C.∘ j C.∘ i
                  ≈˘⟨ C.identityʳ ⟩
                (f (umors.⊥ Z) C.∘ j C.∘ i) C.∘ C.id
                  ∎ }
            ; F-resp-≈     = λ {X} eq → proj₂ $ umors.!-unique₂ X (umors.! X) $
              record { commute = commute (umors.! X) ○ C.∘-resp-≈ˡ (C.∘-resp-≈ʳ (⟺ eq)) }
            }
            where open C.HomReasoning
                  open MR C
          module L = Functor L

          ⊥Rd    : (d : D.Obj) → CommaObj (const! (R.F₀ d)) R
          ⊥Rd d    = umors.⊥ (R.F₀ d)
          ⊥Rd⇒id : (d : D.Obj) →  (R.F₀ d ↙ R) [ ⊥Rd d , record { f = C.id } ]
          ⊥Rd⇒id d = umors.! (R.F₀ d) {record { f = C.id }}
          ε      : ∀ d → L₀ (R.F₀ d) D.⇒ d
          ε d      = h (⊥Rd⇒id d)

-- adjoint functors of a functor are isomorphic
module _ (L : Functor C D) where
  open YP C

  R≃R′ : ∀ {R R′} → L ⊣ R → L ⊣ R′ → R ≃ R′
  R≃R′ {R} {R′} L⊣R L⊣R′ = yoneda-NI R R′ (unlift-≃ Hom[-,R-]≃Hom[-,R′-])
    where module ⊣₁ = Adjoint L⊣R
          module ⊣₂ = Adjoint L⊣R′
          Hom[-,R-]≃Hom[-,R′-] : ⊣₁.Hom[-,R-]′ ≃ ⊣₂.Hom[-,R-]′
          Hom[-,R-]≃Hom[-,R′-] = ≃.trans (≃.sym ⊣₁.Hom-NI) ⊣₂.Hom-NI

module _ {R : Functor D C} where

  L≃L′ : ∀ {L L′} → L ⊣ R → L′ ⊣ R → L ≃ L′
  L≃L′ L⊣R L′⊣R = NaturalIsomorphism.op L′≃Lᵒᵖ
    where module ⊣₁ = Adjoint L⊣R
          module ⊣₂ = Adjoint L′⊣R
          L′≃Lᵒᵖ = R≃R′ (Functor.op R) ⊣₂.op ⊣₁.op

-- adjoint functors are preserved by natural isomorphisms
module _ {L L′ : Functor C D} {R R′ : Functor D C} where
  private
    module C  = Category C
    module D  = Category D
    module L  = Functor L
    module L′ = Functor L′
    module R  = Functor R
    module R′ = Functor R′

  ⊣×≃⇒⊣ : L ⊣ R → L ≃ L′ → R ≃ R′ → L′ ⊣ R′
  ⊣×≃⇒⊣ L⊣R L≃L′ R≃R′ = Hom-NI′⇒Adjoint (≃.trans (LiftSetoids _ _  ⓘˡ Hom[L′-,-]≃Hom[L-,-])
                                        (≃.trans Hom-NI
                                                 (LiftSetoids _ _  ⓘˡ Hom[-,R-]≃Hom[-,R′-])))
    where open Adjoint L⊣R
          Hom[L′-,-]≃Hom[L-,-] : Hom[ D ][-,-] ∘F (L′.op ⁂ idF) ≃ Hom[ D ][-,-] ∘F (L.op ⁂ idF)
          Hom[L′-,-]≃Hom[L-,-] = Hom[ D ][-,-] ⓘˡ (NaturalIsomorphism.op L≃L′ ⁂ⁿⁱ ≃.refl)
          Hom[-,R-]≃Hom[-,R′-] : Hom[ C ][-,-] ∘F (idF ⁂ R) ≃ Hom[ C ][-,-] ∘F (idF ⁂ R′)
          Hom[-,R-]≃Hom[-,R′-] = Hom[ C ][-,-] ⓘˡ (≃.refl ⁂ⁿⁱ R≃R′)
