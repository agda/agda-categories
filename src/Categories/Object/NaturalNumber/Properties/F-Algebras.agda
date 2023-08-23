{-# OPTIONS --without-K --safe #-}
module Categories.Object.NaturalNumber.Properties.F-Algebras where

open import Level
open import Function using (_$_)

open import Categories.Category
open import Categories.Category.Construction.F-Algebras
open import Categories.Category.Cocartesian
open import Categories.Category.Cartesian
open import Categories.Category.Cartesian.Bundle
open import Categories.Category.BinaryProducts
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Algebra
open import Categories.Object.Terminal renaming (up-to-iso to ⊤-up-to-iso)
open import Categories.Object.Initial

import Categories.Morphism.Reasoning as MR
import Categories.Object.NaturalNumber as NNO
import Categories.Object.NaturalNumber.Parametrized as PNNO

-- A NNO is an inital algebra for the 'X ↦ ⊤ + X' endofunctor.
module _ {o ℓ e} (𝒞 : Category o ℓ e) (𝒞-Terminal : Terminal 𝒞) (𝒞-Coproducts : BinaryCoproducts 𝒞) where

  open Terminal 𝒞-Terminal
  open BinaryCoproducts 𝒞-Coproducts
  open Category 𝒞
  open HomReasoning
  open Equiv
  open MR 𝒞
  open NNO 𝒞 𝒞-Terminal
  
  Maybe : Functor 𝒞 𝒞
  Maybe = record
    { F₀ = λ X → ⊤ + X
    ; F₁ = λ f → [ i₁ , i₂ ∘ f ]
    ; identity = []-cong₂ refl identityʳ ○ +-η 
    ; homomorphism = +-unique (pullʳ inject₁ ○ inject₁) (pullʳ inject₂ ○ pullˡ inject₂ ○ assoc)
    ; F-resp-≈ = λ eq → []-cong₂ refl (∘-resp-≈ʳ eq)
    }

  private
    module Maybe = Functor Maybe

  Initial⇒NNO : Initial (F-Algebras Maybe) → NaturalNumber
  Initial⇒NNO initial = record
    { N = ⊥.A
    ; isNaturalNumber = record
      { z = ⊥.α ∘ i₁
      ; s = ⊥.α ∘ i₂
      ; universal = λ {A} q f →
        F-Algebra-Morphism.f (initial.! {A = alg q f})
      ; z-commute = λ {A} {q} {f} → begin
        q                                                                 ≈⟨ ⟺ inject₁ ⟩
        [ q , f ] ∘ i₁                                                    ≈⟨ pushʳ (⟺ inject₁) ⟩
        (([ q , f ] ∘ [ i₁ , i₂ ∘ F-Algebra-Morphism.f initial.! ]) ∘ i₁) ≈⟨ pushˡ (⟺ (F-Algebra-Morphism.commutes (initial.! {A = alg q f}))) ⟩
        F-Algebra-Morphism.f initial.! ∘ ⊥.α ∘ i₁                         ∎
      ; s-commute = λ {A} {q} {f} → begin
        (f ∘ F-Algebra-Morphism.f initial.!)                            ≈⟨ pushˡ (⟺ inject₂) ⟩
        [ q , f ] ∘ i₂ ∘ F-Algebra-Morphism.f initial.!                 ≈⟨ pushʳ (⟺ inject₂) ⟩
        ([ q , f ] ∘ [ i₁ , i₂ ∘ F-Algebra-Morphism.f initial.! ]) ∘ i₂ ≈⟨ pushˡ (⟺ (F-Algebra-Morphism.commutes (initial.! {A = alg q f}))) ⟩
        F-Algebra-Morphism.f initial.! ∘ ⊥.α ∘ i₂                       ∎
      ; unique = λ {A} {f} {q} {u} eqᶻ eqˢ → ⟺ $ initial.!-unique record
          { f = u
          ; commutes = begin
            u ∘ ⊥.α ≈⟨ ⟺ +-g-η ⟩
            [ (u ∘ ⊥.α) ∘ i₁ , (u ∘ ⊥.α) ∘ i₂ ] ≈⟨ []-cong₂ (assoc ○ ⟺ eqᶻ) (assoc ○ ⟺ eqˢ) ⟩
            [ f , q ∘ u ]                       ≈⟨ +-unique (pullʳ inject₁ ○ inject₁) (pullʳ inject₂ ○ pullˡ inject₂) ⟩
            [ f , q ] ∘ [ i₁ , i₂ ∘ u ]         ∎
          }
      }
    }
    where
      module initial = Initial initial
      module ⊥ = F-Algebra initial.⊥
  
      alg : ∀ {A} → (q : ⊤ ⇒ A) → (f : A ⇒ A) → F-Algebra Maybe
      alg {A} q f = record
        { A = A
        ; α = [ q , f ]
        }

  NNO⇒Initial : NaturalNumber → Initial (F-Algebras Maybe)
  NNO⇒Initial NNO = record
    { ⊥ = record
      { A = N 
      ; α = [ z , s ]
      }
    ; ⊥-is-initial = record
      { ! = λ {alg} → record
        { f = universal (F-Algebra.α alg ∘ i₁) (F-Algebra.α alg ∘ i₂)
        ; commutes = begin
          universal _ _ ∘ [ z , s ]                                         ≈⟨ ∘-distribˡ-[] ⟩
          [ universal _ _ ∘ z , universal _ _ ∘ s ]                         ≈⟨ []-cong₂ (⟺ z-commute) (⟺ s-commute ○ assoc) ⟩
          [ F-Algebra.α alg ∘ i₁ , F-Algebra.α alg ∘ (i₂ ∘ universal _ _) ] ≈˘⟨ ∘-distribˡ-[] ⟩
          F-Algebra.α alg ∘ [ i₁ , i₂ ∘ universal _ _ ]                     ∎
        }
      ; !-unique = λ {A} f →
        let z-commutes = begin
              F-Algebra.α A ∘ i₁                                          ≈⟨ pushʳ (⟺ inject₁) ⟩
              (F-Algebra.α A ∘ [ i₁ , i₂ ∘ F-Algebra-Morphism.f f ]) ∘ i₁ ≈˘⟨ F-Algebra-Morphism.commutes f ⟩∘⟨refl ⟩
              (F-Algebra-Morphism.f f ∘ [ z , s ]) ∘ i₁                   ≈⟨ pullʳ inject₁ ⟩
              F-Algebra-Morphism.f f ∘ z                                  ∎
            s-commutes = begin
              (F-Algebra.α A ∘ i₂) ∘ F-Algebra-Morphism.f f               ≈⟨ pullʳ (⟺ inject₂) ○ ⟺ assoc ⟩
              (F-Algebra.α A ∘ [ i₁ , i₂ ∘ F-Algebra-Morphism.f f ]) ∘ i₂ ≈˘⟨ F-Algebra-Morphism.commutes f ⟩∘⟨refl ⟩
              (F-Algebra-Morphism.f f ∘ [ z , s ]) ∘ i₂                   ≈⟨ pullʳ inject₂ ⟩
              F-Algebra-Morphism.f f ∘ s                                  ∎
        in ⟺ $ unique z-commutes s-commutes
      }
    }
    where
      open NaturalNumber NNO

-- A parametrized NNO is an initial algebra for the 'X ↦ A + X' endofunctor.
module _ {o ℓ e} (CC : CartesianCategory o ℓ e) (𝒞-Coproducts : BinaryCoproducts (CartesianCategory.U CC)) where
  open CartesianCategory CC renaming (U to 𝒞)
  open BinaryCoproducts 𝒞-Coproducts
  open BinaryProducts products hiding (unique)
  open HomReasoning
  open Equiv
  open MR 𝒞
  open PNNO CC
  open NNO 𝒞 terminal
  open Terminal terminal

  coproductF : Obj → Endofunctor 𝒞
  coproductF A = record
    { F₀ = λ X → A + X
    ; F₁ = λ f → [ i₁ , (i₂ ∘ f) ]
    ; identity = λ {A} → trans ([]-congˡ identityʳ) 
                               (coproduct.unique identityˡ identityˡ) 
    ; homomorphism = λ {X} {Y} {Z} {f} {g} → coproduct.unique 
      (trans (pullʳ inject₁) (inject₁)) 
      (trans (pullʳ inject₂) (trans (pullˡ inject₂) assoc))
    ; F-resp-≈ = λ fg → []-congˡ (∘-resp-≈ʳ fg)
    }

  private
    module coproductF A = Functor (coproductF A)

  algeb : ∀ A → Initial (F-Algebras (Maybe 𝒞 terminal 𝒞-Coproducts)) → F-Algebra (coproductF A)
  algeb A initial = record 
    { A = A × ⊥.A 
    ; α = [ ⟨ id , (⊥.α ∘ i₁) ∘ ! ⟩ , id ⁂ (⊥.α ∘ i₂) ] 
    }
    where 
      module initial = Initial initial
      module ⊥ = F-Algebra initial.⊥

  Initial⇒PNNO : (initial : Initial (F-Algebras (Maybe 𝒞 terminal 𝒞-Coproducts))) → (∀ A → IsInitial (F-Algebras (coproductF A)) (algeb A initial)) → ParametrizedNaturalNumber
  Initial⇒PNNO initial isInitial = record 
    { N = N
    ; isParametrizedNaturalNumber = record
      { z = z
      ; s = s
      ; universal = λ {A} {X} f g → F-Algebra-Morphism.f (isInitial.! A {A = alg′ f g})
      ; commute₁ = λ {A} {X} {f} {g} → begin 
        f                                                                          ≈˘⟨ inject₁ ⟩ 
        [ f , g ] ∘ i₁                                                             ≈⟨ pushʳ (⟺ inject₁) ⟩
        (([ f , g ] ∘ [ i₁ , i₂ ∘ F-Algebra-Morphism.f (isInitial.! A) ]) ∘ i₁)    ≈⟨ pushˡ (⟺ (F-Algebra-Morphism.commutes (isInitial.! A {A = alg′ f g}))) ⟩
        (F-Algebra-Morphism.f (isInitial.! A) ∘ [ ⟨ id , z ∘ ! ⟩ , id ⁂ s ] ∘  i₁) ≈⟨ refl⟩∘⟨ inject₁ ⟩
        (F-Algebra-Morphism.f (IsInitial.! (isInitial A))) ∘ ⟨ id , z ∘ ! ⟩        ∎
      ; commute₂ = λ {A} {X} {f} {g} → begin 
        g ∘ F-Algebra-Morphism.f (IsInitial.! (isInitial A))                                ≈⟨ pushˡ (⟺ inject₂) ⟩ 
        [ f , g ] ∘ i₂ ∘ F-Algebra-Morphism.f (IsInitial.! (isInitial A))                   ≈⟨ pushʳ (⟺ inject₂) ⟩
        (([ f , g ] ∘ [ i₁ , i₂ ∘ F-Algebra-Morphism.f (IsInitial.! (isInitial A)) ]) ∘ i₂) ≈⟨ pushˡ (⟺ (F-Algebra-Morphism.commutes (isInitial.! A {A = alg′ f g}))) ⟩
        (F-Algebra-Morphism.f (isInitial.! A) ∘ [ ⟨ id , z ∘ ! ⟩ , id ⁂ s ] ∘  i₂)          ≈⟨ (refl⟩∘⟨ inject₂) ⟩
        F-Algebra-Morphism.f (IsInitial.! (isInitial A)) ∘ (id ⁂ s)                         ∎
      ; unique = λ {A} {X} {f} {g} {u} eqᶻ eqˢ → ⟺ $ isInitial.!-unique A {A = alg′ f g} (record 
        { f = u 
        ; commutes = begin 
          u ∘ [ ⟨ id , z ∘ ! ⟩ , id ⁂ s ]                                                         ≈⟨ ⟺ +-g-η ⟩ 
          [ ((u ∘ [ ⟨ id , z ∘ ! ⟩ , id ⁂ s ]) ∘ i₁) , ((u ∘ [ ⟨ id , z ∘ ! ⟩ , id ⁂ s ]) ∘ i₂) ] ≈⟨ []-cong₂ (pullʳ inject₁) (pullʳ inject₂) ⟩ 
          [ u ∘ ⟨ id , z ∘ ! ⟩ , u ∘ (id ⁂ s) ]                                                   ≈˘⟨ []-cong₂ eqᶻ eqˢ ⟩ 
          [ f , g ∘ u ]                                                                           ≈⟨ +-unique (pullʳ inject₁ ○ inject₁) (pullʳ inject₂ ○ pullˡ inject₂) ⟩ 
          [ f , g ] ∘ [ i₁ , i₂ ∘ u ]                                                             ∎ 
        })
      } 
    }
    where
      module initial = Initial initial
      module ⊥ = F-Algebra initial.⊥
      module isInitial A = IsInitial (isInitial A)
      open NaturalNumber (Initial⇒NNO 𝒞 terminal 𝒞-Coproducts initial)

      alg′  : ∀ {A X} → (f : A ⇒ X) → (g : X ⇒ X) → F-Algebra (coproductF A)
      alg′ {A} {X} f g = record 
        { A = X 
        ; α = [ f , g ] 
        }

  PNNO⇒Initial₁ : ParametrizedNaturalNumber → Initial (F-Algebras (Maybe 𝒞 terminal 𝒞-Coproducts))
  PNNO⇒Initial₁ pnno = (NNO⇒Initial 𝒞 terminal 𝒞-Coproducts) (PNNO⇒NNO pnno)

-- TODO fix definition to use IsInitial
  -- every PNNO is also a NNO (the other direction only holds in CCCs)
  PNNO⇒Initial₂ : ParametrizedNaturalNumber → (∀ A → Initial (F-Algebras (coproductF A)))
  PNNO⇒Initial₂ pnno A = record 
    { ⊥ = record 
      { A = A × N 
      ; α = [ ⟨ id , z ∘ ! ⟩ , id ⁂ s ] 
      } 
    ; ⊥-is-initial = record 
      { ! = λ {alg} → record 
        { f = universal (F-Algebra.α alg ∘ i₁) (F-Algebra.α alg ∘ i₂) 
        ; commutes = begin 
          universal _ _ ∘ [ ⟨ id , z ∘ ! ⟩ , id ⁂ s ]                         ≈⟨ ∘-distribˡ-[] ⟩ 
          [ universal _ _ ∘ ⟨ id , z ∘ ! ⟩ , universal _ _ ∘ (id ⁂ s) ]       ≈⟨ []-cong₂ (⟺ commute₁) (⟺ commute₂) ⟩
          [ F-Algebra.α alg ∘ i₁ , ((F-Algebra.α alg ∘ i₂) ∘ universal _ _) ] ≈˘⟨ trans ∘-distribˡ-[] ([]-congˡ sym-assoc) ⟩
          F-Algebra.α alg ∘ [ i₁ , i₂ ∘ universal _ _ ]                       ∎ 
        } 
      ; !-unique = λ {X} f → 
        let commute₁ = begin 
              F-Algebra.α X ∘ i₁ ≈⟨ pushʳ (⟺ inject₁) ⟩ 
              ((F-Algebra.α X ∘ [ i₁ , i₂ ∘ F-Algebra-Morphism.f f ]) ∘ i₁) ≈˘⟨ F-Algebra-Morphism.commutes f ⟩∘⟨refl ⟩
              ((F-Algebra-Morphism.f f ∘ [ ⟨ id , z ∘ ! ⟩ , id ⁂ s ]) ∘ i₁) ≈⟨ pullʳ inject₁ ⟩
              F-Algebra-Morphism.f f ∘ ⟨ id , z ∘ ! ⟩ ∎
            commute₂ = begin 
              (F-Algebra.α X ∘ i₂) ∘ F-Algebra-Morphism.f f ≈⟨ (pullʳ (⟺ inject₂) ○ ⟺ assoc) ⟩ 
              ((F-Algebra.α X ∘ [ i₁ , i₂ ∘ F-Algebra-Morphism.f f ]) ∘ i₂) ≈˘⟨ F-Algebra-Morphism.commutes f ⟩∘⟨refl ⟩
              ((F-Algebra-Morphism.f f ∘ [ ⟨ id , z ∘ ! ⟩ , id ⁂ s ]) ∘ i₂) ≈⟨ pullʳ inject₂ ⟩
              F-Algebra-Morphism.f f ∘ (id ⁂ s) ∎
        in ⟺ $ unique commute₁ commute₂
      } 
    }
    where
      open ParametrizedNaturalNumber pnno

  