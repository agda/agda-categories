open import Level
open import Categories.Category.Core
open import Categories.Object.Terminal using (Terminal)
open import Categories.Category.Cocartesian using (BinaryCoproducts)
open import Categories.Category.Cartesian using (Cartesian)

-- A parametrized NNO corresponds to existence of a (⊤ + (-)) algebra and initiality of the PNNO algebra
module Categories.Object.NaturalNumbers.Parametrized.Properties.F-Algebras {o ℓ e} (𝒞 : Category o ℓ e) (𝒞-Cartesian : Cartesian 𝒞) (𝒞-Coproducts : BinaryCoproducts 𝒞) where

open import Function using (_$_)

open import Categories.Category.Construction.F-Algebras using (F-Algebras)
open import Categories.Functor.Algebra using (F-Algebra; F-Algebra-Morphism)
open import Categories.Object.Initial using (Initial; IsInitial)
open import Categories.Category.BinaryProducts using (BinaryProducts)

import Categories.Morphism.Reasoning as MR

open Category 𝒞
open BinaryCoproducts 𝒞-Coproducts
open Cartesian 𝒞-Cartesian
open HomReasoning
open Equiv
open MR 𝒞
open BinaryProducts products
open Terminal terminal

open import Categories.Object.NaturalNumbers.Parametrized 𝒞 𝒞-Cartesian
open import Categories.Object.NaturalNumbers.Properties.F-Algebras 𝒞 terminal 𝒞-Coproducts

-- the algebra that corresponds to a PNNO (if it is initial)
PNNO-Algebra : ∀ A N → ⊤ ⇒ N → N ⇒ N → F-Algebra (A +-)
PNNO-Algebra A N z s = record
  { A = A × N
  ; α = [ ⟨ id , z ∘ ! ⟩ , id ⁂ s ] 
  }

Initial⇒PNNO : (algebra : F-Algebra (⊤ +-)) 
  → (∀ A → IsInitial (F-Algebras (A +-)) 
                      (PNNO-Algebra A (F-Algebra.A algebra) (F-Algebra.α algebra ∘ i₁) (F-Algebra.α algebra ∘ i₂))) 
  → ParametrizedNNO
Initial⇒PNNO algebra isInitial = record 
  { N = N
  ; isParametrizedNNO = record
    { z = z
    ; s = s
    ; universal = λ {A} {X} f g → F-Algebra-Morphism.f (isInitial.! A {A = alg′ f g})
    ; commute₁ = λ {A} {X} {f} {g} → begin 
      f                                                                       ≈˘⟨ inject₁ ⟩ 
      [ f , g ] ∘ i₁                                                          ≈˘⟨ refl⟩∘⟨ (+₁∘i₁ ○ identityʳ) ⟩ 
      [ f , g ] ∘ (id +₁ F-Algebra-Morphism.f (isInitial.! A)) ∘ i₁           ≈˘⟨ extendʳ (F-Algebra-Morphism.commutes (isInitial.! A {A = alg′ f g})) ⟩ 
      F-Algebra-Morphism.f (isInitial.! A) ∘ [ ⟨ id , z ∘ ! ⟩ , id ⁂ s ] ∘ i₁ ≈⟨ refl⟩∘⟨ inject₁ ⟩ 
      (F-Algebra-Morphism.f (IsInitial.! (isInitial A))) ∘ ⟨ id , z ∘ ! ⟩     ∎
    ; commute₂ = λ {A} {X} {f} {g} → begin 
      g ∘ F-Algebra-Morphism.f (IsInitial.! (isInitial A))                      ≈˘⟨ pullˡ inject₂ ⟩ 
      [ f , g ] ∘ i₂ ∘ F-Algebra-Morphism.f (IsInitial.! (isInitial A))         ≈˘⟨ refl⟩∘⟨ +₁∘i₂ ⟩ 
      [ f , g ] ∘ (id +₁ F-Algebra-Morphism.f (IsInitial.! (isInitial A))) ∘ i₂ ≈˘⟨ extendʳ (F-Algebra-Morphism.commutes (isInitial.! A {A = alg′ f g})) ⟩ 
      F-Algebra-Morphism.f (isInitial.! A) ∘ [ ⟨ id , z ∘ ! ⟩ , id ⁂ s ] ∘  i₂  ≈⟨ refl⟩∘⟨ inject₂ ⟩ 
      F-Algebra-Morphism.f (IsInitial.! (isInitial A)) ∘ (id ⁂ s)               ∎
    ; unique = λ {A} {X} {f} {g} {u} eqᶻ eqˢ → ⟺ $ isInitial.!-unique A {A = alg′ f g} (record 
      { f = u 
      ; commutes = begin 
        u ∘ [ ⟨ id , z ∘ ! ⟩ , id ⁂ s ]              ≈˘⟨ +-g-η ⟩ 
        [ ((u ∘ [ ⟨ id , z ∘ ! ⟩ , id ⁂ s ]) ∘ i₁) 
        , ((u ∘ [ ⟨ id , z ∘ ! ⟩ , id ⁂ s ]) ∘ i₂) ] ≈⟨ []-cong₂ (pullʳ inject₁) (pullʳ inject₂) ⟩ 
        [ u ∘ ⟨ id , z ∘ ! ⟩ , u ∘ (id ⁂ s) ]        ≈˘⟨ []-cong₂ eqᶻ eqˢ ⟩ 
        [ f , g ∘ u ]                                ≈˘⟨ []∘+₁ ○ []-cong₂ identityʳ refl ⟩ 
        [ f , g ] ∘ (id +₁ u)                        ∎ 
      })
    } 
  }
  where
    open F-Algebra algebra using (α) renaming (A to N)
    z = α ∘ i₁
    s = α ∘ i₂

    module isInitial A = IsInitial (isInitial A)

    alg′  : ∀ {A X} → (f : A ⇒ X) → (g : X ⇒ X) → F-Algebra (A +-)
    alg′ {A} {X} f g = record 
      { A = X 
      ; α = [ f , g ] 
      }

PNNO⇒Initial₁ : ParametrizedNNO → Initial (F-Algebras (⊤ +-))
PNNO⇒Initial₁ pnno = NNO⇒Initial (PNNO⇒NNO pnno)

PNNO⇒Initial₂ : (pnno : ParametrizedNNO)
  → (∀ A → IsInitial (F-Algebras (A +-)) 
                      (PNNO-Algebra A (ParametrizedNNO.N pnno) (ParametrizedNNO.z pnno) (ParametrizedNNO.s pnno)))
PNNO⇒Initial₂ pnno A = record 
  { ! = λ {alg} → record 
    { f = universal (F-Algebra.α alg ∘ i₁) (F-Algebra.α alg ∘ i₂) 
    ; commutes = begin 
      universal (F-Algebra.α alg ∘ i₁) (F-Algebra.α alg ∘ i₂) ∘ [ ⟨ id , z ∘ ! ⟩ , id ⁂ s ]  ≈⟨ ∘[] ⟩ 
      [ universal (F-Algebra.α alg ∘ i₁) (F-Algebra.α alg ∘ i₂) ∘ ⟨ id , z ∘ ! ⟩ 
      , universal (F-Algebra.α alg ∘ i₁) (F-Algebra.α alg ∘ i₂) ∘ (id ⁂ s) ]                 ≈˘⟨ []-cong₂ pnno.commute₁ pnno.commute₂ ⟩ 
      [ F-Algebra.α alg ∘ i₁ 
      , ((F-Algebra.α alg ∘ i₂) ∘ universal (F-Algebra.α alg ∘ i₁) (F-Algebra.α alg ∘ i₂)) ] ≈˘⟨ ∘[] ○ []-cong₂ (∘-resp-≈ʳ identityʳ) sym-assoc ⟩ 
      F-Algebra.α alg ∘ (id +₁ universal (F-Algebra.α alg ∘ i₁) (F-Algebra.α alg ∘ i₂))      ∎
    } 
  ; !-unique = λ {X} f → 
    let commute₁ = begin 
          F-Algebra.α X ∘ i₁                                        ≈˘⟨ refl⟩∘⟨ (+₁∘i₁ ○ identityʳ) ⟩ 
          F-Algebra.α X ∘ (id +₁ F-Algebra-Morphism.f f) ∘ i₁       ≈˘⟨ extendʳ (F-Algebra-Morphism.commutes f) ⟩ 
          F-Algebra-Morphism.f f ∘ [ ⟨ id , z ∘ ! ⟩ , id ⁂ s ] ∘ i₁ ≈⟨ refl⟩∘⟨ inject₁ ⟩ 
          F-Algebra-Morphism.f f ∘ ⟨ id , z ∘ ! ⟩                   ∎
        commute₂ = begin 
          (F-Algebra.α X ∘ i₂) ∘ F-Algebra-Morphism.f f             ≈⟨ pullʳ $ ⟺ +₁∘i₂ ⟩ 
          F-Algebra.α X ∘ (id +₁ F-Algebra-Morphism.f f) ∘ i₂       ≈˘⟨ extendʳ (F-Algebra-Morphism.commutes f) ⟩ 
          F-Algebra-Morphism.f f ∘ [ ⟨ id , z ∘ ! ⟩ , id ⁂ s ] ∘ i₂ ≈⟨ refl⟩∘⟨ inject₂ ⟩ 
          F-Algebra-Morphism.f f ∘ (id ⁂ s)                         ∎
    in ⟺ $ pnno.unique commute₁ commute₂
  }
  where
    open ParametrizedNNO pnno using (s ; z ; universal)
    module pnno = ParametrizedNNO pnno