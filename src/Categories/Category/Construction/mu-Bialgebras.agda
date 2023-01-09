{-# OPTIONS --without-K --safe #-}
module Categories.Category.Construction.mu-Bialgebras where

open import Level
open import Function using (_$_)

open import Categories.Category
open import Categories.Functor hiding (id)
open import Categories.Functor.Algebra
open import Categories.Functor.Coalgebra
import Categories.Morphism.Reasoning as MR
open import Categories.Functor.Bialgebra
open import Categories.Category.Construction.F-Algebras
open import Categories.Category.Construction.F-Coalgebras
open import Categories.Functor.DistributiveLaw using (DistributiveLaw)
open import Categories.Functor.Construction.LiftAlgebras using (LiftAlgebras)

open import Categories.Category.Equivalence using (StrongEquivalence;WeakInverse)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism;NIHelper;niHelper)
open import Categories.NaturalTransformation using (NTHelper;ntHelper)

private
  variable
    o ℓ e : Level

module _ {C : Category o ℓ e} (T F : Endofunctor C) (μ : DistributiveLaw T F) where
  open Category C
  open MR C
  open HomReasoning
  open Equiv

  μ-Bialgebras : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
  μ-Bialgebras = record
   { Obj       = μ-Bialgebra T F μ
   ; _⇒_       = μ-Bialgebra-Morphism
   ; _≈_       = λ β₁ β₂ → f β₁ ≈ f β₂
   ; _∘_       = λ β₁ β₂ → record
     { f                = f β₁ ∘ f β₂
     ; f-is-alg-morph   =
       F-Algebra-Morphism.commutes $
         (alg-morph β₁) T-Algebras.∘ (alg-morph β₂)
     ; f-is-coalg-morph = F-Coalgebra-Morphism.commutes $
       (coalg-morph β₁) F-Coalgebras.∘ (coalg-morph β₂)
     }
   ; id        = record
     { f = id
     ; f-is-alg-morph   =  F-Algebra-Morphism.commutes (T-Algebras.id)
     ; f-is-coalg-morph =  F-Coalgebra-Morphism.commutes (F-Coalgebras.id)
     }
   ; assoc     = assoc
   ; sym-assoc = sym-assoc
   ; identityˡ = identityˡ
   ; identityʳ = identityʳ
   ; identity² = identity²
   ; equiv     = record
     { refl  = refl
     ; sym   = sym
     ; trans = trans
     }
   ; ∘-resp-≈  = ∘-resp-≈
   }
     where
      open μ-Bialgebra-Morphism
      open μ-Bialgebra
      module T-Algebras = Category (F-Algebras T)
      module F-Coalgebras = Category (F-Coalgebras F)
      open Functor F
      open F-Coalgebra-Morphism
      open F-Coalgebra

  μ-Bialgebras⇒CoalgebrasLiftAlgebrasF : Functor μ-Bialgebras (F-Coalgebras (LiftAlgebras T F μ))
  μ-Bialgebras⇒CoalgebrasLiftAlgebrasF = record
    { F₀           = λ X → record { A = alg X ; α = record { f = c₁ X ; commutes = respects-μ X ○ sym-assoc } }
    ; F₁           = λ {X Y} β → record
      { f = alg-morph β
      ; commutes = F-Coalgebra-Morphism.commutes (coalg-morph β)
      }
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = λ x → x
    }
    where
      open μ-Bialgebra
      open Functor F
      open μ-Bialgebra-Morphism

  CoalgebrasLiftAlgebrasF⇒μ-Bialgebras : Functor (F-Coalgebras (LiftAlgebras T F μ)) μ-Bialgebras
  CoalgebrasLiftAlgebrasF⇒μ-Bialgebras = record
    { F₀           = λ X → record
      { A = F-Algebra.A (F-Coalgebra.A X)
      ; a₁ = F-Algebra.α (F-Coalgebra.A X)
      ; c₁ = F-Algebra-Morphism.f (F-Coalgebra.α X)
      ; respects-μ = F-Algebra-Morphism.commutes (F-Coalgebra.α X) ○ assoc
      }
    ; F₁           = λ {X Y} β → record
      { f = F-Algebra-Morphism.f (F-Coalgebra-Morphism.f β)
      ; f-is-alg-morph = F-Algebra-Morphism.commutes (F-Coalgebra-Morphism.f β)
      ; f-is-coalg-morph = F-Coalgebra-Morphism.commutes β
      }
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = λ x → x
    }

  μ-Bialgebras⇔CoalgebrasLiftAlgebrasF : StrongEquivalence μ-Bialgebras (F-Coalgebras (LiftAlgebras T F μ))
  μ-Bialgebras⇔CoalgebrasLiftAlgebrasF = record
    { F = μ-Bialgebras⇒CoalgebrasLiftAlgebrasF
    ; G = CoalgebrasLiftAlgebrasF⇒μ-Bialgebras
    ; weak-inverse = record
      { F∘G≈id = niHelper record
        { η = λ X → record
          { f = T-Algebras.id
          ; commutes = commut X
          }
        ; η⁻¹ = λ X → record
          { f = T-Algebras.id
          ; commutes = commut X
          }
        ; commute = λ _ → id-comm-sym
        ; iso = λ _ → record { isoˡ = identity² ; isoʳ = identity² }
        }
      ; G∘F≈id = niHelper record
        { η = λ X → record
          { f = id
          ; f-is-alg-morph = F-Algebra-Morphism.commutes T-Algebras.id
          ; f-is-coalg-morph = F-Coalgebra-Morphism.commutes F-Coalgebras.id
          }
        ; η⁻¹ = λ X → record
          { f = id
          ; f-is-alg-morph = F-Algebra-Morphism.commutes T-Algebras.id
          ; f-is-coalg-morph = F-Coalgebra-Morphism.commutes F-Coalgebras.id
          }
        ; commute = λ _ → id-comm-sym
        ; iso = λ _ → record { isoˡ = identity² ; isoʳ = identity² }
        }
      }
    }
    where
      open Functor F using (F₁;identity)
      module T-Algebras = Category (F-Algebras T)
      module F-Coalgebras = Category (F-Coalgebras F)
      commut = λ X →
            let c = F-Algebra-Morphism.f (F-Coalgebra.α X) in begin
              c ∘ id ≈⟨ identityʳ ⟩
              c ≈⟨ ⟺ identityˡ ⟩
              id ∘ c ≈⟨ ∘-resp-≈ˡ (⟺ identity)⟩
              F₁ id ∘ c ∎
