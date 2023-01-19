{-# OPTIONS --without-K --safe #-}
open import Categories.Category
open import Categories.Functor hiding (id)
open import Categories.Functor.DistributiveLaw using (DistributiveLaw)

module Categories.Category.Construction.mu-Bialgebras {o ℓ e} {C : Category o ℓ e} (T F : Endofunctor C) (μ : DistributiveLaw T F) where

open import Level
open import Function using (_$_)

open import Categories.Functor.Algebra
open import Categories.Functor.Coalgebra
import Categories.Morphism.Reasoning as MR
open import Categories.Functor.Bialgebra
open import Categories.Category.Construction.F-Algebras
open import Categories.Category.Construction.F-Coalgebras
open import Categories.Functor.Construction.LiftAlgebras using (LiftAlgebras;liftInitial)
open import Categories.Functor.Construction.LiftCoalgebras using (LiftCoalgebras;liftTerminal)

open import Categories.Category.Equivalence using (StrongEquivalence;WeakInverse)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism;NIHelper;niHelper)
open import Categories.NaturalTransformation using (NaturalTransformation;NTHelper;ntHelper)

open import Categories.Object.Initial
open import Categories.Object.Terminal

{-
See also comment in `Categories.Functor.Bialgebra`.
μ-Bialgebras is the category of T-F-μ Bialgebras. T is the functor
which provides the algebraic structure, whereas F provides the
coalgebraic structure.
In addition to the explicit construction of μ-Bialgebras given in this
module there are two other ways to construct this:

  We can lift F via μ to the category of T-Algebras (see
`Categories.Functor.Construction.LiftAlgebras`), giving us the
functor:
  F̂ : T-Algebras → T-Algebras.
  Dually we can lift T via μ to the category of F-Coalgebras (see
`Categories.Functor.Construction.LiftCoalgebras`), giving us the
functor:
  T̂ : F-Coalgebra → F-Coalgebras

Then the categories of F̂-Coalgebras and T̂-Algebras are two other ways
of constructing the category μ-Bialgebras.  We show here that these
three constructions are equivalent.

We see in the above modules that initial T-Algebras may be lifted to
initial F̂-Coalgebras, and terminal F-Coalgebras to terminal
T̂-Algebras. In this module we prove what I (CA) call the "central
theorem" of bialgebras: That the bialgebra-maps from a lifted initial
T-Algebra to a lifted final F-Algebra by ititiality and finality are
equal.

A good theoretical reference work for the theories:
[On generalised coinduction and probabilistic specification formats:
Distributive laws in coalgebraic modelling — Vrije Universiteit
Amsterdam (Bartels, 2004)]
(https://research.vu.nl/en/publications/on-generalised-coinduction-and-probabilistic-specification-format-2)
Starting at Definition 3.2.2
-}


module _ where
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

-- begin Bialgs≅Coalgs(F̂)

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

-- end Bialgs≅Coalgs(F̂)
-- begin Coalgs(F̂)≅Algs(T̂)

  AlgebrasT̂⇒CoalgebrasF̂ : Functor (F-Algebras (LiftCoalgebras T F μ)) (F-Coalgebras (LiftAlgebras T F μ))
  AlgebrasT̂⇒CoalgebrasF̂ = record
      { F₀           = λ X → record
        { A = to-Algebra $ F-Coalgebra-Morphism.f $ F-Algebra.α X
        ; α = record
          { f = F-Coalgebra.α $ F-Algebra.A X
          ; commutes = F-Coalgebra-Morphism.commutes (F-Algebra.α X) ○ sym-assoc
          }
        }
      ; F₁           = λ {X Y} β → record
        { f = record
          { f = F-Coalgebra-Morphism.f $ F-Algebra-Morphism.f β
          ; commutes = F-Algebra-Morphism.commutes β
          }
        ; commutes = F-Coalgebra-Morphism.commutes $ F-Algebra-Morphism.f β
        }
      ; identity     = refl
      ; homomorphism = refl
      ; F-resp-≈     = λ x → x
      }

  CoalgebrasF̂⇒AlgebrasT̂ : Functor (F-Coalgebras (LiftAlgebras T F μ)) (F-Algebras (LiftCoalgebras T F μ))
  CoalgebrasF̂⇒AlgebrasT̂ = record
      { F₀           = λ X → record
        { A = to-Coalgebra $ F-Algebra-Morphism.f $ F-Coalgebra.α X
        ; α = record
          { f = F-Algebra.α $ F-Coalgebra.A X
          ; commutes = F-Algebra-Morphism.commutes (F-Coalgebra.α X) ○ assoc
          }
        }
      ; F₁           = λ {X Y} β → record
        { f = record
          { f = F-Algebra-Morphism.f $ F-Coalgebra-Morphism.f β
          ; commutes = F-Coalgebra-Morphism.commutes β
          }
        ; commutes = F-Algebra-Morphism.commutes $ F-Coalgebra-Morphism.f β
        }
      ; identity     = refl
      ; homomorphism = refl
      ; F-resp-≈     = λ x → x
      }

  CoalgebrasF̂⇔AlgebrasT̂ : StrongEquivalence (F-Coalgebras (LiftAlgebras T F μ)) (F-Algebras (LiftCoalgebras T F μ))
  CoalgebrasF̂⇔AlgebrasT̂ = record
    { F = CoalgebrasF̂⇒AlgebrasT̂ -- C2A
    ; G = AlgebrasT̂⇒CoalgebrasF̂ -- A2C
    ; weak-inverse = record
      { F∘G≈id = niHelper record --F∘G = C2A ∘ A2C thus `id` in C
      -- it may look like we can use T̂-Algs.id here, but we can't because of objects being unequal
        { η = λ X → record
          { f = record { f = id ; commutes = F-Coalgebra-Morphism.commutes F-Coalgebras.id }
          ; commutes = F-Algebra-Morphism.commutes T-Algebras.id
          }
        ; η⁻¹ = λ X → record
          { f = record
            { f = id ; commutes = F-Coalgebra-Morphism.commutes F-Coalgebras.id }
          ; commutes = F-Algebra-Morphism.commutes T-Algebras.id
          }
        ; commute = λ _ → id-comm-sym
        ; iso = λ _ → record { isoˡ = identity² ; isoʳ = identity² }
        }
      ; G∘F≈id = niHelper record
        { η = λ X → record
          { f = record
            { f = id ; commutes = F-Algebra-Morphism.commutes T-Algebras.id }
          ; commutes = F-Coalgebra-Morphism.commutes F-Coalgebras.id
          }
        ; η⁻¹ = λ X → record
            { f = record
              { f = id ; commutes = F-Algebra-Morphism.commutes T-Algebras.id }
            ; commutes = F-Coalgebra-Morphism.commutes F-Coalgebras.id
            }
        ; commute = λ _ → id-comm-sym
        ; iso = λ _ → record { isoˡ = identity² ; isoʳ = identity² }
        }
      }
    }
    where
      module T-Algebras = Category (F-Algebras T)
      module F-Coalgebras = Category (F-Coalgebras F)

-- end Coalgs(F̂)≅Algs(T̂)

module _ (μT : Initial (F-Algebras T)) (νF : Terminal (F-Coalgebras F)) where
  open Functor
  open Initial (liftInitial T F μ μT)
  open Terminal (liftTerminal T F μ νF)
  open Category (F-Coalgebras (LiftAlgebras T F μ))
  open StrongEquivalence CoalgebrasF̂⇔AlgebrasT̂
  private
    module μT̂ = IsInitial ⊥-is-initial
    module νF̂ = IsTerminal ⊤-is-terminal
    A2C = AlgebrasT̂⇒CoalgebrasF̂
    C2A = CoalgebrasF̂⇒AlgebrasT̂
    id⇒A2C∘C2A : ∀ ( X : Obj ) → X ⇒ ((A2C ∘F C2A) .F₀ X)
    id⇒A2C∘C2A X = G∘F≈id.⇐.η X

  -- implicit args to `!` supplied here for clarity
  centralTheorem : μT̂.! {A = A2C .F₀ ⊤} ≈ A2C. F₁ (νF̂.! {A = C2A .F₀ ⊥}) ∘ id⇒A2C∘C2A ⊥
  centralTheorem = μT̂.!-unique (A2C. F₁ νF̂.! ∘ id⇒A2C∘C2A ⊥)
