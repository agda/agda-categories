{-# OPTIONS --without-K --safe #-}

-- Categorical equivalences preserve various structures

module Categories.Category.Equivalence.Preserves where

open import Level

open import Categories.Adjoint.Equivalence using (⊣Equivalence)
open import Categories.Category.Core
open import Categories.Category.Equivalence using (WeakInverse; StrongEquivalence)
open import Categories.Category.Equivalence.Properties using (C≅D)
open import Categories.Diagram.Duality
open import Categories.Functor.Core
open import Categories.Morphism
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation.NaturalIsomorphism.Properties
open import Categories.Object.Initial
open import Categories.Object.Terminal
open import Categories.Object.Duality

private
  variable
    o ℓ e o′ ℓ′ e′ : Level
    C : Category o ℓ e
    D : Category o′ ℓ′ e′

module _ (S : StrongEquivalence C D) where
  open StrongEquivalence S
  open IsInitial
  private
    module C = Category C
    module D = Category D
    module F = Functor F
    module G = Functor G
    X : ⊣Equivalence C D
    X = C≅D S

  -- see below the proof for the abbreviations that make the proof readable
  pres-IsInitial : {c : C.Obj} (i : IsInitial C c) → IsInitial D (F.₀ c)
  pres-IsInitial {c} i = record
    { ! = λ {A} →  F∘G≈id.⇒.η A D.∘ F.₁ (! i)
    ; !-unique = λ {A} f → begin  {- f : F.₀ c D.⇒ A -}
      FG⇒ A D.∘ F.₁ (! i)                                            ≈⟨ (refl⟩∘⟨ F.F-resp-≈ (!-unique i _)) ⟩
      FG⇒ A D.∘ F.₁ ((G.₁ f C.∘ GF⇒) C.∘ G.₁ FG⇐′ C.∘ GF⇐)          ≈⟨ (refl⟩∘⟨ F.homomorphism) ⟩
      FG⇒ A D.∘ F.₁ (G.₁ f C.∘ GF⇒) D.∘ F.₁ (G.₁ FG⇐′ C.∘ GF⇐)      ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ (F.homomorphism ○ (D.Equiv.sym (F≃id-comm₂ F∘G≈id) ⟩∘⟨refl))) ⟩
      FG⇒ A D.∘ F.₁ (G.₁ f C.∘ GF⇒) D.∘ FG⇐ D.∘ F.F₁ GF⇐            ≈⟨ (refl⟩∘⟨ F.homomorphism ⟩∘⟨refl) ⟩
      FG⇒ A D.∘ (F.₁ (G.₁ f) D.∘ F.₁ GF⇒) D.∘ (FG⇐ D.∘ F.F₁ GF⇐)    ≈⟨ (D.sym-assoc ○ (D.sym-assoc ⟩∘⟨refl) ○ D.assoc) ⟩
      (FG⇒ A D.∘ F.₁ (G.₁ f)) D.∘ F.F₁ GF⇒ D.∘ FG⇐ D.∘ F.F₁ GF⇐     ≈⟨ (F∘G≈id.⇒.commute f ⟩∘⟨ D.sym-assoc) ⟩
      (f D.∘ FG⇒ (F.₀ c)) D.∘ (F.F₁ GF⇒ D.∘ FG⇐) D.∘ F.F₁ GF⇐       ≈⟨ (D.assoc ○ (refl⟩∘⟨ D.sym-assoc)) ⟩
      f D.∘ (FG⇒ (F.₀ c) D.∘ F.F₁ GF⇒ D.∘ FG⇐) D.∘ F.F₁ GF⇐         ≈⟨ elimʳ (⊣Equivalence.zig X) ⟩
      f ∎
    }
    where
    open D.HomReasoning
    open MR D
    FG⇒ : (A : D.Obj) → F.₀ (G.₀ A) D.⇒ A
    FG⇒ A = F∘G≈id.⇒.η A
    FG⇐ = F∘G≈id.⇐.η (F.F₀ (G.F₀ (F.F₀ c)))
    FG⇐′ = F∘G≈id.⇐.η (F.₀ c)
    GF⇐ : c C.⇒ G.₀ (F.₀ c)
    GF⇐ = G∘F≈id.⇐.η c
    GF⇒ = G∘F≈id.⇒.η (G.F₀ (F.F₀ c))

  pres-Initial : Initial C → Initial D
  pres-Initial i = record { ⊥ = F.₀ ⊥ ; ⊥-is-initial = pres-IsInitial ⊥-is-initial }
    where open Initial i

-- We can do the other proof by duality
pres-terminal : {C : Category o ℓ e} {D : Category o′ ℓ′ e′} (S : StrongEquivalence C D) {c : Category.Obj C} → (t : IsTerminal C c) → IsTerminal D (Functor.F₀ (StrongEquivalence.F S) c)
pres-terminal {C = C} {D} S {c} t = IsInitial⇒coIsTerminal (Category.op D) (pres-IsInitial Sop (coIsTerminal⇒IsInitial (Category.op C) t))
  where
  Sop : StrongEquivalence (Category.op C) (Category.op D)
  Sop = StrongEquivalence.op S

pres-Terminal : {C : Category o ℓ e} {D : Category o′ ℓ′ e′} (S : StrongEquivalence C D) (t : Terminal C) → Terminal D
pres-Terminal S t = record { ⊤ = Functor.F₀ F ⊤; ⊤-is-terminal = pres-terminal S ⊤-is-terminal}
  where
  open Terminal t
  open StrongEquivalence S
