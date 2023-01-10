{-# OPTIONS --without-K  --allow-unsolved-metas #-}

open import Level
open import Categories.Category.Core using (Category)
open import Categories.Category
open import Categories.Monad

module Categories.Adjoint.Construction.Adjunctions {o ℓ e} {C : Category o ℓ e} (M : Monad C) where

private
  module C = Category C
  module M = Monad M
  open C

open import Categories.Adjoint
open import Categories.Functor
open import Categories.Morphism hiding (_≅_)
open import Categories.Functor.Properties
open import Categories.NaturalTransformation.Core
open import Categories.NaturalTransformation.NaturalIsomorphism
open import Categories.NaturalTransformation.Equivalence renaming (_≃_ to _≅_)
open import Categories.Morphism.Reasoning as MR
open import Categories.Tactic.Category

-- the category of adjunctions splitting a given monad
record SplitObj : Set (suc o ⊔ suc ℓ ⊔ suc e) where
  constructor splitobj
  field
    D : Category o ℓ e
    F : Functor C D
    G : Functor D C
    adj : F ⊣ G
    GF≃M : G ∘F F ≃ M.F

  module D = Category D
  module F = Functor F
  module G = Functor G
  module adj = Adjoint adj
  module GF≃M = NaturalIsomorphism GF≃M

  field
    η-eq : ∀ {A} → GF≃M.⇐.η _ ∘ M.η.η A ≈ adj.unit.η _
    μ-eq : ∀ {A} → GF≃M.⇐.η _ ∘ M.μ.η A ≈ G.₁ (adj.counit.η (F.₀ A)) ∘ GF≃M.⇐.η _ ∘ M.F.F₁ (GF≃M.⇐.η A)

  {-
  η-eq:
                 adj.unit.η A
            A ------------------+
    M.η.η A |                   |
            v                   v
            MA --------------> GFA
                  GF≃M.⇐.η A

  μ-eq:
             GF≃M.⇐.η              G.F₁ (F.F₁ (GF≃M.⇐.η))
        ---------------------> GFMA -------------------->
    MMA ---------------------> MGFA --------------------> GFGFA
     |   M.F.F₁ (GF≃M.⇐.η A)              GF≃M.⇐.η         |
     |                                                      |
     | M.μ A                                                | G.₁ (adj.counit.η (F.₀ A))
     v                                                      v
     MA -------------------------------------------------> GFA
                     GF≃M.⇐.η A
  -}

record Split⇒ (X Y : SplitObj) : Set (suc o ⊔ suc ℓ ⊔ suc e) where
  constructor split⇒
  private
    module X = SplitObj X
    module Y = SplitObj Y

  field
    H : Functor X.D Y.D
    Γ : H ∘F X.F ≃ Y.F

  module Γ = NaturalIsomorphism Γ
  module H = Functor H

  field
    μ-comp : ∀ {x : Obj} → Y.GF≃M.⇐.η x ≈ Y.G.F₁ (Γ.⇒.η x) ∘ ((Y.G.F₁ (Functor.F₁ H (X.adj.counit.η (X.F.F₀ x)))) ∘ Y.G.F₁ (Γ.⇐.η (X.G.F₀ (X.F.F₀ x))) ∘ (Y.adj.unit.η (X.G.F₀ (X.F.F₀ x)))) ∘ X.GF≃M.⇐.η x

Split : Monad C → Category _ _ _
Split M = record
  { Obj = SplitObj
  ; _⇒_ = Split⇒
  ; _≈_ = λ U V → Split⇒.H U ≃ Split⇒.H V
  ; id = split-id
  ; _∘_ = comp
  ; assoc = λ { {f = f} {g = g} {h = h} → associator (Split⇒.H f) (Split⇒.H g) (Split⇒.H h) }
  ; sym-assoc = λ { {f = f} {g = g} {h = h} → sym-associator (Split⇒.H f) (Split⇒.H g) (Split⇒.H h) }
  ; identityˡ = unitorˡ
  ; identityʳ = unitorʳ
  ; identity² = unitor²
  ; equiv = record { refl = refl ; sym = sym ; trans = trans }
  ; ∘-resp-≈ = _ⓘₕ_
  }
  where
  open NaturalTransformation
  split-id : {A : SplitObj} → Split⇒ A A
  split-id {A} = record
    { H = Categories.Functor.id
    ; Γ = unitorˡ
    ; μ-comp = λ { {x} →
      Equiv.sym(begin _ ≈⟨ elimˡ C (Functor.identity A.G) ⟩
                      _ ≈⟨ (refl⟩∘⟨ elimˡ C (Functor.identity A.G)) ⟩∘⟨refl ⟩
                      _ ≈⟨ elimˡ C A.adj.zag ⟩
                      _ ∎)}
    } where module A = SplitObj A
            open C
            open C.HomReasoning
  comp : {A B X : SplitObj} → Split⇒ B X → Split⇒ A B → Split⇒ A X
  comp {A = A} {B = B} {X = X} (split⇒ Hᵤ Γᵤ Aμ-comp) (split⇒ Hᵥ Γᵥ Bμ-comp) = record
    { H = Hᵤ ∘F Hᵥ
    ; Γ = Γᵤ ⓘᵥ (Hᵤ ⓘˡ Γᵥ) ⓘᵥ associator (SplitObj.F A) Hᵥ Hᵤ
    ; μ-comp = λ { {x} →
        Equiv.sym (begin {!   !} ≈⟨ (X.G.F-resp-≈ (X.D.HomReasoning.refl⟩∘⟨ X.D.identityʳ) ⟩∘⟨refl) ⟩
                         {!   !} ≈⟨ (refl⟩∘⟨ ((refl⟩∘⟨ (X.G.F-resp-≈ (X.D.identityˡ X.D.HomReasoning.⟩∘⟨refl) ⟩∘⟨refl)) ⟩∘⟨refl)) ⟩
                         {!   !} ≈⟨ pushˡ C X.G.homomorphism ⟩
                         {!   !} ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ assoc) ⟩
                         {!   !} ≈⟨ {!  !} ⟩
                         {!   !} ≈⟨ {!   !} ⟩
                         {!   !} ≈⟨ {!   !} ⟩
                         {!   !} ≈⟨ {!  !} ⟩
                         {!   !} ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ Equiv.sym Bμ-comp) ⟩
                         {!   !} ≈⟨ Equiv.sym Aμ-comp ⟩
                         {!   !} ∎) }


{-
Have

X.G.F₁ (Γᵤ.⇒.η x) ∘
      X.G.F₁ (Hᵤ.F₁ (Γᵥ.⇒.η x)) ∘
      X.G.F₁ (Hᵤ.F₁ (Hᵥ.F₁ (A.adj.counit.η (A.F.F₀ x)))) ∘
      (X.G.F₁
       (Hᵤ.F₁ (Γᵥ.⇐.η (A.G.F₀ (A.F.F₀ x))) X.D.∘
        Γᵤ.⇐.η (A.G.F₀ (A.F.F₀ x)))
       ∘ X.adj.unit.η (A.G.F₀ (A.F.F₀ x)))
      ∘ A.GF≃M.⇐.η x

Goal

      X.G.F₁ (Γᵤ.⇒.η x) ∘
      (X.G.F₁ (Hᵤ.F₁ (B.adj.counit.η (B.F.F₀ x))) ∘
       X.G.F₁ (Γᵤ.⇐.η (B.G.F₀ (B.F.F₀ x))) ∘
       X.adj.unit.η (B.G.F₀ (B.F.F₀ x)))
      ∘
      B.G.F₁ (Γᵥ.⇒.η x) ∘
      (B.G.F₁ (Hᵥ.F₁ (A.adj.counit.η (A.F.F₀ x))) ∘
       B.G.F₁ (Γᵥ.⇐.η (A.G.F₀ (A.F.F₀ x))) ∘
       B.adj.unit.η (A.G.F₀ (A.F.F₀ x)))
      ∘ A.GF≃M.⇐.η x
-}
    } where
       module A = SplitObj A
       module B = SplitObj B
       module X = SplitObj X
       open C
       open C.HomReasoning
       module Hᵤ = Functor Hᵤ
       module Hᵥ = Functor Hᵥ
       module Γᵤ = NaturalIsomorphism Γᵤ
       module Γᵥ = NaturalIsomorphism Γᵥ
