{-# OPTIONS --without-K --safe #-}

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
open import Categories.Morphism
open import Categories.Functor.Properties
open import Categories.NaturalTransformation.Core
open import Categories.NaturalTransformation.NaturalIsomorphism
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
    open X
    open Y
  field
    H : Functor X.D Y.D
    Γ : H ∘F X.F ≃ Y.F

  private
    module Γ = NaturalIsomorphism Γ

  Γ' : NaturalTransformation X.G (Y.G ∘F H)
  Γ' = F∘id⇒F ∘ᵥ
    (((Y.G ∘F H) ∘ˡ X.adj.counit) ∘ᵥ zip ∘ᵥ Y.G ∘ˡ zop)
              ∘ᵥ (Y.G ∘ˡ Γ.F⇐G ∘ʳ X.G)
              ∘ᵥ (zap ∘ᵥ Y.adj.unit ∘ʳ X.G)
              ∘ᵥ F⇒id∘F
    where
      open NaturalIsomorphism
      zip = F⇐G (associator (X.F ∘F X.G) H Y.G)
      zop = F⇒G (associator X.G X.F H)
      zap = F⇒G (associator X.G Y.F Y.G)

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
  split-id = record
    { H = Categories.Functor.id
    ; Γ = unitorˡ
    -- ; G'H≃G = unitorʳ
    }
  comp : {A B X : SplitObj} → Split⇒ B X → Split⇒ A B → Split⇒ A X
  comp {A = A} {B = B} {X = X} (split⇒ Hᵤ HF≃F'ᵤ) (split⇒ Hᵥ HF≃F'ᵥ) = record
    { H = Hᵤ ∘F Hᵥ
    ; Γ = HF≃F'ᵤ ⓘᵥ (Hᵤ ⓘˡ HF≃F'ᵥ) ⓘᵥ associator (SplitObj.F A) Hᵥ Hᵤ
    -- ; G'H≃G = G'H≃Gᵥ ⓘᵥ (G'H≃Gᵤ ⓘʳ Hᵥ) ⓘᵥ sym-associator Hᵥ Hᵤ (SplitObj.G X)
    }
