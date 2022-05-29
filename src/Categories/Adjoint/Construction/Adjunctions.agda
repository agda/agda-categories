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
    η-eq : ∀ {A} → GF≃M.⇐.η A ∘ M.η.η A ≈ adj.unit.η A
    μ-eq : ∀ {A} → GF≃M.⇐.η A ∘ M.μ.η A ≈ G.₁ (adj.counit.η _) ∘ GF≃M.⇐.η _ ∘ M.F.F₁ (GF≃M.⇐.η A)

  {-
  η-eq:
                 adj.unit.η A
            A ------------------+
    M.η.η A |                   |
            v                   v
            MA --------------> GFA
                  GF≃M.⇐.η A

  μ-eq:

         M.F.F₁ (GF≃M.⇐.η A)        GF≃M.⇐.η
    MMA ---------------------> GFM ----------> GFGFA
     |                                           |
     | M.μ A                                     | G.₁ (adj.counit.η A)
     v                                           v
     MA --------------------------------------> GFA
                     GF≃M.⇐.η A
  -}


record Split⇒ (X Y : SplitObj) : Set (suc o ⊔ suc ℓ ⊔ suc e) where
  constructor split⇒
  private
    module X = SplitObj X
    module Y = SplitObj Y
  field
    H : Functor X.D Y.D
    HF≃F' : H ∘F X.F ≃ Y.F
    G'H≃G : Y.G ∘F H ≃ X.G

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
    ; HF≃F' = unitorˡ
    ; G'H≃G = unitorʳ
    }
  comp : {A B X : SplitObj} → Split⇒ B X → Split⇒ A B → Split⇒ A X
  comp {A = A} {B = B} {X = X} (split⇒ Hᵤ HF≃F'ᵤ G'H≃Gᵤ) (split⇒ Hᵥ HF≃F'ᵥ G'H≃Gᵥ) = record
    { H = Hᵤ ∘F Hᵥ
    ; HF≃F' = HF≃F'ᵤ ⓘᵥ (Hᵤ ⓘˡ HF≃F'ᵥ) ⓘᵥ associator (SplitObj.F A) Hᵥ Hᵤ
    ; G'H≃G = G'H≃Gᵥ ⓘᵥ (G'H≃Gᵤ ⓘʳ Hᵥ) ⓘᵥ sym-associator Hᵥ Hᵤ (SplitObj.G X)
    }
