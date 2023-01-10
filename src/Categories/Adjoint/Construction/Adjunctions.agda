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

module _ {X Y : SplitObj} (H : Functor (SplitObj.D X) (SplitObj.D Y)) (Γ : H ∘F (SplitObj.F X) ≃ (SplitObj.F Y)) where
  private
    module X = SplitObj X
    module Y = SplitObj Y
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

record Split⇒ (X Y : SplitObj) : Set (suc o ⊔ suc ℓ ⊔ suc e) where
  constructor split⇒
  private
    module X = SplitObj X
    module Y = SplitObj Y

  field
    H : Functor X.D Y.D
    Γ : H ∘F X.F ≃ Y.F

  private
    module Γ = NaturalIsomorphism Γ

  field
    -- μ-comp : Y.GF≃M.F⇐G -- Y.GF≃M.F⇒G
    --        ≅ (Y.G ∘ˡ Γ.F⇒G)
    --        ∘ᵥ NaturalIsomorphism.F⇒G (associator X.F H Y.G)
    --        ∘ᵥ (Γ' {X = X} {Y = Y} H Γ ∘ʳ X.F)
    --        ∘ᵥ X.GF≃M.F⇐G
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
      Equiv.sym(begin {!   !} ≈⟨ elimˡ C (Functor.identity A.G) ⟩ 
                      {!   !} ≈⟨ (refl⟩∘⟨ elimˡ C (Functor.identity A.G)) ⟩∘⟨refl ⟩ 
                      {!   !} ≈⟨ elimˡ C A.adj.zag ⟩ 
                      {!   !} ∎)}
      --  Equiv.sym (begin _ ≈⟨ elimˡ C (Functor.identity A.G) ⟩
      --        _ ≈⟨ identityˡ ⟩
      --        _ ≈⟨ assoc  ⟩
      --        _ ≈⟨ identityˡ ⟩
      --        _ ≈⟨ ((refl⟩∘⟨ (refl⟩∘⟨ identityʳ)) ⟩∘⟨refl) ⟩
      --        _ ≈⟨ (refl⟩∘⟨ elimˡ C (Functor.identity A.G)) ⟩∘⟨refl ⟩
      --        _ ≈⟨ ((refl⟩∘⟨ identityˡ) ⟩∘⟨refl) ⟩
      --        _ ≈⟨ (((refl⟩∘⟨ identityˡ) ⟩∘⟨refl) ⟩∘⟨refl) ⟩
      --        _ ≈⟨ ((elimʳ C (Functor.identity A.G) ⟩∘⟨refl) ⟩∘⟨refl) ⟩
      --        _ ≈⟨ elimˡ C A.adj.zag ⟩
      --        _ ∎)}
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
                         {!   !} ≈⟨ {!   !} ⟩ 
                         {!   !} ≈⟨ {!   !} ⟩ 
                         {!   !} ∎) }
        -- Equiv.sym (begin {!   !} ≈⟨ ( Functor.homomorphism X.G ⟩∘⟨refl) ⟩
        --       {!   !} ≈⟨ ((refl⟩∘⟨ Functor.F-resp-≈ X.G X.D.identityʳ)  ⟩∘⟨refl) ⟩
        --       {!   !} ≈⟨ (refl⟩∘⟨ (identityˡ ○ (identityˡ ⟩∘⟨refl))) ⟩
        --       {!   !} ≈⟨ (refl⟩∘⟨ (refl⟩∘⟨ (refl⟩∘⟨ (identityʳ ○ identityˡ))) ⟩∘⟨refl) ⟩
        --       {!   !} ≈⟨ refl⟩∘⟨ ((refl⟩∘⟨ (Functor.homomorphism X.G ⟩∘⟨refl)) ⟩∘⟨refl) ⟩
        --       {!   !} ≈⟨ (refl⟩∘⟨ (((refl⟩∘⟨ (identityˡ ○ Functor.identity X.G)) ⟩∘⟨refl) ⟩∘⟨refl)) ⟩
        --       {!   !} ≈⟨ (refl⟩∘⟨ (identityʳ ⟩∘⟨refl) ⟩∘⟨refl) ⟩
        --       {!   !} ≈⟨ (refl⟩∘⟨ ((refl⟩∘⟨ ((Functor.homomorphism X.G ⟩∘⟨refl) ⟩∘⟨refl)) ⟩∘⟨refl)) ⟩
        --       {!   !} ≈⟨ (refl⟩∘⟨ ((refl⟩∘⟨ ((elimˡ C (Functor.identity X.G) ⟩∘⟨refl) ⟩∘⟨refl)) ⟩∘⟨refl)) ⟩
        --       {!   !} ≈⟨ {!   !} ⟩
        --       {!   !} ≈⟨ {!   !} ⟩
        --       {!   !} ∎)}
    -- ; G'H≃G = G'H≃Gᵥ ⓘᵥ (G'H≃Gᵤ ⓘʳ Hᵥ) ⓘᵥ sym-associator Hᵥ Hᵤ (SplitObj.G X)
    } where
       module A = SplitObj A
       module B = SplitObj B
       module X = SplitObj X
       open C
       open C.HomReasoning
