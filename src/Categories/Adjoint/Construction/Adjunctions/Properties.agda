{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category.Core using (Category)
open import Categories.Category
open import Categories.Monad

module Categories.Adjoint.Construction.Adjunctions.Properties {o ℓ e} {C : Category (o ⊔ ℓ ⊔ e) (ℓ ⊔ e) e} (M : Monad C) where

module C = Category C
module M = Monad M

open import Categories.Adjoint
open import Categories.Functor
open import Categories.Morphism.Reasoning
open import Categories.NaturalTransformation.Core as NT
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; niHelper)

open import Categories.Adjoint.Construction.Adjunctions M

open import Categories.Object.Terminal (Split M)
open import Categories.Object.Initial (Split M)
open import Categories.Category.Construction.EilenbergMoore
open import Categories.Category.Construction.Kleisli
open import Categories.Adjoint.Construction.Kleisli M as KL
open import Categories.Adjoint.Construction.EilenbergMoore M as EM

open import Categories.Tactic.Category

EM-object : SplitObj
EM-object = record
  { D = EilenbergMoore M
  ; F = EM.Free
  ; G = EM.Forgetful
  ; adj = EM.Free⊣Forgetful
  ; GF≃M = EM.FF≃F
  ; η-eq = begin
             M.F.F₁ C.id ∘ M.η.η _ ≈⟨ M.F.identity ⟩∘⟨refl ⟩
             C.id ∘ M.η.η _        ≈⟨ identityˡ ⟩
             M.η.η _               ∎
  ; μ-eq = begin
             M.F.F₁ C.id ∘ M.μ.η _                        ≈⟨ M.F.identity ⟩∘⟨refl ⟩
             C.id ∘ M.μ.η _                               ≈⟨ identityˡ ⟩
             M.μ.η _                                      ≈⟨ Equiv.sym identityʳ ⟩
             M.μ.η _  ∘ C.id                              ≈⟨ refl⟩∘⟨ Equiv.sym M.F.identity ⟩
             M.μ.η _ ∘ M.F.F₁ C.id                        ≈⟨ Equiv.sym identityʳ ⟩
             (M.μ.η _ ∘ M.F.F₁ C.id) ∘ C.id               ≈⟨ assoc ⟩
             M.μ.η _ ∘ M.F.F₁ C.id ∘ C.id                 ≈⟨ refl⟩∘⟨  refl⟩∘⟨ Equiv.sym M.F.identity ⟩
             M.μ.η _ ∘ M.F.F₁ C.id ∘ M.F.F₁ C.id          ≈⟨ refl⟩∘⟨  refl⟩∘⟨ M.F.F-resp-≈ (Equiv.sym M.F.identity) ⟩
             M.μ.η _ ∘ M.F.F₁ C.id ∘ M.F.F₁ (M.F.F₁ C.id) ∎
  } where open C
          open HomReasoning

Kl-object : SplitObj
Kl-object = record
  { D = Kleisli M
  ; F = KL.Free
  ; G = KL.Forgetful
  ; adj = KL.Free⊣Forgetful
  ; GF≃M = KL.FF≃F
  ; η-eq = begin
            M.F.F₁ C.id ∘ M.η.η _ ≈⟨ M.F.identity ⟩∘⟨refl ⟩
            C.id ∘ M.η.η _        ≈⟨ identityˡ ⟩
            M.η.η _               ∎
  ; μ-eq = begin M.F.F₁ C.id ∘ M.μ.η _                                            ≈⟨ M.F.identity ⟩∘⟨refl ⟩
            C.id ∘ M.μ.η _                                                        ≈⟨ identityˡ ⟩
            M.μ.η _                                                               ≈⟨ Equiv.sym identityʳ ⟩
            M.μ.η _ ∘ C.id                                                        ≈⟨ refl⟩∘⟨ Equiv.sym M.F.identity ⟩
            M.μ.η _ ∘ M.F.F₁ C.id                                                 ≈⟨ refl⟩∘⟨ M.F.F-resp-≈ (Equiv.sym M.F.identity) ⟩
            M.μ.η _ ∘ M.F.F₁ (M.F.F₁ C.id)                                        ≈⟨ Equiv.sym identityʳ ⟩
            (M.μ.η _ ∘ M.F.F₁ (M.F.F₁ C.id)) ∘ C.id                               ≈⟨ refl⟩∘⟨ Equiv.sym M.F.identity ⟩
            (M.μ.η _ ∘ M.F.F₁ (M.F.F₁ C.id)) ∘ M.F.F₁ C.id                        ≈⟨ Equiv.sym identityʳ  ⟩
            ((M.μ.η _ ∘ M.F.F₁ (M.F.F₁ C.id)) ∘ M.F.F₁ C.id) ∘ C.id               ≈⟨ assoc ⟩
            (M.μ.η _ ∘ M.F.F₁ (M.F.F₁ C.id)) ∘ M.F.F₁ C.id ∘ C.id                 ≈⟨ refl⟩∘⟨ refl⟩∘⟨ Equiv.sym M.F.identity ⟩
            (M.μ.η _ ∘ M.F.F₁ (M.F.F₁ C.id)) ∘ M.F.F₁ C.id ∘ M.F.F₁ C.id          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ M.F.F-resp-≈ (Equiv.sym M.F.identity) ⟩
            (M.μ.η _ ∘ M.F.F₁ (M.F.F₁ C.id)) ∘ M.F.F₁ C.id ∘ M.F.F₁ (M.F.F₁ C.id) ∎
  } where open C
          open HomReasoning

EM-terminal : IsTerminal EM-object
EM-terminal = record
  { ! = {!   !}
  ; !-unique = {!   !}
  }

Kl-initial : IsInitial Kl-object
Kl-initial = record
  { ! = bang
  ; !-unique = λ { {A} f → niHelper (
    let open SplitObj A
        open Split⇒ f in
    record
      { η = λ X → {!   !}
      ; η⁻¹ = {!   !}
      ; commute = {!   !}
      ; iso = {!   !}
      })
    }
  }
  where
    bang : {A : SplitObj} → Split⇒ Kl-object A
    bang {splitobj D F G adj GF≃M η-eq μ-eq} = record
      { H = record
            { F₀ = F.F₀
            ; F₁ = λ f → adj.counit.η _ ∘ F.₁ (GF≃M.⇐.η _ C.∘ f)
            ; identity = λ {A} →
             begin
                adj.counit.η (F.₀ A) ∘ F.₁ (GF≃M.⇐.η A C.∘ M.η.η A) ≈⟨ refl⟩∘⟨ F.F-resp-≈ η-eq ⟩
                adj.counit.η (F.₀ A) ∘ F.₁ (adj.unit.η A)           ≈⟨ adj.zig ⟩
                D.id                                                ∎
            ; homomorphism = λ {X} {Y} {Z} {f} {g} →
                let ε x = adj.counit.η x in
                begin
                  ε _ ∘ F.₁ (GF≃M.⇐.η _ C.∘ (M.μ.η _ C.∘ M.₁ g) C.∘ f)                            ≈⟨ refl⟩∘⟨ F.F-resp-≈ (CMR.assoc²'') ⟩
                  ε _ ∘ F.₁ ((GF≃M.⇐.η _ C.∘ M.μ.η _) C.∘ M.₁ g C.∘ f)                            ≈⟨ (refl⟩∘⟨ F.F-resp-≈ (μ-eq CHR.⟩∘⟨refl)) ⟩
                  ε _ ∘ F.₁ ((G.₁ (ε (F.₀ _)) C.∘ GF≃M.⇐.η _ C.∘ M.₁ (GF≃M.⇐.η _)) C.∘ M.₁ g C.∘ f)   ≈⟨ (refl⟩∘⟨ F.F-resp-≈ CMR.assoc²') ⟩
                  ε _ ∘ F.₁ (G.₁ (ε (F.₀ _)) C.∘ GF≃M.⇐.η _ C.∘ M.₁ (GF≃M.⇐.η _) C.∘ M.₁ g C.∘ f)     ≈⟨ (refl⟩∘⟨ F.F-resp-≈ (CHR.refl⟩∘⟨ CHR.refl⟩∘⟨ CMR.pullˡ (C.Equiv.sym M.F.homomorphism))) ⟩
                  ε _ ∘ F.₁ (G.₁ (ε (F.₀ _)) C.∘ GF≃M.⇐.η _ C.∘ M.₁ (GF≃M.⇐.η _ C.∘ g) C.∘ f)       ≈⟨ (refl⟩∘⟨ F.F-resp-≈ (CHR.refl⟩∘⟨ CMR.extendʳ (GF≃M.⇐.commute _))) ⟩
                  ε _ ∘ F.₁ (G.₁ (ε (F.₀ _)) C.∘ G.₁ (F.₁ (GF≃M.⇐.η _ C.∘ g)) C.∘ GF≃M.⇐.η _ C.∘ f)   ≈⟨ (refl⟩∘⟨ F.homomorphism) ⟩
                  ε _ ∘ F.₁ (G.₁ (ε (F.₀ _))) ∘ F.₁ (G.₁ (F.₁ (GF≃M.⇐.η _ C.∘ g)) C.∘ GF≃M.⇐.η _ C.∘ f) ≈⟨ DMR.extendʳ (adj.counit.commute _) ⟩
                  ε _ ∘ ε _ ∘ F.₁ (G.₁ (F.₁ (GF≃M.⇐.η _ C.∘ g)) C.∘ GF≃M.⇐.η _ C.∘ f)               ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ F.homomorphism) ⟩
                  ε _ ∘ ε _ ∘ F.₁ (G.₁ (F.₁ (GF≃M.⇐.η _ C.∘ g))) ∘ F.₁ (GF≃M.⇐.η _ C.∘ f)             ≈⟨ (refl⟩∘⟨ DMR.extendʳ (adj.counit.commute _)) ⟩
                  ε _ ∘ F.₁ (GF≃M.⇐.η _ C.∘ g) ∘ ε _ ∘ F.₁ (GF≃M.⇐.η _ C.∘ f)                     ≈⟨ sym-assoc ⟩
                  (ε _ ∘ F.₁ (GF≃M.⇐.η _ C.∘ g)) ∘ ε _ ∘ F.₁ (GF≃M.⇐.η _ C.∘ f)                   ∎
              ; F-resp-≈ = λ x → D.∘-resp-≈ʳ (F.F-resp-≈ (C.∘-resp-≈ʳ x))
              }
      ; HF≃F' = niHelper (record
        { η = λ _ → D.id
        ; η⁻¹ = λ _ → D.id
        ; commute = λ f →
            begin
              D.id ∘ adj.counit.η _ ∘ F.F₁ (GF≃M.⇐.η _ C.∘ M.η.η _ C.∘ f) ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ F.F-resp-≈ (pullˡ C η-eq)) ⟩
              (D.id ∘ adj.counit.η _ ∘ F.F₁ (adj.unit.η _ C.∘ f))         ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ F.homomorphism) ⟩
              (D.id ∘ adj.counit.η _ ∘ F.F₁ (adj.unit.η _) ∘ F.F₁ f)      ≈⟨ (refl⟩∘⟨ pullˡ D adj.zig) ⟩
              (D.id ∘ D.id ∘ F.F₁ f)                                      ≈⟨ identityˡ ⟩
              (D.id ∘ F.F₁ f)                                             ≈⟨ identityˡ ⟩
              F.F₁ f                                                      ≈⟨ D.Equiv.sym identityʳ ⟩
              (F.F₁ f ∘ D.id)                                             ∎
        ; iso = λ X → record { isoˡ = identityˡ ; isoʳ = identityˡ }
        })
      ; G'H≃G = {!   !}
      } where
       module adj  = Adjoint adj
       module F    = Functor F
       module G    = Functor G
       module GF≃M = NaturalIsomorphism GF≃M
       module D    = Category D
       open D
       open D.HomReasoning
       module CHR = C.HomReasoning
       module DMR = Categories.Morphism.Reasoning D
       module CMR = Categories.Morphism.Reasoning C
