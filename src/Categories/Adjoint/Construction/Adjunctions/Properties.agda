{-# OPTIONS --without-K  --allow-unsolved-metas #-}

open import Level
open import Categories.Category.Core using (Category)
open import Categories.Category
open import Categories.Monad

module Categories.Adjoint.Construction.Adjunctions.Properties {o ℓ e} {C : Category (o ⊔ ℓ ⊔ e) (ℓ ⊔ e) e} (M : Monad C) where

module C = Category C
module M = Monad M

open import Categories.Adjoint using (Adjoint)
open import Categories.Functor using (Functor)
open import Categories.Morphism.Reasoning
open import Categories.NaturalTransformation hiding (id)
open NaturalTransformation using (η)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; niHelper; sym; associator)

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
             M.F.₁ id ∘ M.η.η _ ≈⟨ M.F.identity ⟩∘⟨refl ⟩
             id ∘ M.η.η _       ≈⟨ identityˡ ⟩
             M.η.η _            ∎
  ; μ-eq = begin
             M.F.₁ id ∘ M.μ.η _                    ≈⟨ M.F.identity ⟩∘⟨refl ⟩
             id ∘ M.μ.η _                          ≈⟨ identityˡ ⟩
             M.μ.η _                               ≈⟨ Equiv.sym identityʳ ⟩
             M.μ.η _  ∘ id                         ≈⟨ refl⟩∘⟨ Equiv.sym M.F.identity ⟩
             M.μ.η _ ∘ M.F.₁ id                    ≈⟨ Equiv.sym identityʳ ⟩
             (M.μ.η _ ∘ M.F.₁ id) ∘ id             ≈⟨ assoc ⟩
             M.μ.η _ ∘ M.F.₁ id ∘ id               ≈⟨ refl⟩∘⟨  refl⟩∘⟨ Equiv.sym M.F.identity ⟩
             M.μ.η _ ∘ M.F.₁ id ∘ M.F.₁ id         ≈⟨ refl⟩∘⟨  refl⟩∘⟨ M.F.F-resp-≈ (Equiv.sym M.F.identity) ⟩
             M.μ.η _ ∘ M.F.₁ id ∘ M.F.₁ (M.F.₁ id) ∎
  } where open Category C
          open HomReasoning

Kl-object : SplitObj
Kl-object = record
  { D = Kleisli M
  ; F = KL.Free
  ; G = KL.Forgetful
  ; adj = KL.Free⊣Forgetful
  ; GF≃M = KL.FF≃F
  ; η-eq = begin
             M.F.₁ id ∘ M.η.η _ ≈⟨ M.F.identity ⟩∘⟨refl ⟩
             id ∘ M.η.η _       ≈⟨ identityˡ ⟩
             M.η.η _            ∎
  ; μ-eq = begin M.F.₁ id ∘ M.μ.η _                                     ≈⟨ M.F.identity ⟩∘⟨refl ⟩
             id ∘ M.μ.η _                                               ≈⟨ identityˡ ⟩
             M.μ.η _                                                    ≈⟨ Equiv.sym identityʳ ⟩
             M.μ.η _ ∘ id                                               ≈⟨ refl⟩∘⟨ Equiv.sym M.F.identity ⟩
             M.μ.η _ ∘ M.F.₁ id                                         ≈⟨ refl⟩∘⟨ M.F.F-resp-≈ (Equiv.sym M.F.identity) ⟩
             M.μ.η _ ∘ M.F.₁ (M.F.₁ id)                                 ≈⟨ Equiv.sym identityʳ ⟩
             (M.μ.η _ ∘ M.F.₁ (M.F.₁ id)) ∘ id                          ≈⟨ refl⟩∘⟨ Equiv.sym M.F.identity ⟩
             (M.μ.η _ ∘ M.F.₁ (M.F.₁ id)) ∘ M.F.₁ id                    ≈⟨ Equiv.sym identityʳ  ⟩
             ((M.μ.η _ ∘ M.F.₁ (M.F.₁ id)) ∘ M.F.₁ id) ∘ id             ≈⟨ assoc ⟩
             (M.μ.η _ ∘ M.F.₁ (M.F.₁ id)) ∘ M.F.₁ id ∘ id               ≈⟨ refl⟩∘⟨ refl⟩∘⟨ Equiv.sym M.F.identity ⟩
             (M.μ.η _ ∘ M.F.₁ (M.F.₁ id)) ∘ M.F.₁ id ∘ M.F.₁ id         ≈⟨ refl⟩∘⟨ refl⟩∘⟨ M.F.F-resp-≈ (Equiv.sym M.F.identity) ⟩
             (M.μ.η _ ∘ M.F.₁ (M.F.₁ id)) ∘ M.F.₁ id ∘ M.F.₁ (M.F.₁ id) ∎
  } where open Category C
          open HomReasoning

EM-terminal : IsTerminal EM-object
EM-terminal = record
  { ! = {!   !}
  ; !-unique = {!   !}
  }

Kl-initial : IsInitial Kl-object
Kl-initial = record
  { ! = !
  ; !-unique = λ { {A} H → niHelper (
    let module A = SplitObj A
        module K = SplitObj Kl-object
        module H = Split⇒ H
        module ! = Split⇒ !
        module Γ = NaturalIsomorphism H.Γ
        module CH = C.HomReasoning
        open Category A.D in
    record
      { η   = Γ.⇐.η
      ; η⁻¹ = Γ.⇒.η
      ; commute = λ f →
         let useful : ∀ {x}
                    → A.GF≃M.⇐.η x C.≈ A.G.F₁ (Γ.⇒.η x)
                                   C.∘ A.G.F₁ (Functor.F₁ H.H C.id)
                                   C.∘ A.G.F₁ (Γ.⇐.η (M.F.F₀ x))
                                   C.∘ A.adj.unit.η (M.F.F₀ x)
             useful = let open C.HomReasoning in
                         begin _ ≈⟨ H.μ-comp ⟩
                               _ ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ elimʳ C (M.F.identity)) ⟩
                               _ ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.identityʳ) ⟩
                               _ ≈⟨ (refl⟩∘⟨ C.identityˡ) ⟩
                               _ ≈⟨ refl⟩∘⟨ C.identityˡ   ⟩
                               _ ≈⟨ (refl⟩∘⟨ (A.G.F-resp-≈ (Functor.F-resp-≈ H.H M.F.identity) ⟩∘⟨refl) ⟩∘⟨refl) ⟩
                               _ ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.identityˡ) ⟩
                               _ ≈⟨ (refl⟩∘⟨ (elimʳ C (elimʳ C A.G.identity)) ⟩∘⟨refl) ⟩
                               _ ∎
     in let open A.D.HomReasoning

         in begin (Γ.⇐.η _ ∘ A.adj.counit.η (A.F.F₀ _) ∘ A.F.F₁ (A.GF≃M.⇐.η _ C.∘ f))
                                        ≈⟨  (refl⟩∘⟨ refl⟩∘⟨ A.F.F-resp-≈ ((useful CH.⟩∘⟨refl) CH.○ (C.assoc CH.○ (CH.refl⟩∘⟨ C.assoc ) CH.○ CH.refl⟩∘⟨ CH.refl⟩∘⟨ C.assoc ))) ⟩
                              _ ≈⟨ ((refl⟩∘⟨ refl⟩∘⟨ A.F.homomorphism)) ⟩
                              _ ≈⟨ (refl⟩∘⟨ pullˡ A.D (A.adj.counit.commute _)) ⟩
                              _ ≈⟨ (refl⟩∘⟨ assoc) ⟩
                              _ ≈⟨ cancelˡ A.D (Γ.iso.isoˡ _) ⟩
                              _ ≈⟨ (refl⟩∘⟨ (A.F.homomorphism ○ refl⟩∘⟨ A.F.homomorphism ○ refl⟩∘⟨ refl⟩∘⟨ A.F.homomorphism)) ⟩
                              _ ≈⟨ extendʳ A.D (A.adj.counit.commute _) ⟩
                              _ ≈⟨ (refl⟩∘⟨ extendʳ A.D (A.adj.counit.commute _)) ⟩
                              _ ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ pullˡ A.D A.adj.zig) ⟩
                              _ ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ A.D.identityˡ) ⟩
                              _ ≈⟨ (refl⟩∘⟨ Γ.⇐.commute _) ⟩
                              _ ≈⟨ (refl⟩∘⟨ Functor.F-resp-≈ H.H (M.η.commute _) ⟩∘⟨refl) ⟩
                              _ ≈⟨ Equiv.sym assoc ⟩
                              _ ≈⟨ (Equiv.sym (Functor.homomorphism H.H) ⟩∘⟨refl) ⟩
                              _ ≈⟨ (Functor.F-resp-≈ H.H (elimʳ C M.F.identity CH.⟩∘⟨refl) ⟩∘⟨refl) ⟩
                              _ ≈⟨ (Functor.F-resp-≈ H.H C.sym-assoc ⟩∘⟨refl) ⟩
                              _ ≈⟨ pushˡ A.D (Functor.homomorphism H.H) ⟩
                              _ ≈⟨ (refl⟩∘⟨ elimˡ A.D (Functor.identity H.H)) ⟩
                              Functor.F₁ H.H f ∘ Γ.⇐.η _ ∎
      ; iso = NaturalIsomorphism.iso (sym H.Γ)
      })
    }
  }
  where
    ! : {A : SplitObj} → Split⇒ Kl-object A
    ! {splitobj D F G adj GF≃M η-eq μ-eq} = record
      { H =
        let open D
            open D.HomReasoning in
        record
          { F₀ = F.₀
          ; F₁ = λ f → adj.counit.η _ ∘ F.₁ (GF≃M.⇐.η _ C.∘ f)
          ; identity = λ {A} →
            begin
              adj.counit.η (F.₀ A) ∘ F.₁ (GF≃M.⇐.η A C.∘ M.η.η A) ≈⟨ refl⟩∘⟨ F.F-resp-≈ η-eq ⟩
              adj.counit.η (F.₀ A) ∘ F.₁ (adj.unit.η A)           ≈⟨ adj.zig ⟩
              D.id                                                ∎
          ; homomorphism = λ {X} {Y} {Z} {f} {g} →
            let ε x = adj.counit.η x in
            begin
              ε _ ∘ F.₁ (GF≃M.⇐.η _ C.∘ (M.μ.η _ C.∘ M.F.₁ g) C.∘ f)                                ≈⟨ refl⟩∘⟨ F.F-resp-≈ (assoc²'' C) ⟩
              ε _ ∘ F.₁ ((GF≃M.⇐.η _ C.∘ M.μ.η _) C.∘ M.F.₁ g C.∘ f)                                ≈⟨ refl⟩∘⟨ F.F-resp-≈ (μ-eq CHR.⟩∘⟨refl) ⟩
              ε _ ∘ F.₁ ((G.₁ (ε (F.₀ _)) C.∘ GF≃M.⇐.η _ C.∘ M.F.₁ (GF≃M.⇐.η _)) C.∘ M.F.₁ g C.∘ f) ≈⟨ refl⟩∘⟨ F.F-resp-≈ (assoc²' C) ⟩
              ε _ ∘ F.₁ (G.₁ (ε (F.₀ _)) C.∘ GF≃M.⇐.η _ C.∘ M.F.₁ (GF≃M.⇐.η _) C.∘ M.F.₁ g C.∘ f)   ≈⟨ refl⟩∘⟨ F.F-resp-≈ (CHR.refl⟩∘⟨ CHR.refl⟩∘⟨ pullˡ C (C.Equiv.sym M.F.homomorphism)) ⟩
              ε _ ∘ F.₁ (G.₁ (ε (F.₀ _)) C.∘ GF≃M.⇐.η _ C.∘ M.F.₁ (GF≃M.⇐.η _ C.∘ g) C.∘ f)         ≈⟨ refl⟩∘⟨ F.F-resp-≈ (CHR.refl⟩∘⟨ extendʳ C (GF≃M.⇐.commute _)) ⟩
              ε _ ∘ F.₁ (G.₁ (ε (F.₀ _)) C.∘ G.₁ (F.₁ (GF≃M.⇐.η _ C.∘ g)) C.∘ GF≃M.⇐.η _ C.∘ f)     ≈⟨ refl⟩∘⟨ F.homomorphism ⟩
              ε _ ∘ F.₁ (G.₁ (ε (F.₀ _))) ∘ F.₁ (G.₁ (F.₁ (GF≃M.⇐.η _ C.∘ g)) C.∘ GF≃M.⇐.η _ C.∘ f) ≈⟨ DMR.extendʳ (adj.counit.commute _) ⟩
              ε _ ∘ ε _ ∘ F.₁ (G.₁ (F.₁ (GF≃M.⇐.η _ C.∘ g)) C.∘ GF≃M.⇐.η _ C.∘ f)                   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ F.homomorphism ⟩
              ε _ ∘ ε _ ∘ F.₁ (G.₁ (F.₁ (GF≃M.⇐.η _ C.∘ g))) ∘ F.₁ (GF≃M.⇐.η _ C.∘ f)               ≈⟨ refl⟩∘⟨ DMR.extendʳ (adj.counit.commute _) ⟩
              ε _ ∘ F.₁ (GF≃M.⇐.η _ C.∘ g) ∘ ε _ ∘ F.₁ (GF≃M.⇐.η _ C.∘ f)                           ≈⟨ sym-assoc ⟩
              (ε _ ∘ F.₁ (GF≃M.⇐.η _ C.∘ g)) ∘ ε _ ∘ F.₁ (GF≃M.⇐.η _ C.∘ f)                         ∎
          ; F-resp-≈ = λ x → D.∘-resp-≈ʳ (F.F-resp-≈ (C.∘-resp-≈ʳ x))
          }
      ; Γ =
        let open D
            open D.HomReasoning in
        niHelper (record
          { η = λ _ → D.id
          ; η⁻¹ = λ _ → D.id
          ; commute = λ f →
            begin
              D.id ∘ adj.counit.η _ ∘ F.₁ (GF≃M.⇐.η _ C.∘ M.η.η _ C.∘ f) ≈⟨ refl⟩∘⟨ refl⟩∘⟨ F.F-resp-≈ (pullˡ C η-eq) ⟩
              D.id ∘ adj.counit.η _ ∘ F.₁ (adj.unit.η _ C.∘ f)           ≈⟨ refl⟩∘⟨ refl⟩∘⟨ F.homomorphism ⟩
              D.id ∘ adj.counit.η _ ∘ F.₁ (adj.unit.η _) ∘ F.₁ f         ≈⟨ refl⟩∘⟨ pullˡ D adj.zig ⟩
              D.id ∘ D.id ∘ F.₁ f                                        ≈⟨ identityˡ ⟩
              D.id ∘ F.₁ f                                               ≈⟨ identityˡ ⟩
              F.₁ f                                                      ≈⟨ D.Equiv.sym identityʳ ⟩
              (F.₁ f ∘ D.id)                                             ∎
          ; iso = λ X → record { isoˡ = identityˡ ; isoʳ = identityˡ }
          })
      ; μ-comp = {!   !}
      } where
        module adj  = Adjoint adj
        module F    = Functor F
        module G    = Functor G
        module GF≃M = NaturalIsomorphism GF≃M
        module D    = Category D
        module CHR = C.HomReasoning
        module DHR = D.HomReasoning
        module DMR = Categories.Morphism.Reasoning D
        module CMR = Categories.Morphism.Reasoning C
