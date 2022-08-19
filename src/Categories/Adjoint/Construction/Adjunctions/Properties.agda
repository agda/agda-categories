{-# OPTIONS --without-K --safe #-}

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
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; niHelper; sym)

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
  ; !-unique = λ { {A} f → niHelper (
    let open SplitObj A
        open Split⇒ f
        module G'H≃G = NaturalIsomorphism G'H≃G
        module HF≃F' = NaturalIsomorphism HF≃F' in
    record
      { η = HF≃F'.⇐.η
      ; η⁻¹ = HF≃F'.⇒.η
      ; commute =
          let open D
              open D.HomReasoning in λ f →
              {!   !}
      ; iso = NaturalIsomorphism.iso (sym HF≃F')
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
      ; HF≃F' =
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
      ; G'H≃G =
        let open C
            open C.HomReasoning in
        niHelper (record
          { η = GF≃M.⇒.η
          ; η⁻¹ = GF≃M.⇐.η
          ; commute = λ f →
            begin
              GF≃M.⇒.η _ ∘ G.₁ (adj.counit.η (F.₀ _) D.∘ F.₁ (GF≃M.⇐.η _ ∘ f))                                            ≈⟨ refl⟩∘⟨ G.F-resp-≈ (DHR.refl⟩∘⟨ F.homomorphism) ⟩
              GF≃M.⇒.η _ ∘ G.₁ (adj.counit.η (F.₀ _) D.∘ F.₁ (GF≃M.⇐.η _) D.∘ F.₁ f)                                      ≈⟨ refl⟩∘⟨ G.homomorphism ⟩
              GF≃M.⇒.η _ ∘ G.₁ (adj.counit.η (F.₀ _)) ∘ G.₁ (F.₁ (GF≃M.⇐.η _) D.∘ F.₁ f)                                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ G.homomorphism ⟩
              GF≃M.⇒.η _ ∘ G.₁ (adj.counit.η (F.₀ _)) ∘ (G.₁ (F.₁ (GF≃M.⇐.η _))) ∘ G.₁ (F.₁ f)                            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ introʳ C (GF≃M.iso.isoˡ _) ⟩∘⟨refl ⟩
              GF≃M.⇒.η _ ∘ G.₁ (adj.counit.η (F.₀ _)) ∘ (G.₁ (F.₁ (GF≃M.⇐.η _)) ∘ GF≃M.⇐.η _ ∘ GF≃M.⇒.η _) ∘ G.₁ (F.₁ f)  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ C (C.Equiv.sym (GF≃M.⇐.commute _)) ⟩∘⟨refl ⟩
              GF≃M.⇒.η _ ∘ G.₁ (adj.counit.η (F.₀ _)) ∘ (GF≃M.⇐.η _ ∘ M.F.₁ (GF≃M.⇐.η _) ∘ GF≃M.⇒.η _) ∘ G.₁ (F.₁ f)      ≈⟨ solve C ⟩ -- TODO: remove this
              GF≃M.⇒.η _ ∘ (G.₁ (adj.counit.η (F.₀ _)) ∘ GF≃M.⇐.η _ ∘ M.F.₁ (GF≃M.⇐.η _)) ∘ GF≃M.⇒.η _ ∘ G.₁ (F.₁ f)      ≈⟨ (refl⟩∘⟨ C.Equiv.sym μ-eq ⟩∘⟨refl) ⟩
              GF≃M.⇒.η _ ∘ (GF≃M.⇐.η _ ∘ M.μ.η _) ∘ GF≃M.⇒.η _ ∘ G.₁ (F.₁ f)                                              ≈⟨ solve C ⟩ -- TODO: remove this
              GF≃M.⇒.η _ ∘ GF≃M.⇐.η _ ∘ M.μ.η _ ∘ GF≃M.⇒.η _ ∘ G.₁ (F.₁ f)                                                ≈⟨ pullˡ C (GF≃M.iso.isoʳ _) ⟩
              C.id ∘ M.μ.η _ ∘ GF≃M.⇒.η _ ∘ G.₁ (F.₁ f)                                                                   ≈⟨ identityˡ ⟩
              M.μ.η _ ∘ GF≃M.⇒.η _ ∘ G.₁ (F.₁ f)                                                                          ≈⟨ pushʳ C (GF≃M.⇒.commute _) ⟩
              (M.μ.η _ ∘ M.F.₁ f) ∘ GF≃M.⇒.η _                                                                            ∎
          ; iso = GF≃M.iso
          })
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
