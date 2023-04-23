{-# OPTIONS --without-K  --allow-unsolved-metas #-}

open import Level
open import Categories.Category.Core using (Category)
open import Categories.Category
open import Categories.Monad

module Categories.Adjoint.Construction.Adjunctions.Properties {o ℓ e} {C : Category (o ⊔ ℓ ⊔ e) (ℓ ⊔ e) e} (M : Monad C) where

private
  module C = Category C
  module M = Monad M

open import Categories.Adjoint using (Adjoint)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Morphism.Reasoning
open import Categories.NaturalTransformation hiding (id)
open NaturalTransformation using (η)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; niHelper; sym; associator)

open import Categories.Adjoint.Construction.Adjunctions M

open import Categories.Object.Terminal Split
open import Categories.Object.Initial Split
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
             id ∘ M.μ.η _                          ≈⟨ id-comm-sym C ⟩
             M.μ.η _  ∘ id                         ≈⟨ refl⟩∘⟨ Equiv.sym M.F.identity ⟩
             M.μ.η _ ∘ M.F.₁ id                    ≈⟨ Equiv.sym identityʳ ⟩
             (M.μ.η _ ∘ M.F.₁ id) ∘ id             ≈⟨ assoc ⟩
             M.μ.η _ ∘ M.F.₁ id ∘ id               ≈⟨ refl⟩∘⟨ refl⟩∘⟨ Equiv.sym M.F.identity ⟩
             M.μ.η _ ∘ M.F.₁ id ∘ M.F.₁ id         ≈⟨ refl⟩∘⟨ refl⟩∘⟨ M.F.F-resp-≈ (Equiv.sym M.F.identity) ⟩
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
  ; μ-eq = begin
             M.F.₁ id ∘ M.μ.η _                                         ≈⟨ M.F.identity ⟩∘⟨refl ⟩
             id ∘ M.μ.η _                                               ≈⟨ id-comm-sym C ⟩
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
  ; μ-comp = λ { {x} →
    let open C
        open C.HomReasoning in
      Equiv.sym (begin
        G.F₁ D.id ∘ (G.F₁ (adj.counit.η (F.₀ x) D.∘ F.₁ (GF≃M.⇐.η x ∘ M.F.F₁ id)) ∘ G.F₁ D.id ∘ adj.unit.η (M.F.F₀ x)) ∘ M.F.F₁ id
          ≈⟨ elimˡ C G.identity ⟩
        (G.F₁ (adj.counit.η (F.₀ x) D.∘ F.₁ (GF≃M.⇐.η x ∘ M.F.F₁ id)) ∘ G.F₁ D.id ∘ adj.unit.η (M.F.F₀ x)) ∘ M.F.F₁ id
          ≈⟨ elimʳ C M.F.identity ⟩
        G.F₁ (adj.counit.η (F.₀ x) D.∘ F.₁ (GF≃M.⇐.η x ∘ M.F.F₁ id)) ∘ G.F₁ D.id ∘ adj.unit.η (M.F.F₀ x)
          ≈⟨ refl⟩∘⟨ elimˡ C G.identity ⟩
        (G.F₁ ( adj.counit.η (F.₀ x) D.∘  F.₁ (GF≃M.⇐.η x ∘ M.F.F₁ id)) ∘ adj.unit.η (M.F.F₀ x))
          ≈⟨ (G.homomorphism ⟩∘⟨refl) ⟩
        ((G.F₁ (adj.counit.η (F.₀ x)) ∘ Functor.F₁ (G ∘F F) (GF≃M.⇐.η x ∘ M.F.F₁ id)) ∘ adj.unit.η (M.F.F₀ x))
          ≈⟨ pullʳ C (adj.unit.sym-commute _) ⟩
        (G.F₁ (adj.counit.η (F.₀ x)) ∘ adj.unit.η (G.F₀ (F.₀ x)) ∘ GF≃M.⇐.η x ∘ M.F.F₁ id)
          ≈⟨ sym-assoc ⟩
        (G.F₁ (adj.counit.η (F.₀ x)) ∘ adj.unit.η (G.F₀ (F.₀ x))) ∘ GF≃M.⇐.η x ∘ M.F.F₁ id
          ≈⟨ elimˡ C adj.zag ⟩
        (GF≃M.⇐.η x ∘ M.F.F₁ id)
          ≈⟨ elimʳ C M.F.identity ⟩
        GF≃M.⇐.η x ∎) }
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

Kl-initial : IsInitial Kl-object
Kl-initial = record
  { ! = !
  ; !-unique = λ { {A} H → niHelper (
    let module A = SplitObj A
        module K = SplitObj Kl-object
        module H = Split⇒ H
        module Γ = NaturalIsomorphism H.Γ
        module CH = C.HomReasoning
        open Category A.D in
    record
      { η   = Γ.⇐.η
      ; η⁻¹ = Γ.⇒.η
      ; commute = λ f → let open A.D.HomReasoning in
          begin
            Γ.⇐.η _ ∘ A.adj.counit.η (A.F.F₀ _) ∘ A.F.F₁ (A.GF≃M.⇐.η _ C.∘ f)
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ A.F.F-resp-≈ ((H.μ-comp CH.⟩∘⟨refl) CH.○ (C.assoc CH.○ (CH.refl⟩∘⟨ C.assoc))) ⟩
            Γ.⇐.η _ ∘ A.adj.counit.η (A.F.F₀ _) ∘ A.F.F₁ (A.G.₁ (Γ.⇒.η _) C.∘ (A.G.₁ (H.H.F₁ (M.F.F₁ C.id)) C.∘ (A.G.₁ (Γ.⇐.η (M.F.F₀ _)) C.∘ A.adj.unit.η (M.F.F₀ _))) C.∘ M.F.F₁ C.id C.∘ f)
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ A.F.homomorphism ⟩
            Γ.⇐.η _ ∘ A.adj.counit.η (A.F.F₀ _) ∘ Functor.F₁ (A.F Categories.Functor.∘F A.G) (Γ.⇒.η _) ∘ A.F.F₁ ((A.G.₁ (H.H.F₁ (M.F.F₁ C.id)) C.∘ A.G.₁ (Γ.⇐.η (M.F.F₀ _)) C.∘ A.adj.unit.η (M.F.F₀ _)) C.∘ M.F.F₁ C.id C.∘ f)
              ≈⟨ refl⟩∘⟨ pullˡ A.D (A.adj.counit.commute _) ⟩
            Γ.⇐.η _ ∘ (Γ.⇒.η _ ∘ A.adj.counit.η (H.H.F₀ (Functor.₀ K.F _))) ∘ A.F.F₁ ((A.G.₁ (H.H.F₁ (M.F.F₁ C.id)) C.∘ (A.G.₁ (Γ.⇐.η (M.F.F₀ _)) C.∘ A.adj.unit.η (M.F.F₀ _))) C.∘ M.F.F₁ C.id C.∘ f)
              ≈⟨ refl⟩∘⟨ assoc ⟩
            Γ.⇐.η _ ∘ Γ.⇒.η _ ∘ A.adj.counit.η (H.H.F₀ (Functor.₀ K.F _)) ∘ A.F.F₁ ((A.G.₁ (H.H.F₁ (M.F.F₁ C.id)) C.∘ A.G.₁ (Γ.⇐.η (M.F.F₀ _)) C.∘ A.adj.unit.η (M.F.F₀ _)) C.∘ M.F.F₁ C.id C.∘ f)
              ≈⟨ cancelˡ A.D (Γ.iso.isoˡ _) ⟩
            A.adj.counit.η (H.H.F₀ (Functor.₀ K.F _)) ∘ A.F.F₁ ((A.G.₁ (H.H.F₁ (M.F.F₁ C.id)) C.∘ (A.G.₁ (Γ.⇐.η (M.F.F₀ _)) C.∘ A.adj.unit.η (M.F.F₀ _))) C.∘ M.F.F₁ C.id C.∘ f)
              ≈⟨ refl⟩∘⟨ A.F.homomorphism ⟩
            A.adj.counit.η (H.H.F₀ (Functor.₀ K.F _)) ∘ A.F.F₁ (A.G.₁ (H.H.F₁ (M.F.F₁ C.id)) C.∘ A.G.₁ (Γ.⇐.η (M.F.F₀ _)) C.∘ A.adj.unit.η (M.F.F₀ _)) ∘ A.F.F₁ (M.F.F₁ C.id C.∘ f)
              ≈⟨ refl⟩∘⟨ pushˡ A.D A.F.homomorphism ⟩
            A.adj.counit.η (H.H.F₀ (Functor.₀ K.F _)) ∘ Functor.F₁ (A.F Categories.Functor.∘F A.G) (H.H.F₁ (M.F.F₁ C.id)) ∘ A.F.F₁ (A.G.₁ (Γ.⇐.η (M.F.F₀ _)) C.∘ A.adj.unit.η (M.F.F₀ _)) ∘ A.F.F₁ (M.F.F₁ C.id C.∘ f)
              ≈⟨ extendʳ A.D (A.adj.counit.commute _) ⟩
            H.H.F₁ (M.F.F₁ C.id) ∘ A.adj.counit.η (H.H.F₀ (Functor.₀ K.F (M.F.F₀ _))) ∘ A.F.F₁ (A.G.₁ (Γ.⇐.η (M.F.F₀ _)) C.∘ A.adj.unit.η (M.F.F₀ _)) ∘ A.F.F₁ (M.F.F₁ C.id C.∘ f)
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ A.D A.F.homomorphism ⟩
            H.H.F₁ (M.F.F₁ C.id) ∘ A.adj.counit.η (H.H.F₀ (Functor.₀ K.F (M.F.F₀ _))) ∘ Functor.F₁ (A.F Categories.Functor.∘F A.G) (Γ.⇐.η (M.F.F₀ _)) ∘ A.F.F₁ (A.adj.unit.η (M.F.F₀ _)) ∘ A.F.F₁ (M.F.F₁ C.id C.∘ f)
              ≈⟨ refl⟩∘⟨ extendʳ A.D (A.adj.counit.commute _) ⟩
            H.H.F₁ (M.F.F₁ C.id) ∘ Γ.⇐.η (M.F.F₀ _) ∘ A.adj.counit.η (A.F.F₀ (M.F.F₀ _)) ∘ A.F.F₁ (A.adj.unit.η (M.F.F₀ _)) ∘ A.F.F₁ (M.F.F₁ C.id C.∘ f)
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ A.D A.adj.zig ⟩
            H.H.F₁ (M.F.F₁ C.id) ∘ Γ.⇐.η (M.F.F₀ _) ∘ id ∘ A.F.F₁ (M.F.F₁ C.id C.∘ f)
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (identityˡ ○ A.F.F-resp-≈ (elimˡ C M.F.identity)) ⟩
            H.H.F₁ (M.F.F₁ C.id) ∘ Γ.⇐.η (M.F.F₀ _) ∘ A.F.F₁ f
              ≈⟨ refl⟩∘⟨ Γ.⇐.commute f ⟩
            H.H.F₁ (M.F.F₁ C.id) ∘ H.H.F₁ (M.η.η (M.F.F₀ (Functor.₀ K.F _)) C.∘ f) ∘ Γ.⇐.η _
              ≈⟨ pullˡ A.D (Equiv.sym H.H.homomorphism) ⟩
            H.H.F₁ ((M.μ.η (Functor.₀ K.F _) C.∘ M.F.F₁ (M.F.F₁ C.id)) C.∘  M.η.η (M.F.F₀ (Functor.₀ K.F _)) C.∘ f) ∘ Γ.⇐.η _
              ≈⟨ H.H.F-resp-≈ (elimʳ C (M.F.F-resp-≈ M.F.identity CH.○ M.F.identity) CH.⟩∘⟨refl) ⟩∘⟨refl ⟩
            H.H.F₁ (M.μ.η (Functor.₀ K.F _) C.∘  M.η.η (M.F.F₀ (Functor.₀ K.F _)) C.∘ f) ∘ Γ.⇐.η _
              ≈⟨ H.H.F-resp-≈ (pullˡ C M.identityʳ CH.○ C.identityˡ) ⟩∘⟨refl ⟩
            H.H.F₁ f ∘ Γ.⇐.η _ ∎
      ; iso = NaturalIsomorphism.iso (sym H.Γ)
      })
    }
  }
