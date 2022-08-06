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
                let 𝐹 = F.F₁ in
                let 𝐺 = G.F₁ in
                let ε x = adj.counit.η x in
                let μ x = M.μ.η x in
                let M⇒GF x = GF≃M.⇐.η x in
                let GF⇒M x = GF≃M.⇒.η x in
                let 𝑓 = M⇒GF _ C.∘ f in
                let 𝑔 = M⇒GF _ C.∘ g in
                let lemma : 𝐹 (𝐺 (ε (F.F₀ Z))) ≈ ε (F.F₀ (G.F₀ (F.F₀ Z)))
                    lemma = {!   !} in
                begin
                  -- Push f externally
                  ε _ ∘ 𝐹 (M⇒GF _ C.∘ (μ _ C.∘ M.F.F₁ g) C.∘ f)        ≈⟨ refl⟩∘⟨ F.F-resp-≈ {! DMR.assoc²''  !} ⟩
                  ε _ ∘ 𝐹 ((M⇒GF _ C.∘ μ _ C.∘ M.F.F₁ g) C.∘ f)        ≈⟨ refl⟩∘⟨ F.homomorphism ⟩
                  ε _ ∘ 𝐹 (M⇒GF _ C.∘ μ _ C.∘ M.F.F₁ g)  ∘ 𝐹 f         ≈⟨ refl⟩∘⟨ F.F-resp-≈ C.sym-assoc ⟩∘⟨refl ⟩
                  ε _ ∘ 𝐹 ((M⇒GF _ C.∘ μ _) C.∘ M.F.F₁ g)  ∘ 𝐹 f       ≈⟨ refl⟩∘⟨ F.F-resp-≈ (μ-eq CHR.⟩∘⟨refl) ⟩∘⟨refl ⟩
                  -- Switch from M to GF as close to g as possible
                  ε _ ∘ 𝐹 ((𝐺 (ε (F.₀ _)) C.∘ M⇒GF _ C.∘ M.F.F₁ (M⇒GF _)) C.∘ M.F.F₁ g)  ∘ 𝐹 f ≈⟨ refl⟩∘⟨ F.F-resp-≈ {!   !} ⟩∘⟨refl ⟩
                  ε _ ∘ 𝐹 (𝐺 (ε (F.₀ _)) C.∘ M⇒GF _ C.∘ (M.F.F₁ (M⇒GF _) C.∘ M.F.F₁ g))  ∘ 𝐹 f ≈⟨ refl⟩∘⟨ F.F-resp-≈ (CHR.refl⟩∘⟨ CHR.refl⟩∘⟨ C.Equiv.sym M.F.homomorphism) ⟩∘⟨refl ⟩
                  ε _ ∘ 𝐹 (𝐺 (ε (F.₀ _)) C.∘ M⇒GF _ C.∘ (M.F.F₁ 𝑔))  ∘ 𝐹 f        ≈⟨ refl⟩∘⟨ F.F-resp-≈ (CHR.refl⟩∘⟨ GF≃M.⇐.commute _) ⟩∘⟨refl ⟩
                  -- Switch from M to GF as close to f as possible
                  ε _ ∘ 𝐹 (𝐺 (ε (F.₀ _)) C.∘ 𝐺 (𝐹 𝑔) C.∘ M⇒GF _) ∘ 𝐹 f          ≈⟨ ((refl⟩∘⟨ F.F-resp-≈ C.sym-assoc ⟩∘⟨refl)) ⟩
                  ε _ ∘ 𝐹 ((𝐺 (ε (F.₀ _)) C.∘ 𝐺 (𝐹 𝑔)) C.∘ M⇒GF _) ∘ 𝐹 f        ≈⟨ (refl⟩∘⟨ F.homomorphism ⟩∘⟨refl) ⟩
                  ε _ ∘ (𝐹 ((𝐺 (ε (F.₀ _)) C.∘ 𝐺 (𝐹 𝑔))) ∘ 𝐹 (M⇒GF _)) ∘ 𝐹 f    ≈⟨ (refl⟩∘⟨ assoc) ⟩
                  ε _ ∘ 𝐹 ((𝐺 (ε (F.₀ _)) C.∘ 𝐺 (𝐹 𝑔))) ∘ 𝐹 (M⇒GF _) ∘ 𝐹 f     ≈⟨ (refl⟩∘⟨ (refl⟩∘⟨ Equiv.sym F.homomorphism)) ⟩
                  ε _ ∘ 𝐹 ((𝐺 (ε (F.₀ _)) C.∘ 𝐺 (𝐹 𝑔))) ∘ 𝐹 𝑓                   ≈⟨ (refl⟩∘⟨ F.homomorphism ⟩∘⟨refl) ⟩
                  -- Solve the adjunction
                  ε _ ∘ (𝐹 (𝐺 (ε (F.₀ _))) ∘ 𝐹 (𝐺 (𝐹 𝑔))) ∘ 𝐹 𝑓                 ≈⟨ (refl⟩∘⟨ (lemma ⟩∘⟨refl) ⟩∘⟨refl) ⟩
                  ε _ ∘ ((ε _) ∘ 𝐹 (𝐺 (𝐹 𝑔))) ∘ 𝐹 𝑓                             ≈⟨ (refl⟩∘⟨ adj.counit.commute _ ⟩∘⟨refl) ⟩
                  ε _ ∘ (𝐹 𝑔 ∘ ε _) ∘ 𝐹 𝑓                                       ≈⟨ DMR.assoc²'' ⟩
                  (ε _ ∘ 𝐹 𝑔) ∘ ε _ ∘ 𝐹 𝑓                                       ∎
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
