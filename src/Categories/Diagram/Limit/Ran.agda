{-# OPTIONS --without-K --safe #-}

module Categories.Diagram.Limit.Ran where

open import Level
open import Data.Product using (Σ)

open import Categories.Category
open import Categories.Category.Complete
open import Categories.Category.Construction.Cones
open import Categories.Category.Construction.Comma
open import Categories.Category.Construction.Properties.Comma
open import Categories.Diagram.Cone.Properties
open import Categories.Diagram.Limit.Properties
open import Categories.Functor
open import Categories.Functor.Properties
open import Categories.Functor.Construction.Constant
open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.Equivalence using () renaming (_≃_ to _≊_)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; _≃_; module ≃; _ⓘˡ_)
open import Categories.Kan
open import Categories.Diagram.Limit

import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level
    C D E : Category o ℓ e

-- construct a Ran from a limit
module _ {o ℓ e o′ ℓ′ e′} {C : Category o′ ℓ′ e′} {D : Category o ℓ e}
         (F : Functor C D) (X : Functor C E) (Com : Complete (o′ ⊔ ℓ) (ℓ′ ⊔ e) e′ E) where
  private
    module C = Category C
    module D = Category D
    module E = Category E
    module F = Functor F
    module X = Functor X
    open Limit
    open Cone renaming (commute to K-commute)
    open Cone⇒ renaming (commute to ⇒-commute)
    open Mor E

    G   : (d : D.Obj) → Functor (d ↙ F) E
    G d   = X ∘F Cod (const! d) F
    ⊤Gd : ∀ d → Limit (G d)
    ⊤Gd d = Com (G d)
    module ⊤Gd d = Limit (⊤Gd d)
    f↙F : ∀ {Y Z} (f : Y D.⇒ Z) → Functor (Z ↙ F) (Y ↙ F)
    f↙F   = along-natˡ′ F

    Gf≃ : ∀ {Y Z} (f : Y D.⇒ Z) → G Z ≃ G Y ∘F f↙F f
    Gf≃ f = record
      { F⇒G = ntHelper record
        { η       = λ _ → X.F₁ C.id
        ; commute = λ _ → [ X ]-resp-square id-comm-sym
        }
      ; F⇐G = ntHelper record
        { η       = λ _ → X.F₁ C.id
        ; commute = λ _ → [ X ]-resp-square id-comm-sym
        }
      ; iso = λ _ → record
        { isoˡ = [ X ]-resp-∘ C.identity² ○ X.identity
        ; isoʳ = [ X ]-resp-∘ C.identity² ○ X.identity
        }
      }
      where open MR C
            open E.HomReasoning

    limY⇒limZ∘ : ∀ {Y Z} (f : Y D.⇒ Z) → Cones (G Y ∘F f↙F f) [ F-map-Coneʳ (f↙F f) (limit (Com (G Y))) , limit (Com (G Y ∘F f↙F f)) ]
    limY⇒limZ∘ {Y} f     = F⇒arr Com (f↙F f) (G Y)
    limZ∘≅limZ : ∀ {Y Z} (f : Y D.⇒ Z) → apex (⊤Gd Z) ≅ apex (Com (G Y ∘F f↙F f))
    limZ∘≅limZ {Y} {Z} f = ≃⇒lim≅ (Gf≃ f) (⊤Gd Z) (Com _)

  limit-is-ran : Ran F X
  limit-is-ran = record
    { R        = R
    ; ε        = ε
    ; δ        = δ
    ; δ-unique = λ {M γ} δ′ eq → δ-unique {M} {γ} δ′ eq
    ; commutes = commutes
    }
    where open MR E
          open E.HomReasoning
          open D.HomReasoning using () renaming (_○_ to _●_ ; ⟺ to ⟷)

          R₀ : D.Obj → E.Obj
          R₀ d = apex (⊤Gd d)
          R₁ : ∀ {A B} → D [ A , B ] → E [ R₀ A , R₀ B ]
          R₁ {A} f = _≅_.to (limZ∘≅limZ f) E.∘ arr (limY⇒limZ∘ f)

          proj-red : ∀ {Y Z} K (f : Y D.⇒ Z) → ⊤Gd.proj Z K E.∘ R₁ f E.≈ ⊤Gd.proj Y (record { f = D.id D.∘ CommaObj.f K D.∘ f })
          proj-red {Y} {Z} K f = begin
            ⊤Gd.proj Z K E.∘ R₁ f                                 ≈⟨ pullˡ (⇒-commute (≃⇒Cone⇒ (≃.sym (Gf≃ f)) (Com _) (⊤Gd Z))) ⟩
            (X.F₁ C.id E.∘ proj (Com _) K) E.∘ arr (limY⇒limZ∘ f) ≈⟨ pullʳ (⇒-commute (limY⇒limZ∘ f)) ⟩
            X.F₁ C.id E.∘ ⊤Gd.proj Y _                            ≈⟨ elimˡ X.identity ⟩
            ⊤Gd.proj Y _                                          ∎

          proj≈ : ∀ {d b} {f g : d D.⇒ F.F₀ b} → f D.≈ g → ⊤Gd.proj d record { f = f } E.≈ ⊤Gd.proj d record { f = g }
          proj≈ {d} {b} {f} {g} eq = begin
            ⊤Gd.proj d _               ≈⟨ introˡ X.identity ⟩
            X.F₁ C.id E.∘ ⊤Gd.proj d _ ≈⟨ K-commute _ (⊤Gd.limit d) (record { h = C.id ; commute = D.∘-resp-≈ F.identity eq ● MR.id-comm-sym D }) ⟩
            ⊤Gd.proj d _               ∎
          
          R : Functor D E
          R = record
            { F₀           = R₀
            ; F₁           = R₁
            ; identity     = λ {d} → terminal.⊤-id (⊤Gd d) record
              { commute = λ {Z} → begin
                ⊤Gd.proj d Z ∘ R₁ D.id                                   ≈⟨ proj-red Z D.id ⟩
                ⊤Gd.proj d record { f = D.id D.∘ CommaObj.f Z D.∘ D.id } ≈⟨ proj≈ (D.identityˡ ● D.identityʳ) ⟩
                ⊤Gd.proj d Z                                             ∎
              }
            ; homomorphism = λ {Y Z W} {f g} →
              terminal.!-unique₂ (⊤Gd W)
                {let module ⊤GY = Cone _ (⊤Gd.limit Y)
                     module H   = Functor (f↙F (g D.∘ f))
                 in record
                 { apex = record
                   { ψ       = λ K → ⊤GY.ψ (H.F₀ K)
                   ; commute = λ h → ⊤GY.commute (H.F₁ h)
                   }
                 }}
                {record
                  { arr     = R₁ (g D.∘ f)
                  ; commute = λ {K} → proj-red K (g D.∘ f)
                  }}
                {record
                  { arr     = R₁ g ∘ R₁ f
                  ; commute = λ {K} → begin
                    ⊤Gd.proj W K ∘ R₁ g ∘ R₁ f
                      ≈⟨ sym-assoc ⟩
                    (⊤Gd.proj W K ∘ R₁ g) ∘ R₁ f
                      ≈⟨ proj-red K g ⟩∘⟨refl ⟩
                    ⊤Gd.proj Z record { f = D.id D.∘ CommaObj.f K D.∘ g } ∘ R₁ f
                      ≈⟨ proj-red _ f ⟩
                    ⊤Gd.proj Y record { f = D.id D.∘ (D.id D.∘ CommaObj.f K D.∘ g) D.∘ f }
                      ≈⟨ proj≈ (D.identityˡ ● (MR.assoc²' D)) ⟩
                    ⊤Gd.proj Y record { f = D.id D.∘ CommaObj.f K D.∘ g D.∘ f }
                      ∎
                  }}
            ; F-resp-≈     = λ {Y Z} {f g} eq →
              terminal.!-unique₂ (⊤Gd Z)
                {let module ⊤GY = Cone _ (⊤Gd.limit Y)
                     module H = Functor (f↙F f)
                 in record
                    { apex = record
                      { ψ       = λ K → ⊤GY.ψ (H.F₀ K)
                      ; commute = λ h → ⊤GY.commute (H.F₁ h)
                      }
                    }}
                {record
                  { arr     = R₁ f
                  ; commute = F-resp-≈-commute D.Equiv.refl
                  }}
                {record
                  { arr     = R₁ g
                  ; commute = F-resp-≈-commute eq
                  }}
            }
            where open E
                  F-resp-≈-commute : ∀ {Y Z} {K : Category.Obj (Z ↙ F)} {f g : Y D.⇒ Z} → f D.≈ g →
                                       ⊤Gd.proj Z K ∘ R₁ g ≈ ⊤Gd.proj Y record { f = D.id D.∘ CommaObj.f K D.∘ f }
                  F-resp-≈-commute {Y} {Z} {K} {f} {g} eq = begin
                    ⊤Gd.proj Z K ∘ R₁ g ≈⟨ proj-red K g ⟩
                    ⊤Gd.proj Y _        ≈⟨ proj≈ (D.∘-resp-≈ʳ (D.∘-resp-≈ʳ (D.Equiv.sym eq))) ⟩
                    ⊤Gd.proj Y _        ∎

          ε : NaturalTransformation (R ∘F F) X
          ε = ntHelper record
            { η       = λ c → ⊤Gd.proj (F.F₀ c) record { f = D.id }
            ; commute = λ {Y Z} f → begin
              ⊤Gd.proj (F.F₀ Z) _ ∘ Functor.F₁ (R ∘F F) f ≈⟨ proj-red _ (F.F₁ f) ⟩
              ⊤Gd.proj (F.F₀ Y) _                         ≈˘⟨ K-commute _ (⊤Gd.limit (F.F₀ Y)) record { h = f ; commute = ⟷ (D.∘-resp-≈ˡ D.identityˡ ● D.∘-resp-≈ˡ D.identityˡ) } ⟩
              X.F₁ f ∘ ⊤Gd.proj (F.F₀ Y) _                ∎
            }
            where open E

          δ-Cone : ∀ d (M : Functor D E) → NaturalTransformation (M ∘F F) X → Cone (G d)
          δ-Cone d M γ = record
            { apex = record
              { ψ       = λ K → γ.η (CommaObj.β K) E.∘ M.F₁ (CommaObj.f K) 
              ; commute = λ {Y Z} f → begin
                X.F₁ (Comma⇒.h f) E.∘ γ.η (CommaObj.β Y) E.∘ M.F₁ (CommaObj.f Y)
                  ≈˘⟨ pushˡ (γ.commute (Comma⇒.h f)) ⟩
                (γ.η (CommaObj.β Z) E.∘ M.F₁ (F.F₁ (Comma⇒.h f))) E.∘ M.F₁ (CommaObj.f Y)
                  ≈⟨ pullʳ ([ M ]-resp-∘ (Comma⇒.commute f ● D.identityʳ)) ⟩
                γ.η (CommaObj.β Z) E.∘ M.F₁ (CommaObj.f Z)
                  ∎
              }
            }
            where module M = Functor M
                  module γ = NaturalTransformation γ

          δ : (M : Functor D E) → NaturalTransformation (M ∘F F) X → NaturalTransformation M R
          δ M γ = ntHelper record
            { η       = λ d → ⊤Gd.rep d (δ-Cone d M γ)
            ; commute = λ {Y Z} f →
              terminal.!-unique₂ (⊤Gd Z)
                {record
                  { apex = record
                    { ψ       = λ W → δ-Cone.ψ Z W E.∘ M.F₁ f
                    ; commute = λ {W V} g → begin
                      X.F₁ (Comma⇒.h g) E.∘ (γ.η (CommaObj.β W) E.∘ M.F₁ (CommaObj.f W)) E.∘ M.F₁ f
                        ≈⟨ E.sym-assoc ⟩
                      (X.F₁ (Comma⇒.h g) E.∘ γ.η (CommaObj.β W) E.∘ M.F₁ (CommaObj.f W)) E.∘ M.F₁ f
                        ≈⟨ δ-Cone.commute Z g ⟩∘⟨refl ⟩
                      (γ.η (CommaObj.β V) E.∘ M.F₁ (CommaObj.f V)) E.∘ M.F₁ f
                        ∎
                    }
                  }}
                {record
                  { arr     = ⊤Gd.rep Z (δ-Cone Z M γ) E.∘ M.F₁ f
                  ; commute = pullˡ (⇒-commute (⊤Gd.rep-cone Z (δ-Cone Z M γ)))
                  }}
                {record
                  { arr     = R₁ f E.∘ ⊤Gd.rep Y (δ-Cone Y M γ)
                  ; commute = λ {W} → begin
                    ⊤Gd.proj Z W E.∘ R₁ f E.∘ ⊤Gd.rep Y (δ-Cone Y M γ)
                      ≈⟨ pullˡ (proj-red W f) ⟩
                    ⊤Gd.proj Y (record { f = D.id D.∘ CommaObj.f W D.∘ f }) E.∘ ⊤Gd.rep Y (δ-Cone Y M γ)
                      ≈⟨ ⇒-commute (⊤Gd.rep-cone Y (δ-Cone Y M γ)) ⟩
                    γ.η (CommaObj.β W) E.∘ M.F₁ (D.id D.∘ CommaObj.f W D.∘ f)
                      ≈˘⟨ refl⟩∘⟨ [ M ]-resp-∘ (⟷ D.identityˡ) ⟩
                    γ.η (CommaObj.β W) E.∘ M.F₁ (CommaObj.f W) E.∘ M.F₁ f
                      ≈⟨ E.sym-assoc ⟩
                    (γ.η (CommaObj.β W) E.∘ M.F₁ (CommaObj.f W)) E.∘ M.F₁ f
                      ∎
                  }}
            }
            where module M        = Functor M
                  module γ        = NaturalTransformation γ
                  module δ-Cone d = Cone _ (δ-Cone d M γ)

          δ-unique : ∀ {M : Functor D E} {α : NaturalTransformation (M ∘F F) X}
                       (δ′ : NaturalTransformation M R) → α ≊ ε ∘ᵥ δ′ ∘ʳ F → δ′ ≊ δ M α
          δ-unique {M} {γ} δ′ eq {d} = ⟺ (⊤Gd.terminal.!-unique d record
            { arr     = δ′.η d
            ; commute = λ {W} → begin
              ⊤Gd.proj d W E.∘ δ′.η d
                ≈˘⟨ proj≈ (D.identityˡ ● D.identityˡ) ⟩∘⟨refl ⟩
              ⊤Gd.proj d (record { f = D.id D.∘ D.id D.∘ CommaObj.f W }) E.∘ δ′.η d
                ≈˘⟨ pullˡ (proj-red _ (CommaObj.f W)) ⟩
              ⊤Gd.proj (F.F₀ (CommaObj.β W)) _ E.∘ R₁ (CommaObj.f W) E.∘ δ′.η d
                ≈˘⟨ pullʳ (δ′.commute (CommaObj.f W)) ⟩
              (⊤Gd.proj (F.F₀ (CommaObj.β W)) (record { f = D.id}) E.∘ δ′.η (F.F₀ (CommaObj.β W))) E.∘ M.F₁ (CommaObj.f W)
                ≈˘⟨ eq ⟩∘⟨refl ⟩
              γ.η (CommaObj.β W) E.∘ M.F₁ (CommaObj.f W)
                ∎
            })
            where module M  = Functor M
                  module γ  = NaturalTransformation γ
                  module δ′ = NaturalTransformation δ′

          commutes : (M : Functor D E) (α : NaturalTransformation (M ∘F F) X) → α ≊ ε ∘ᵥ δ M α ∘ʳ F
          commutes M γ {c} = ⟺ (⇒-commute (⊤Gd.rep-cone (F.F₀ c) (δ-Cone (F.F₀ c) M γ)) ○ elimʳ M.identity)
            where module M  = Functor M
                  module γ  = NaturalTransformation γ
