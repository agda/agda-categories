{-# OPTIONS --without-K --safe #-}

module Categories.Diagram.Limit.Ran where

open import Level
open import Data.Product using (Σ)

open import Categories.Category
open import Categories.Category.Complete
import Categories.Category.Construction.Cones as ConesCat
open import Categories.Category.Construction.Comma
open import Categories.Category.Construction.Properties.Comma
open import Categories.Category.Instance.One using (One)
open import Categories.Diagram.Cone using (Cone; Cone⇒)
open import Categories.Diagram.Cone.Properties
open import Categories.Diagram.Limit
open import Categories.Diagram.Limit.Properties
open import Categories.Functor
open import Categories.Functor.Properties
open import Categories.Functor.Construction.Constant
open import Categories.Kan
open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.Equivalence using () renaming (_≃_ to _≊_)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; _≃_; module ≃; _ⓘˡ_)
open import Categories.Object.Terminal using (Terminal)

import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR

-- construct a Ran from a limit
module _ {o ℓ e o′ ℓ′ e′ o″ ℓ″ e″} {C : Category o′ ℓ′ e′} {D : Category o ℓ e} {E : Category o″ ℓ″ e″}
         (F : Functor C D) (X : Functor C E) (Com : Complete (o′ ⊔ ℓ) (ℓ′ ⊔ e) e′ E) where
  private
    module C = Category C
    module D = Category D
    module E = Category E
    module F = Functor F
    module X = Functor X
    open Limit using (limit; proj; apex; module terminal)
    open Cone using () renaming (commute to K-commute)
    open ConesCat.Cone⇒ using (arr) renaming (commute to ⇒-commute)
    open Mor E using (_≅_)

    G   : (d : D.Obj) → Functor (d ↙ F) E
    G d = X ∘F Cod {A = One} {B = C} {C = D} (const! d) F

    ⊤Gd : (d : D.Obj) → Limit (G d)
    ⊤Gd d = Com (G d)
    module ⊤Gd d = Limit (⊤Gd d) using (proj; limit; rep; rep-cone; apex; module terminal)

    f↙F : {Y Z : D.Obj} (f : Y D.⇒ Z) → Functor (Z ↙ F) (Y ↙ F)
    f↙F   =  along-natˡ′ F

    Gf≃ : {Y Z : D.Obj} (f : Y D.⇒ Z) → G Z ≃ G Y ∘F f↙F f
    Gf≃ f = record
      { F⇒G = record
        { η           = λ z/F →  let j = CommaObj.β z/F in X.₁ {j} C.id -- help inference a bit
        ; commute     = λ _ → [ X ]-resp-square id-comm-sym
        ; sym-commute = λ _ → [ X ]-resp-square id-comm
        }
      ; F⇐G = record
        { η       = λ _ → X.₁ C.id
        ; commute = λ _ → [ X ]-resp-square id-comm-sym
        ; sym-commute = λ _ → [ X ]-resp-square id-comm
        }
      ; iso = λ _ → record
        { isoˡ = [ X ]-resp-∘ C.identity² ○ X.identity
        ; isoʳ = [ X ]-resp-∘ C.identity² ○ X.identity
        }
      }
      where open MR C using (id-comm-sym; id-comm)
            open E.HomReasoning using (_○_)

    Compl : {Y Z : D.Obj} (f : Y D.⇒ Z) → Limit (G Y ∘F f↙F f)
    Compl {Y} f = Com (G Y ∘F f↙F f)

    limY⇒limZ∘ : {Y Z : D.Obj} (f : Y D.⇒ Z) →
        ConesCat.Cones (G Y ∘F f↙F f) [ F-map-Coneʳ (f↙F f) (limit (Com (G Y))) , limit (Compl f) ]
    limY⇒limZ∘ {Y} f = F⇒arr Com (f↙F f) (G Y)

    limZ∘≅limZ : {Y Z : D.Obj} (f : Y D.⇒ Z) → ⊤Gd.apex Z ≅ apex (Compl f)
    limZ∘≅limZ {Y} {Z} f = ≃⇒lim≅ (Gf≃ f) (⊤Gd Z) (Compl f)

  limit-is-ran : Ran F X
  limit-is-ran = record
    { R        = R
    ; ε        = ε
    ; δ        = δ
    ; δ-unique = λ {M γ} δ′ eq → δ-unique {M} {γ} δ′ eq
    ; commutes = commutes
    }
    where
    open MR E
    open E.HomReasoning
    module DH = D.HomReasoning

    R₀ : D.Obj → E.Obj
    R₀ = ⊤Gd.apex
    R₁ : ∀ {A B} → D [ A , B ] → E [ R₀ A , R₀ B ]
    R₁ {A} f = _≅_.to (limZ∘≅limZ f) E.∘ arr (limY⇒limZ∘ f)

    ↙⇒ : {Y Z : D.Obj} (K : CommaObj {A = One} {C} {D} (const Z) F) (f : Y D.⇒ Z) → CommaObj {A = One} {C} {D} (const Y) F
    ↙⇒ K f = record { β = CommaObj.β K; f = D.id D.∘ CommaObj.f K D.∘ f }

    proj-red : {Y Z : D.Obj} (K : CommaObj (const Z) F) (f : Y D.⇒ Z) → ⊤Gd.proj Z K E.∘ R₁ f E.≈ ⊤Gd.proj Y (↙⇒ K f)
    proj-red {Y} {Z} K f = begin
      ⊤Gd.proj Z K E.∘ R₁ f                                  ≈⟨ pullˡ (⇒-commute (≃⇒Cone⇒ (≃.sym (Gf≃ f)) (Compl f) (⊤Gd Z))) ⟩
      (X.₁ C.id E.∘ proj (Compl f) K) E.∘ arr (limY⇒limZ∘ f) ≈⟨ pullʳ (⇒-commute (limY⇒limZ∘ f)) ⟩
      X.₁ C.id E.∘ ⊤Gd.proj Y f/K                            ≈⟨ elimˡ X.identity ⟩
      ⊤Gd.proj Y f/K                                         ∎
      where
      f/K : CommaObj {A = One} {C} {D} (const Y) F
      f/K = ↙⇒ K f

    commaF : {d : D.Obj} {c : C.Obj} (f : d D.⇒ F.₀ c) → CommaObj {A = One} {C} {D} (const d) F
    commaF f = record { f = f }

    proj≈ : {d : D.Obj} {b : C.Obj} {f g : d D.⇒ F.₀ b} → f D.≈ g → ⊤Gd.proj d (commaF f) E.≈ ⊤Gd.proj d (commaF g)
    proj≈ {d} {b} {f} {g} eq = begin
      ⊤Gd.proj d (commaF f)              ≈⟨ introˡ X.identity ⟩
      X.₁ C.id E.∘ ⊤Gd.proj d (commaF f) ≈⟨ K-commute (⊤Gd.limit d) C⇒ ⟩
      ⊤Gd.proj d (commaF g)               ∎
      where
      C⇒ : Comma⇒ (commaF f) (commaF g)
      C⇒ = record
             { h = C.id
             ; commute = DH.begin
               F.₁ C.id D.∘ f   DH.≈⟨ D.∘-resp-≈ F.identity eq ⟩
               D.id D.∘ g       DH.≈⟨ MR.id-comm-sym D  ⟩
               g D.∘ D.id       DH.∎
              }

    ConesGd : {d : D.Obj} → Functor (Comma {A = One} (const d) F) E
    ConesGd {d} = X ∘F Cod {A = One} {B = C} {C = D} (const d) F

    R-identity : {d : D.Obj} → R₁ {d} D.id E.≈ E.id
    R-identity {d} = G.terminal.⊤-id ConeArr
        where
        open E
        module G = Limit (Com (G d))
        ConeArr : Cone⇒ (ConesGd {d}) G.limit G.limit
        ConeArr = record
          { arr = R₁ D.id
          ; commute = λ {Z} → begin
            G.proj Z ∘ R₁ D.id  ≈⟨ proj-red Z D.id ⟩
            G.proj (↙⇒ Z D.id) ≈⟨ proj≈ (D.Equiv.trans D.identityˡ D.identityʳ) ⟩
            G.proj Z            ∎
          }

    R-hom : {Y Z W : D.Obj} {f : D [ Y , Z ]} {g : D [ Z , W ]} → E [ R₁ (D [ g ∘ f ]) ≈ E [ R₁ g ∘ R₁ f ] ]
    R-hom {Y} {Z} {W} {f} {g} = terminal.!-unique₂ (⊤Gd W) {A = cc} {f = f⇒} {g = g⇒}
      where
      module ⊤GY = Cone (⊤Gd.limit Y)
      module H   = Functor (f↙F (g D.∘ f)) using (₀; ₁)
      open E
      cc : Cone (X ∘F Cod (const W) F)
      cc = record { N = ⊤GY.N; apex = record
        { ψ      =  λ K → ⊤GY.ψ (H.₀ K)
        ; commute = λ h → ⊤GY.commute (H.₁ h)
        } }
      f⇒ : Cone⇒ (ConesGd {W}) cc (⊤Gd.terminal.⊤ W)
      f⇒ = record
        { arr = R₁ (g D.∘ f)
        ; commute = λ {K} → proj-red K (g D.∘ f)
        }
      g⇒ : Cone⇒ (ConesGd {W}) cc (⊤Gd.terminal.⊤ W)
      g⇒ = record
        { arr = R₁ g ∘ R₁ f
        ; commute = λ {K} → begin
          ⊤Gd.proj W K ∘ R₁ g ∘ R₁ f        ≈⟨ pullˡ (proj-red K g) ⟩
          ⊤Gd.proj Z (↙⇒ K g) ∘ R₁ f       ≈⟨ proj-red (↙⇒ K g) f ⟩
          ⊤Gd.proj Y (↙⇒ (↙⇒ K g) f)     ≈⟨ proj≈ (D.Equiv.trans D.identityˡ (MR.assoc²' D)) ⟩
          ⊤Gd.proj Y (↙⇒ K (g D.∘ f))      ∎
        }

    R-resp-≈ : {Y Z : D.Obj} {f g : D [ Y , Z ]} → D [ f ≈ g ] → E [ R₁ f ≈ R₁ g ]
    R-resp-≈ {Y} {Z} {f} {g} f≈g = terminal.!-unique₂ (⊤Gd Z) {A = cc} {f = fc} {g = gc}
      where
      open E
      module ⊤GY = Cone (⊤Gd.limit Y)
      module H = Functor (f↙F f)
      cc : Cone (X ∘F Cod (const Z) F)
      cc = record { apex = record
            { ψ       = λ K → ⊤GY.ψ (H.F₀ K)
            ; commute = λ h → ⊤GY.commute (H.F₁ h)
            } }
      F-resp-≈-commute : ∀ {Y Z} {K : Category.Obj (Z ↙ F)} {f g : Y D.⇒ Z} → f D.≈ g →
                           ⊤Gd.proj Z K ∘ R₁ f ≈ ⊤Gd.proj Y (↙⇒ K g)
      F-resp-≈-commute {Y} {Z} {K} {f} {g} eq = begin
        ⊤Gd.proj Z K ∘ R₁ f   ≈⟨ proj-red K f ⟩
        ⊤Gd.proj Y (↙⇒ K f) ≈⟨ proj≈ (D.∘-resp-≈ʳ (D.∘-resp-≈ʳ eq)) ⟩
        ⊤Gd.proj Y (↙⇒ K g) ∎
      fc : Cone⇒ (ConesGd {Z}) cc (⊤Gd.terminal.⊤ Z)
      fc = record
        { arr     = R₁ f
        ; commute = λ {X} → F-resp-≈-commute {Y} {Z} {X} {f} {f} D.Equiv.refl
        }
      gc : Cone⇒ (ConesGd {Z}) cc (⊤Gd.terminal.⊤ Z)
      gc = record
        { arr = R₁ g
        ; commute = λ {X} → F-resp-≈-commute {Y} {Z} {X} {g} {f} (D.Equiv.sym f≈g)
        }

    R : Functor D E
    R = record
      { F₀           = R₀
      ; F₁           = R₁
      ; identity     = λ {d} → R-identity {d}
      ; homomorphism = λ {A B C} {f g} → R-hom {A} {B} {C} {f} {g}
      ; F-resp-≈     = λ {A B} {f g} → R-resp-≈ {A} {B} {f} {g}
      }

    ,Fc : (c : C.Obj) → CommaObj {A = One} {B = C} {C = D} (const (F.₀ c)) F
    ,Fc c = record { β = c ; f = D.id }

    ε : NaturalTransformation (R ∘F F) X
    ε = ntHelper record
      { η       = λ c → ⊤Gd.proj (F.F₀ c) record { f = D.id }
      ; commute = λ {Y Z} f → begin
        ⊤Gd.proj (F.F₀ Z) _ ∘ Functor.F₁ (R ∘F F) f ≈⟨ proj-red _ (F.F₁ f) ⟩
        ⊤Gd.proj (F.F₀ Y) _                         ≈˘⟨ K-commute {C = E} (⊤Gd.limit (F.F₀ Y)) record { h = f ; commute = D.Equiv.sym (D.Equiv.trans (D.∘-resp-≈ˡ D.identityˡ) (D.∘-resp-≈ˡ D.identityˡ)) } ⟩
        X.F₁ f ∘ ⊤Gd.proj (F.F₀ Y) _                ∎
      }
      where open E

{-
    ε : NaturalTransformation (R ∘F F) X
    ε = ntHelper record
      { η       = λ c → ⊤Gd.proj (F.₀ c) (,Fc c)
      ; commute = λ {Y Z} f → let module G = Limit (Com (G (F.₀ Y))) in begin
        ⊤Gd.proj (F.₀ Z) (,Fc Z) E.∘ Functor.F₁ (R ∘F F) f ≈⟨ proj-red (,Fc Z) (F.₁ f) ⟩
        G.proj (↙⇒ (,Fc Z) (F.₁ f))                       ≈˘⟨ K-commute {C = E} {J = Comma (const (F.₀ Y)) F} {F = ConesGd {F.₀ Y}}
                                                                         G.limit (,⇒ f) ⟩
        X.₁ f E.∘ G.proj (,Fc Y)                           ∎
      }
        where
        ,⇒ : {Y Z : C.Obj} (f : Y C.⇒ Z) → Comma⇒ (,Fc Y) (↙⇒ (,Fc Z) (F.₁ f))
        ,⇒ f = record
               { g = _
               ; h = f
               ; commute = DH.begin
                   F.₁ f D.∘ D.id                      DH.≈˘⟨ D.identityˡ DH.⟩∘⟨refl ⟩
                   ((D.id D.∘ F.₁ f) D.∘ D.id)         DH.≈˘⟨ D.identityˡ DH.⟩∘⟨refl ⟩
                    (D.id D.∘ D.id D.∘ F.₁ f) D.∘ D.id DH.∎
               }
-}
    δ-Cone : ∀ d (M : Functor D E) → NaturalTransformation (M ∘F F) X → Cone (G d)
    δ-Cone d M γ = record
      { apex = record
        { ψ       = λ K → γ.η (β K) E.∘ M.₁ (f K)
        ; commute = λ {Y Z} g → begin
          X.₁ (h g) E.∘ γ.η (β Y) E.∘ M.₁ (f Y)          ≈˘⟨ pushˡ (γ.commute (h g)) ⟩
          (γ.η (β Z) E.∘ M.₁ (F.₁ (h g))) E.∘ M.₁ (f Y)  ≈⟨  pullʳ ([ M ]-resp-∘ (D.Equiv.trans (commute g) D.identityʳ))  ⟩
          γ.η (β Z) E.∘ M.₁ (f Z)
            ∎
        }
      }
      where module M = Functor M
            module γ = NaturalTransformation γ
            open CommaObj
            open Comma⇒

    δ : (M : Functor D E) → NaturalTransformation (M ∘F F) X → NaturalTransformation M R
    δ M γ = record
      { η           = λ d → ⊤Gd.rep d (δ-Cone d M γ)
      ; commute     = λ {Y Z} f → terminal.!-unique₂ (⊤Gd Z) {cc f} {q⇒ f} {w⇒ f}
      ; sym-commute = λ {Y Z} f → terminal.!-unique₂ (⊤Gd Z) {cc f} {w⇒ f} {q⇒ f}
      }
      where module M        = Functor M
            module γ        = NaturalTransformation γ
            module δ-Cone d = Cone (δ-Cone d M γ)
            open CommaObj
            cc : {Y Z : D.Obj} → Y D.⇒ Z → Cone (X ∘F Cod (const Z) F)
            cc {_} {Z} f = record
                 { apex = record
                   { ψ       = λ W → δ-Cone.ψ Z W E.∘ M.F₁ f
                   ; commute = λ g → pullˡ (δ-Cone.commute Z g)
                   }
                 }
            q⇒ : {Y Z : D.Obj} → (f : Y D.⇒ Z) → Cone⇒ (ConesGd {Z}) (cc f) (⊤Gd.terminal.⊤ Z)
            q⇒ {Y} {Z} f = record
              { arr     = ⊤Gd.rep Z (δ-Cone Z M γ) E.∘ M.F₁ f
              ; commute = pullˡ (⇒-commute (⊤Gd.rep-cone Z (δ-Cone Z M γ)))
              }
            w⇒ : {Y Z : D.Obj} → (g : Y D.⇒ Z) → Cone⇒ (ConesGd {Z}) (cc g) (⊤Gd.terminal.⊤ Z)
            w⇒ {Y} {Z} g = record
              { arr     = R₁ g E.∘ ⊤Gd.rep Y (δ-Cone Y M γ)
              ; commute = λ {W} → begin
                ⊤Gd.proj Z W E.∘ R₁ g E.∘ ⊤Gd.rep Y (δ-Cone Y M γ)  ≈⟨ pullˡ (proj-red W g) ⟩
                ⊤Gd.proj Y (↙⇒ W g) E.∘ ⊤Gd.rep Y (δ-Cone Y M γ)  ≈⟨ ⇒-commute (⊤Gd.rep-cone Y (δ-Cone Y M γ)) ⟩
                γ.η (β W) E.∘ M.F₁ (D.id D.∘ f W D.∘ g)             ≈˘⟨ refl⟩∘⟨ [ M ]-resp-∘ ( D.Equiv.sym D.identityˡ ) ⟩
                γ.η (β W) E.∘ M.F₁ (f W) E.∘ M.F₁ g                 ≈⟨ E.sym-assoc ⟩
                (γ.η (β W) E.∘ M.F₁ (f W)) E.∘ M.F₁ g               ∎
              }

    δ-unique : ∀ {M : Functor D E} {γ : NaturalTransformation (M ∘F F) X}
                 (δ′ : NaturalTransformation M R) → γ ≊ ε ∘ᵥ δ′ ∘ʳ F → δ′ ≊ δ M γ
    δ-unique {M} {γ} δ′ eq {d} = ⟺ (⊤Gd.terminal.!-unique d C⇒)
      where
      module M = Functor M using (₁)
      module γ = NaturalTransformation γ using (η)
      module δ = NaturalTransformation δ′ using (η; commute)
      open CommaObj
      C⇒ : Cone⇒ (X ∘F Cod (const d) F) (δ-Cone d M γ) (terminal.⊤ (⊤Gd d))
      C⇒ = record
        { arr     = δ.η d
        ; commute = λ {W} → begin
          ⊤Gd.proj d W E.∘ δ.η d                                                   ≈˘⟨ proj≈ (D.Equiv.trans D.identityˡ D.identityˡ)  ⟩∘⟨refl ⟩
          ⊤Gd.proj d (↙⇒ (commaF D.id) (f W)) E.∘ δ.η d                          ≈˘⟨ pullˡ (proj-red (commaF D.id) (f W)) ⟩
          ⊤Gd.proj (F.₀ (β W)) (commaF D.id) E.∘ R₁ (f W) E.∘ δ.η d                ≈˘⟨ pullʳ (δ.commute (f W)) ⟩
          (⊤Gd.proj (F.₀ (β W)) (commaF D.id) E.∘ δ.η (F.₀ (β W))) E.∘ M.₁ (f W)   ≈˘⟨ eq ⟩∘⟨refl ⟩
          γ.η (β W) E.∘ M.₁ (f W)
            ∎
        }

    commutes : (M : Functor D E) (γ : NaturalTransformation (M ∘F F) X) → γ ≊ ε ∘ᵥ δ M γ ∘ʳ F
    commutes M γ {c} = begin
        η γ c                 ≈˘⟨ elimʳ M.identity ⟩
        η γ c E.∘ M.₁ D.id    ≈˘⟨ ⇒-commute (⊤Gd.rep-cone (F.₀ c) (δ-Cone (F.₀ c) M γ)) {,Fc c} ⟩
        η (ε ∘ᵥ δ M γ ∘ʳ F) c ∎
      where
      open NaturalTransformation
      module M  = Functor M using (₁; identity)
