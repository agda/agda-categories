{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Construction.Limit where

open import Function using (_$_)

open import Categories.Adjoint
open import Categories.Adjoint.Equivalence
open import Categories.Adjoint.Compose
open import Categories.Adjoint.Properties
open import Categories.Category
open import Categories.Category.Construction.Cones
open import Categories.Category.Complete
open import Categories.Category.Cocomplete
open import Categories.Category.Construction.Functors
open import Categories.Functor
open import Categories.Functor.Construction.Diagonal
open import Categories.Functor.Construction.Constant
open import Categories.NaturalTransformation renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_; module ≃)
open import Categories.Diagram.Cone.Properties
open import Categories.Diagram.Duality

import Categories.Diagram.Limit as Lim
import Categories.Diagram.Cone as Con
import Categories.Morphism.Reasoning as MR

module _ {o ℓ e o′ ℓ′ e′} (C : Category o ℓ e) (Com : Complete o′ ℓ′ e′ C) {J : Category o′ ℓ′ e′} where
  private
    module C = Category C
    module J = Category J
    open C
    open HomReasoning
    open Lim.Limit
    open Con.Cone⇒ renaming (commute to ⇒-commute)
    open MR C

    K⇒lim : ∀ {F G : Functor J C} (α : NaturalTransformation F G) (K : Con.Cone F) →
              Cones G [ nat-map-Cone α K , limit (Com G) ]
    K⇒lim {G = G} α K = rep-cone (Com G) (nat-map-Cone α K)

    lim⇒lim : ∀ {F G : Functor J C} (α : NaturalTransformation F G) →
                Cones G [ nat-map-Cone α (limit (Com F)) , limit (Com G) ]
    lim⇒lim {F} α = K⇒lim α (limit (Com F))

    id-Cone : ∀ X → Con.Cone {C = C} {J = J} (const X)
    id-Cone X = record
      { apex = record
        { ψ       = λ _ → C.id
        ; commute = λ _ → C.identity²
        }
      }

    X⇒limΔ : ∀ X → Cones (const {C = J} X) [ id-Cone X , limit (Com (const X)) ]
    X⇒limΔ X = rep-cone (Com (const X)) _

  LimitF : Functor (Functors J C) C
  LimitF = record
    { F₀           = λ F → apex (Com F)
    ; F₁           = λ {F G} α → arr (lim⇒lim α)
    ; identity     = λ {F} → terminal.!-unique (Com F) $ record
      { arr     = C.id
      ; commute = id-comm
      }
    ; homomorphism = λ {F G H} {α β} →
      let module α = NaturalTransformation α
          module β = NaturalTransformation β
      in terminal.!-unique₂ (Com H) {_} {terminal.! (Com H)}
      {record { commute = λ {j} → begin
        proj (Com H) j ∘ arr (lim⇒lim β) ∘ arr (lim⇒lim α) ≈⟨ pullˡ (⇒-commute (lim⇒lim β)) ⟩
        (β.η j ∘ proj (Com G) j) ∘ arr (lim⇒lim α)         ≈⟨ assoc ⟩
        β.η j ∘ proj (Com G) j ∘ arr (lim⇒lim α)           ≈⟨ pushʳ (⇒-commute (lim⇒lim α)) ⟩
        (β.η j ∘ α.η j) ∘ proj (Com F) j                   ∎ }}
    ; F-resp-≈     = λ {F G} {α β} eq → terminal.!-unique (Com G) $ record
      { commute = ⇒-commute (lim⇒lim β) ○ ∘-resp-≈ˡ (⟺ eq)
      }
    }

  Δ⊣LimitF : ΔF J ⊣ LimitF
  Δ⊣LimitF = record
    { unit   = ntHelper record
      { η       = λ X → rep (Com (const X)) (id-Cone X)
      ; commute = λ {X Y} f → terminal.!-unique₂ (Com (const Y))
        {record
          { apex = record
            { ψ       = λ _ → f
            ; commute = λ _ → C.identityˡ
            }
          }}
        {record
          { commute = cancelˡ (⇒-commute (X⇒limΔ Y))
          }}
        {record
          { commute =
            ⇒-commute (Cones (const Y) [ lim⇒lim (constNat f)
                                       ∘ nat-map-Cone⇒ (constNat f) (terminal.! (Com (const X)) {id-Cone X}) ])
            ○ identityʳ
          }}
      }
    ; counit = ntHelper record
      { η       = counit-nat
      ; commute = λ α → ⇒-commute (lim⇒lim α)
      }
    ; zig    = λ {X} → ⇒-commute (X⇒limΔ X)
    ; zag    = λ {F} →
      let apF = apex (Com F)
          align : Cones F [ limit (Com F) , nat-map-Cone (counit-nat F) (id-Cone apF) ]
          align = record
            { arr     = C.id
            ; commute = identityʳ ○ identityʳ
            }
          limF⇒limF : Cones F [ limit (Com F) , limit (Com F) ]
          limF⇒limF = Cones F [ Cones F [ lim⇒lim (counit-nat F)
                              ∘ nat-map-Cone⇒ (counit-nat F) (terminal.! (Com (const apF))) ]
                              ∘ align ]
      in terminal.!-unique₂ (Com F)
         {limit (Com F)}
         {record { commute = ∘-resp-≈ʳ (⟺ identityʳ) ○ ⇒-commute limF⇒limF }}
         {record { commute = identityʳ }}
    }
    where counit-nat : (F : Functor J C) → NaturalTransformation (const (apex (Com F))) F
          counit-nat F = ntHelper record
            { η       = proj (Com F)
            ; commute = λ f → identityʳ ○ ⟺ (limit-commute (Com F) f)
            }

module _ {o ℓ e o′ ℓ′ e′} (C : Category o ℓ e) (Coc : Cocomplete o′ ℓ′ e′ C) {J : Category o′ ℓ′ e′} where
  private
    module C = Category C
    module J = Category J
    open C
    open MR C

    Com : Complete o′ ℓ′ e′ C.op
    Com F = Colimit⇒coLimit C (Coc (Functor.op F))
    LF  : Functor (Functors J.op op) C.op
    LF    = LimitF C.op Com {J.op}

  ColimitF : Functor (Functors J C) C
  ColimitF = Functor.op LF ∘F opF⇐

  ColimitF⊣Δ : ColimitF ⊣ ΔF J
  ColimitF⊣Δ = ⊣×≃⇒⊣ helper ≃.refl ΔF≃
    where Δ⊣LimitFᵒᵖ : ΔF J.op ⊣ LF
          Δ⊣LimitFᵒᵖ = Δ⊣LimitF op Com {J.op}
          opF⊣ : opF⇐ {A = J} {C} ⊣ opF⇒
          opF⊣ = ⊣Equivalence.R⊣L (Functorsᵒᵖ-equiv J C)
          helper : ColimitF ⊣ opF⇒ ∘F Functor.op (ΔF J.op)
          helper = opF⊣ ∘⊣ Adjoint.op Δ⊣LimitFᵒᵖ
          ΔF≃ : opF⇒ ∘F Functor.op (ΔF J.op) ≃ ΔF J
          ΔF≃ = record
            { F⇒G = record
              { η           = λ _ → idN
              ; commute     = λ _ → id-comm-sym
              ; sym-commute = λ _ → id-comm
              }
            ; F⇐G = record
              { η           = λ _ → idN
              ; commute     = λ _ → id-comm-sym
              ; sym-commute = λ _ → id-comm
              }
            ; iso = λ X → record
              { isoˡ = identity²
              ; isoʳ = identity²
              }
            }
