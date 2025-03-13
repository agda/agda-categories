{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Diagram.Limit.Properties
       {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {J : Category o′ ℓ′ e′}  where

open import Categories.Category.Construction.Arrow J using (Morphism; mor)
open import Categories.Diagram.Cone using (Cone; Cone⇒)
open import Categories.Diagram.Cone.Properties using (nat-map-Cone)
open import Categories.Diagram.Equalizer C using (Equalizer)
open import Categories.Functor using (Functor)
open import Categories.Morphism C using (_≅_)
open import Categories.Morphism.Reasoning C using (pullˡ; pullʳ; pushˡ; pushʳ; cancelˡ; switch-tofromˡ; switch-fromtoˡ)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; _≃_; module ≃)
open import Categories.Object.Product.Indexed C using (IndexedProductOf)

open import Function.Base using (_$_)

import Categories.Category.Construction.Cones as Con
import Categories.Diagram.Limit as Lim

private
  module J = Category J
  module C = Category C

  open C
  variable
    X Y Z : Obj
    f g h : X ⇒ Y

open HomReasoning

-- natural isomorphisms respects limits
module _ {F G : Functor J C} (F≃G : F ≃ G) where
  private
    module F  = Functor F
    module G  = Functor G
    module LF = Lim F
    module LG = Lim G
    open NaturalIsomorphism F≃G

  ≃-resp-lim : LF.Limit → LG.Limit
  ≃-resp-lim L = record
    { terminal = record
      { ⊤        = record
        { apex = record
          { ψ       = λ j → ⇒.η j ∘ proj j
          ; commute = λ {X Y} f → begin
            G.F₁ f ∘ ⇒.η X ∘ proj X   ≈⟨ pullˡ (⇒.sym-commute f) ⟩
            (⇒.η Y ∘ F.F₁ f) ∘ proj X ≈⟨ pullʳ (limit-commute f) ⟩
            ⇒.η Y ∘ proj Y            ∎
          }
        }
      ; ⊤-is-terminal = record
        { !        = λ {A} → record
          { arr     = rep (nat-map-Cone F⇐G A)
          ; commute = λ {j} → assoc ○ ⟺ (switch-tofromˡ (record { iso = iso j }) (⟺ commute))
          }
        ; !-unique = λ {K} f →
          let module f = Con.Cone⇒ G f
          in terminal.!-unique record
            { arr     = f.arr
            ; commute = λ {j} → switch-fromtoˡ (record { iso = iso j }) (sym-assoc ○ f.commute)
            }
        }
      }
    }
    where open LF.Limit L

  ≃⇒Cone⇒ : ∀ (Lf : LF.Limit) (Lg : LG.Limit) → Con.Cones G [ LG.Limit.limit (≃-resp-lim Lf) , LG.Limit.limit Lg ]
  ≃⇒Cone⇒ Lf Lg = rep-cone (LG.Limit.limit (≃-resp-lim Lf))
    where open LG.Limit Lg

≃⇒lim≅ : ∀ {F G : Functor J C} (F≃G : F ≃ G) (Lf : Lim.Limit F) (Lg : Lim.Limit G) → Lim.Limit.apex Lf ≅ Lim.Limit.apex Lg
≃⇒lim≅ {F = F} {G} F≃G Lf Lg = record
  { from = arr (≃⇒Cone⇒ F≃G Lf Lg)
  ; to   = arr (≃⇒Cone⇒ (≃.sym F≃G) Lg Lf)
  ; iso  = record
    { isoˡ = Lf.terminal.⊤-id record
      { commute = λ {j} → begin
        Lf.proj j ∘ arr (≃⇒Cone⇒ (≃.sym F≃G) Lg Lf) ∘ arr (≃⇒Cone⇒ F≃G Lf Lg) ≈⟨ pullˡ (⇒-commute (≃⇒Cone⇒ (≃.sym F≃G) Lg Lf)) ⟩
        (⇐.η j ∘ Lg.proj j) ∘ arr (≃⇒Cone⇒ F≃G Lf Lg)                         ≈⟨ pullʳ (⇒-commute (≃⇒Cone⇒ F≃G Lf Lg)) ⟩
        ⇐.η j ∘ ⇒.η j ∘ Lf.proj j                                             ≈⟨ cancelˡ (iso.isoˡ j) ⟩
        Lf.proj j                                                             ∎
      }
    ; isoʳ = Lg.terminal.⊤-id record
      { commute = λ {j} → begin
        Lg.proj j ∘ arr (≃⇒Cone⇒ F≃G Lf Lg) ∘ arr (≃⇒Cone⇒ (≃.sym F≃G) Lg Lf) ≈⟨ pullˡ (⇒-commute (≃⇒Cone⇒ F≃G Lf Lg)) ⟩
        (⇒.η j ∘ Lf.proj j) ∘ arr (≃⇒Cone⇒ (≃.sym F≃G) Lg Lf)                 ≈⟨ pullʳ (⇒-commute (≃⇒Cone⇒ (≃.sym F≃G) Lg Lf)) ⟩
        ⇒.η j ∘ ⇐.η j ∘ Lg.proj j                                             ≈⟨ cancelˡ (iso.isoʳ j) ⟩
        Lg.proj j                                                             ∎
      }
    }
  }
  where open Con.Cone⇒ renaming (commute to ⇒-commute)
        module Lf = Lim.Limit Lf
        module Lg = Lim.Limit Lg
        open NaturalIsomorphism F≃G

-- existence theorem
module _ {F : Functor J C} {OP : IndexedProductOf (Functor.₀ F)} {MP : IndexedProductOf λ f → Functor.₀ F (Morphism.cod f)} where

  private
    module F = Functor F
    module OP = IndexedProductOf OP
    module MP = IndexedProductOf MP

    s t : OP.X ⇒ MP.X
    s = MP.⟨ (λ f → F.₁ (Morphism.arr f) ∘ OP.π (Morphism.dom f)) ⟩
    t = MP.⟨ (λ f → OP.π (Morphism.cod f)) ⟩

  build-lim : Equalizer s t → Lim.Limit F
  build-lim eq = record
    { terminal = record
      { ⊤ = record
        { N = obj
        ; apex = record
          { ψ = λ X → OP.π X ∘ arr
          ; commute = λ {X} {Y} f → begin
            F.₁ f ∘ (OP.π X ∘ arr)   ≈⟨ pushˡ MP.commute ⟨
            (MP.π (mor f) ∘ s) ∘ arr ≈⟨ pullʳ equality ⟩
            MP.π (mor f) ∘ (t ∘ arr) ≈⟨ pullˡ MP.commute ⟩
            OP.π Y ∘ arr             ∎
          }
        }
      ; ⊤-is-terminal = record
        { ! = λ {A} → record
          { arr = equalize (bang-lemma A)
          ; commute = ⟺ (pushʳ universal) ○ OP.commute
          }
        ; !-unique = λ f → Equiv.sym (unique (OP.unique (sym-assoc ○ Cone⇒.commute f)))
        }
      }
    }
    where
      open Equalizer eq
      abstract
        bang-lemma : (A : Cone F) → s ∘ OP.⟨ Cone.ψ A ⟩ ≈ t ∘ OP.⟨ Cone.ψ A ⟩
        bang-lemma A = begin
          s ∘ OP.⟨ Cone.ψ A ⟩                                                             ≈⟨ MP.⟨⟩∘ (λ f → F.₁ (Morphism.arr f) ∘ OP.π (Morphism.dom f)) OP.⟨ Cone.ψ A ⟩ ⟩
          MP.⟨ (λ f → (F.₁ (Morphism.arr f) ∘ OP.π (Morphism.dom f)) ∘ OP.⟨ Cone.ψ A ⟩) ⟩ ≈⟨ MP.⟨⟩-cong (pullʳ OP.commute) ⟩
          MP.⟨ (λ f → F.₁ (Morphism.arr f) ∘ Cone.ψ A (Morphism.dom f)) ⟩                 ≈⟨ MP.⟨⟩-cong (Cone.commute A _) ⟩
          MP.⟨ (λ f → Cone.ψ A (Morphism.cod f)) ⟩                                        ≈⟨ MP.⟨⟩-cong OP.commute ⟨
          MP.⟨ (λ f → OP.π (Morphism.cod f) ∘ OP.⟨ Cone.ψ A ⟩) ⟩                          ≈⟨ MP.⟨⟩∘ (λ f → OP.π (Morphism.cod f)) OP.⟨ Cone.ψ A ⟩ ⟨
          t ∘ OP.⟨ Cone.ψ A ⟩                                                             ∎
