{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Functor

module Categories.Diagram.Limit.Properties
       {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {J : Category o′ ℓ′ e′}  where

open import Function.Equality using (Π)
open import Relation.Binary using (Setoid)

open import Categories.Category.Instance.Setoids
open import Categories.Diagram.Cone.Properties
open import Categories.Functor.Hom
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; _≃_; module ≃)
open import Categories.Morphism.Reasoning C
open import Categories.Morphism C

import Categories.Category.Construction.Cones as Con
import Categories.Diagram.Limit as Lim


open Π
open Hom C

private
  module J = Category J
  module C = Category C

  open C
  variable
    X Y Z : Obj
    f g h : X ⇒ Y

open HomReasoning

-- Hom functor preserves limits in C
module _ (W : Obj) {F : Functor J C} (lim : Lim.Limit F) where
  private
    module F  = Functor F
    module LF = Lim F
    module CF = Con F
    module lim = LF.Limit lim
    open lim
    HomF : Functor J (Setoids ℓ e)
    HomF = Hom[ W ,-] ∘F F
    
    module LHomF = Lim HomF
    module CHomF = Con HomF

  hom-resp-limit : LHomF.Limit
  hom-resp-limit = record
    { terminal = record
      { ⊤        = ⊤
      ; !        = !
      ; !-unique = !-unique
      }
    }
    where ⊤ : CHomF.Cone
          ⊤ = record
            { N    = hom-setoid {W} {apex}
            ; apex = record
              { ψ       = λ X → record
                { _⟨$⟩_ = λ f → proj X ∘ f
                ; cong  = ∘-resp-≈ʳ
                }
              ; commute = λ {X Y} f {h i} eq → begin
                F.F₁ f ∘ (proj X ∘ h) ∘ C.id ≈⟨ center⁻¹ (limit-commute f) identityʳ ⟩
                proj Y ∘ h                   ≈⟨ refl⟩∘⟨ eq ⟩
                proj Y ∘ i                   ∎
              }
            }

          KW : (K : CHomF.Cone) → Setoid.Carrier (CHomF.Cone.N K) → CF.Cone
          KW K x = record
            { N    = W
            ; apex = record
              { ψ       = λ X → K.ψ X ⟨$⟩ x
              ; commute = λ f → sym (∘-resp-≈ʳ identityʳ) ○ K.commute f (Setoid.refl K.N)
              }
            }
            where module K = CHomF.Cone K

          ! : ∀ {K : CHomF.Cone} → CHomF.Cones [ K , ⊤ ]
          ! {K} = record
            { arr     = record
              { _⟨$⟩_ = λ x → rep (KW K x)
              ; cong  = λ {x y} eq → LF.ψ-≈⇒rep-≈ W (CF.Cone.apex (KW K x)) (CF.Cone.apex (KW K y)) lim
                                                  (λ A → cong (K.ψ A) eq)
              }
            ; commute = λ {X} {x y} eq → begin
              proj X ∘ rep (KW K x) ≈⟨ lim.commute ⟩
              K.ψ X ⟨$⟩ x           ≈⟨ cong (K.ψ X) eq ⟩
              K.ψ X ⟨$⟩ y           ∎
            }
            where module K = CHomF.Cone K

          !-unique : ∀ {K : CHomF.Cone} (f : CHomF.Cones [ K , ⊤ ]) → CHomF.Cones [ ! ≈ f ]
          !-unique {K} f {x} {y} x≈y = begin
            rep (KW K x) ≈⟨ terminal.!-unique f′ ⟩
            f.arr ⟨$⟩ x  ≈⟨ cong f.arr x≈y ⟩
            f.arr ⟨$⟩ y  ∎
            where module K = CHomF.Cone K
                  module f = CHomF.Cone⇒ f

                  f′ : CF.Cones [ KW K x , limit ]
                  f′ = record
                    { arr     = f.arr ⟨$⟩ x
                    ; commute = f.commute (Setoid.refl K.N)
                    }

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
      ; !        = λ {A} → record
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
