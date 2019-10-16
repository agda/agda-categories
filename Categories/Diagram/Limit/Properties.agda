{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Functor

module Categories.Diagram.Limit.Properties
       {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} (F : Functor J C) where

open import Function.Equality using (Π)
open import Relation.Binary using (Setoid)

open import Categories.Category.Instance.Setoids
open import Categories.Functor.Hom
import Categories.Category.Construction.Cones as Con
import Categories.Diagram.Limit as Lim
open import Categories.Morphism.Reasoning C as MR

open Π
open Hom C

private
  module J  = Category J
  module C  = Category C
  module F  = Functor F
  module LF = Lim F
  module CF = Con F

  open C
  variable
    X Y Z : Obj
    f g h : X ⇒ Y

open HomReasoning

-- Hom functor preserves limits in C
module _ (W : Obj) (lim : LF.Limit) where
  private
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
