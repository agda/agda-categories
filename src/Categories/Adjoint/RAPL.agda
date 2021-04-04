{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Functor
open import Categories.Adjoint

-- Right Adjoint Preserves Limits.
module Categories.Adjoint.RAPL {o o′ ℓ ℓ′ e e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′}
  {L : Functor C D} {R : Functor D C} (L⊣R : L ⊣ R) where

open import Categories.Functor.Properties

import Categories.Morphism.Reasoning as MR
import Categories.Diagram.Limit as Lim
import Categories.Category.Construction.Cones as Con

private
  module C = Category C
  module D = Category D
  module L = Functor L
  module R = Functor R

open Adjoint L⊣R

module _ {o″ ℓ″ e″} {J : Category o″ ℓ″ e″} (F : Functor J D) where
  private
    module F = Functor F
    module LF = Lim F
    module CF = Con F

    RF = R ∘F F

    module LRF = Lim RF
    module CRF = Con RF

  rapl : LF.Limit → LRF.Limit
  rapl lim = record
    { terminal = record
      { ⊤             = ⊤
      ; ⊤-is-terminal = record
        { !        = !
        ; !-unique = !-unique
        }
      }
    }
    where module lim = LF.Limit lim
          open lim
          
          ⊤ : CRF.Cone
          ⊤ = record
            { N    = R.F₀ apex
            ; apex = record
              { ψ       = λ X → R.F₁ (proj X)
              ; commute = λ f → [ R ]-resp-∘ (limit-commute f)
              }
            }
            
          K′ : CRF.Cone → CF.Cone
          K′ K = record
            { N    = L.F₀ K.N
            ; apex = record
              { ψ       = λ X → counit.η (F.F₀ X) D.∘ L.F₁ (K.ψ X)
              ; commute = λ {X Y} f → begin
                F.F₁ f D.∘ counit.η (F.F₀ X) D.∘ L.F₁ (K.ψ X)
                  ≈˘⟨ pushˡ (counit.commute (F.F₁ f)) ⟩
                (counit.η (F.F₀ Y) D.∘ L.F₁ (R.F₁ (F.F₁ f))) D.∘ L.F₁ (K.ψ X)
                  ≈⟨ pullʳ ([ L ]-resp-∘ (K.commute f)) ⟩
                counit.η (F.F₀ Y) D.∘ L.F₁ (K.ψ Y)
                  ∎
              }
            }
            where module K = CRF.Cone K
                  open D.HomReasoning
                  open MR D
                  
          module K′ K = CF.Cone (K′ K)
          
          ! : ∀ {K : CRF.Cone} → CRF.Cones [ K , ⊤ ]
          ! {K} = record
            { arr     = R.F₁ (rep (K′ K)) C.∘ unit.η K.N
            ; commute = commute′
            }
            where module K = CRF.Cone K
                  commute′ : ∀ {X} → R.F₁ (proj X) C.∘ R.F₁ (rep (K′ K)) C.∘ unit.η K.N C.≈ K.ψ X
                  commute′ {X} = begin
                    R.F₁ (proj X) C.∘ R.F₁ (rep (K′ K)) C.∘ unit.η K.N
                      ≈⟨ pullˡ ([ R ]-resp-∘ commute) ⟩
                    R.F₁ (K′.ψ K X) C.∘ unit.η K.N
                      ≈⟨ LRadjunct≈id ⟩
                    K.ψ X
                      ∎
                    where open C.HomReasoning
                          open MR C

          module ! {K} = CRF.Cone⇒ (! {K})
          
          !-unique : ∀ {K : CRF.Cone} (f : CRF.Cones [ K , ⊤ ]) → CRF.Cones [ ! ≈ f ]
          !-unique {K} f =
            let open C.HomReasoning
                open MR C
             in begin
               R.F₁ (rep (K′ K)) C.∘ unit.η K.N ≈⟨ R.F-resp-≈ (terminal.!-unique f′) ⟩∘⟨refl ⟩
               Ladjunct (Radjunct f.arr)        ≈⟨ LRadjunct≈id ⟩
               f.arr                            ∎
            where module K = CRF.Cone K
                  module f = CRF.Cone⇒ f
                  
                  f′ : CF.Cones [ K′ K , limit ]
                  f′ = record
                    { arr     = Radjunct f.arr
                    ; commute = λ {X} → begin
                      proj X D.∘ Radjunct f.arr                                   ≈˘⟨ pushˡ (counit.commute (proj X)) ⟩
                      (counit.η (F.F₀ X) D.∘ L.F₁ (R.F₁ (proj X))) D.∘ L.F₁ f.arr ≈˘⟨ pushʳ L.homomorphism ⟩
                      Radjunct (R.F₁ (proj X) C.∘ f.arr)                          ≈⟨ Radjunct-resp-≈ f.commute ⟩
                      Radjunct (K.ψ X)                                            ∎
                    }
                    where open D.HomReasoning
                          open MR D
