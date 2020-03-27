{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Construction.Properties.Presheaves.Complete {o ℓ e} (C : Category o ℓ e) where

open import Data.Product
open import Function.Equality using (Π) renaming (_∘_ to _∙_)
open import Relation.Binary
open import Relation.Binary.Construct.Closure.SymmetricTransitive as ST using (Plus⇔)
open Plus⇔

open import Categories.Category.Complete
open import Categories.Category.Cocomplete
open import Categories.Category.Construction.Presheaves
open import Categories.Category.Instance.Setoids
open import Categories.Category.Instance.Properties.Setoids
open import Categories.Diagram.Limit as Lim
open import Categories.Diagram.Colimit
open import Categories.Functor
open import Categories.NaturalTransformation

import Categories.Category.Construction.Cones as Co
import Categories.Category.Construction.Cocones as Coc
import Relation.Binary.Reasoning.Setoid as SetoidR

private
  module C = Category C
  open C
  open Π using (_⟨$⟩_)

module _ o′ where
  private
    P = Presheaves′ o′ o′ C
    module P = Category P

    module _ {J : Category o′ o′ o′} (F : Functor J P) where
      module J = Category J
      module F = Functor F
      open F
      module F₀ j = Functor (F₀ j)
      module F₁ {a b} (f : a J.⇒ b) = NaturalTransformation (F₁ f)
      open Setoid using () renaming (_≈_ to [_]_≈_)

      F[-,_] : Obj → Functor J (Setoids o′ o′)
      F[-, X ] = record
        { F₀           = λ j → F₀.₀ j X
        ; F₁           = λ f → F₁.η f X
        ; identity     = identity
        ; homomorphism = homomorphism
        ; F-resp-≈     = λ eq → F-resp-≈ eq -- this application cannot be eta reduced
        }

      -- limit related definitions

      module LimFX X = Limit (Setoids-Complete _ _ _ o′ o′ F[-, X ])

      module FCone (K : Co.Cone F) where
        open Co.Cone F K public
        module N = Functor N
        module ψ j = NaturalTransformation (ψ j)

      module FCone⇒ {K K′ : Co.Cone F} (K⇒K′ : Co.Cone⇒ F K K′) where
        open Co.Cone⇒ F K⇒K′ public
        module arr = NaturalTransformation arr

      FXcone : ∀ X → (K : Co.Cone F) → Co.Cone F[-, X ]
      FXcone X K = record
        { N    = N.₀ X
        ; apex = record
          { ψ       = λ j → ψ.η j X
          ; commute = λ f → commute f -- this application cannot be eta reduced
          }
        }
        where open FCone K

      ⊤ : Co.Cone F
      ⊤ = record
        { N    = record
          { F₀           = λ X → LimFX.apex X
          ; F₁           = λ {A B} f → record
            { _⟨$⟩_ = λ { (S , eq) → (λ j → F₀.₁ j f ⟨$⟩ S j) , λ {X Y} g →
              let open SetoidR (F₀.₀ Y B)
              in begin
                F₁.η g B ⟨$⟩ (F₀.₁ X f ⟨$⟩ S X) ≈⟨ F₁.commute g f (Setoid.refl (F₀.₀ X A)) ⟩
                F₀.₁ Y f ⟨$⟩ (F₁.η g A ⟨$⟩ S X) ≈⟨ Π.cong (F₀.₁ Y f) (eq g) ⟩
                F₀.₁ Y f ⟨$⟩ S Y ∎ }
            ; cong  = λ eq j → Π.cong (F₀.₁ j f) (eq j)
            }
          ; identity     = λ eq j → F₀.identity j (eq j)
          ; homomorphism = λ eq j → F₀.homomorphism j (eq j)
          ; F-resp-≈     = λ eq eq′ j → F₀.F-resp-≈ j eq (eq′ j)
          }
        ; apex = record
          { ψ       = λ j → ntHelper record
            { η       = λ X → record
              { _⟨$⟩_ = λ { (S , eq) → S j }
              ; cong  = λ eq → eq j
              }
            ; commute = λ f eq → Π.cong (F₀.₁ j f) (eq j)
            }
          ; commute = λ { {Y} {Z} f {W} {S₁ , eq₁} {S₂ , eq₂} eq →
            let open SetoidR (F₀.₀ Z W)
            in begin
              F₁.η f W ⟨$⟩ S₁ Y ≈⟨ eq₁ f ⟩
              S₁ Z              ≈⟨ eq Z ⟩
              S₂ Z              ∎ }
          }
        }

      K⇒⊤′ : ∀ X {K} → Co.Cones F [ K , ⊤ ] → Co.Cones F[-, X ] [ FXcone X K , LimFX.limit X ]
      K⇒⊤′ X {K} K⇒⊤ = record
        { arr     = arr.η X
        ; commute = comm
        }
        where open FCone⇒ K⇒⊤ renaming (commute to comm)

      complete : Limit F
      complete = record
        { terminal = record
          { ⊤        = ⊤
          ; !        = λ {K} →
            let module K = FCone K
            in record
            { arr     = ntHelper record
              { η       = λ X → LimFX.rep X (FXcone X K)
              ; commute = λ {X Y} f eq j → K.ψ.commute j f eq
              }
            ; commute = λ eq → Π.cong (K.ψ.η _ _) eq
            }
          ; !-unique = λ K⇒⊤ {X} → LimFX.terminal.!-unique X (K⇒⊤′ X K⇒⊤)
          }
        }      


      -- colimit related definitions

      module ColimFX X = Colimit (Setoids-Cocomplete _ _ _ o′ o′ F[-, X ])

      module FCocone (K : Coc.Cocone F) where
        open Coc.Cocone F K public
        module N = Functor N
        module ψ j = NaturalTransformation (ψ j)

      module FCocone⇒ {K K′ : Coc.Cocone F} (K⇒K′ : Coc.Cocone⇒ F K K′) where
        open Coc.Cocone⇒ F K⇒K′ public
        module arr = NaturalTransformation arr

      FXcocone : ∀ X → (K : Coc.Cocone F) → Coc.Cocone F[-, X ]
      FXcocone X K = record
        { N      = N.₀ X
        ; coapex = record
          { ψ       = λ j → ψ.η j X
          ; commute = λ f → commute f -- this application cannot be eta reduced
          }
        }
        where open FCocone K

      ⊥ : Coc.Cocone F
      ⊥ = record
        { N      = record
          { F₀           = λ X → ColimFX.coapex X
          ; F₁           = λ {A B} f → record
            { _⟨$⟩_ = λ { (j , Sj) → j , F₀.₁ j f ⟨$⟩ Sj  }
            ; cong  = λ { {a , Sa} {b , Sb} →
              ST.map (λ { (j , Sj) → j , F₀.₁ j f ⟨$⟩ Sj }) (helper f) }
            }
          ; identity     = λ { {A} {j , _} eq → forth⁺ (J.id , identity (F₀.identity j (Setoid.refl (F₀.₀ j A)))) eq }
          ; homomorphism = λ {X Y Z} {f g} → λ { {_} {j , Sj} eq →
            let open Setoid (F₀.₀ j Z)
            in ST.trans (coc o′ o′ F[-, Z ])
                        (ST.map (hom-map f g) (helper (f ∘ g)) eq)
                        (forth (J.id , trans (identity refl) (F₀.homomorphism j (Setoid.refl (F₀.₀ j X))))) }
          ; F-resp-≈     = λ {A B} {f g} eq → λ { {j , Sj} eq′ →
            let open Setoid (F₀.₀ j B)
            in ST.trans (coc o′ o′ F[-, B ])
                        (forth (J.id , trans (identity refl) (F₀.F-resp-≈ j eq (Setoid.refl (F₀.₀ j A)))))
                        (ST.map (λ { (j , Sj) → (j , F₀.₁ j g ⟨$⟩ Sj) }) (helper g) eq′) }
          }
        ; coapex = record
          { ψ       = λ j → ntHelper record
            { η       = λ X → record
              { _⟨$⟩_ = j ,_
              ; cong  = λ eq → forth (-, identity eq)
              }
            ; commute = λ {X Y} f eq → back (-, identity (Π.cong (F₀.₁ j f) (Setoid.sym (F₀.₀ j X) eq)))
            }
          ; commute = λ {a b} f {X} {x y} eq →
            let open ST.Plus⇔Reasoning (coc o′ o′ F[-, X ])
            in back (f , Π.cong (F₁.η f X) (Setoid.sym (F₀.₀ a X) eq))
          }
        }
        where helper : ∀ {A B} (f : B C.⇒ A) {a Sa b Sb} →
                         Σ (a J.⇒ b) (λ g → [ F₀.₀ b A ] F₁.η g A ⟨$⟩ Sa ≈ Sb) →
                         Σ (a J.⇒ b) λ h → [ F₀.₀ b B ] F₁.η h B ⟨$⟩ (F₀.₁ a f ⟨$⟩ Sa) ≈ F₀.₁ b f ⟨$⟩ Sb
              helper {A} {B} f {a} {Sa} {b} {Sb} (g , eq′) =
                let open SetoidR (F₀.₀ b B)
                in g , (begin
                  F₁.η g B ⟨$⟩ (F₀.₁ a f ⟨$⟩ Sa) ≈⟨ F₁.commute g f (Setoid.refl (F₀.₀ a A)) ⟩
                  F₀.₁ b f ⟨$⟩ (F₁.η g A ⟨$⟩ Sa) ≈⟨ Π.cong (F₀.₁ b f) eq′ ⟩
                  F₀.₁ b f ⟨$⟩ Sb ∎)

              hom-map : ∀ {X Y Z} → Y C.⇒ X → Z C.⇒ Y → Σ J.Obj (λ j → Setoid.Carrier (F₀.₀ j X)) → Σ J.Obj (λ j → Setoid.Carrier (F₀.₀ j Z))
              hom-map f g (j , Sj) = j , F₀.₁ j (f ∘ g) ⟨$⟩ Sj

      ⊥⇒K′ : ∀ X {K} → Coc.Cocones F [ ⊥ , K ] → Coc.Cocones F[-, X ] [ ColimFX.colimit X , FXcocone X K ]
      ⊥⇒K′ X {K} ⊥⇒K = record
        { arr     = arr.η X
        ; commute = comm
        }
        where open FCocone⇒ ⊥⇒K renaming (commute to comm)

      ! : {K : Coc.Cocone F} → Coc.Cocone⇒ F ⊥ K
      ! {K} = record
        { arr     = ntHelper record
          { η       = λ X → ColimFX.rep X (FXcocone X K)
          ; commute = λ {X Y} f → λ { {a , Sa} {b , Sb} eq →
            let open SetoidR (K.N.F₀ Y)
            in begin
              K.ψ.η a Y ⟨$⟩ (F₀.₁ a f ⟨$⟩ Sa) ≈⟨ K.ψ.commute a f (Setoid.refl (F₀.₀ a X)) ⟩
              K.N.F₁ f ⟨$⟩ (K.ψ.η a X ⟨$⟩ Sa) ≈⟨ Π.cong (K.N.F₁ f) (ST.minimal (coc o′ o′ F[-, X ]) (K.N.₀ X) (Kψ X) (helper X) eq) ⟩
              K.N.F₁ f ⟨$⟩ (K.ψ.η b X ⟨$⟩ Sb) ∎ }
          }
        ; commute = λ eq → Π.cong (K.ψ.η _ _) eq
        }
        where module K = FCocone K
              Kψ : ∀ X → Σ J.Obj (λ j → Setoid.Carrier (F₀.₀ j X)) → Setoid.Carrier (K.N.F₀ X)
              Kψ X (j , S) = K.ψ.η j X ⟨$⟩ S
              helper : ∀ X → coc o′ o′ F[-, X ] =[ Kψ X ]⇒ [ K.N.₀ X ]_≈_
              helper X {a , Sa} {b , Sb} (f , eq) = begin
                K.ψ.η a X ⟨$⟩ Sa                ≈˘⟨ K.commute f (Setoid.refl (F₀.₀ a X)) ⟩
                K.ψ.η b X ⟨$⟩ (F₁.η f X ⟨$⟩ Sa) ≈⟨ Π.cong (K.ψ.η b X) eq ⟩
                K.ψ.η b X ⟨$⟩ Sb                ∎
                where open SetoidR (K.N.₀ X)

      cocomplete : Colimit F
      cocomplete = record
        { initial = record
          { ⊥        = ⊥
          ; !        = !
          ; !-unique = λ ⊥⇒K {X} → ColimFX.initial.!-unique X (⊥⇒K′ X ⊥⇒K)
          }
        }

  Presheaves-Complete : Complete o′ o′ o′ P
  Presheaves-Complete F = complete F

  Presheaves-Cocomplete : Cocomplete o′ o′ o′ P
  Presheaves-Cocomplete F = cocomplete F
