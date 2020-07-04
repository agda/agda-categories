{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Complete.Properties {o ℓ e} (C : Category o ℓ e) where

open import Level
open import Data.Product
open import Relation.Binary

open import Categories.Category.Complete
open import Categories.Category.Complete.IndexedProduct C
open import Categories.Category.Complete.Finitely
open import Categories.Category.Construction.Functors
open import Categories.Diagram.Equalizer C
open import Categories.Diagram.Limit as Lim
open import Categories.Diagram.Limit.Properties
open import Categories.Diagram.Equalizer.Limit C
open import Categories.Diagram.Cone.Properties
open import Categories.Object.Product.Limit C
open import Categories.Object.Terminal.Limit C
open import Categories.Functor
open import Categories.Functor.Continuous
open import Categories.Functor.Properties
open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_)

import Categories.Category.Construction.Cones as Co
import Categories.Morphism.Reasoning as MR
import Categories.Morphism as Mor
import Categories.Morphism.Properties as Morₚ

private
  variable
    o′ ℓ′ e′ o″ ℓ″ e″ : Level
  module C = Category C

module _ (Com : Complete o′ ℓ′ e′ C) where

  Complete⇒FinitelyComplete : FinitelyComplete C
  Complete⇒FinitelyComplete = record
    { cartesian = record
      { terminal = limit⇒⊥ (Com (⊥⇒limit-F _ _ _))
      ; products = record
        { product = λ {A B} → limit⇒product (Com (product⇒limit-F _ _ _ A B))
        }
      }
    ; equalizer = λ f g → limit⇒equalizer (Com (equalizer⇒limit-F _ _ _ f g))
    }

-- if the base category is complete, then the functor category is complete.
-- in addition, the evaluation functor is continuous.
--
--     Functors-Complete : Complete o″ ℓ″ e″ D^C
--     evalF-Continuous : ∀ X → Continuous o″ ℓ″ e″ (evalF C D X)

module _ {D : Category o′ ℓ′ e′} (Com : Complete o″ ℓ″ e″ D) where
  private
    D^C = Functors C D
    module D^C = Category D^C
    module D   = Category D    

    module _ {J : Category o″ ℓ″ e″} (F : Functor J D^C) where
      private
        module J = Category J
        module F = Functor F
        open F
        module F₀ j = Functor (F₀ j)
        module F₁ {a b} (f : a J.⇒ b) = NaturalTransformation (F₁ f)

      F[-,_] : C.Obj → Functor J D
      F[-, X ] = record
        { F₀           = λ j → F₀.₀ j X
        ; F₁           = λ f → F₁.η f X
        ; identity     = identity
        ; homomorphism = homomorphism
        ; F-resp-≈     = λ eq → F-resp-≈ eq -- this application cannot be eta reduced
        }

      F[-,-] : Functor C (Functors J D)
      F[-,-] = record
        { F₀           = F[-,_]
        ; F₁           = λ f → ntHelper record
          { η       = λ j → F₀.₁ j f
          ; commute = λ g → F₁.sym-commute g f
          }
        ; identity     = F₀.identity _
        ; homomorphism = F₀.homomorphism _
        ; F-resp-≈     = λ eq → F₀.F-resp-≈ _ eq
        }

      module F[-,-] = Functor F[-,-]

      module LimFX X = Limit (Com F[-, X ])
      open LimFX hiding (commute)

      K⇒lim : ∀ {X Y} (f : X C.⇒ Y) K → Co.Cones F[-, Y ] [ nat-map-Cone (F[-,-].₁ f) K , limit Y ]
      K⇒lim f K = rep-cone _ (nat-map-Cone (F[-,-].₁ f) K)

      lim⇒lim : ∀ {X Y} (f : X C.⇒ Y) → Co.Cones F[-, Y ] [ nat-map-Cone (F[-,-].₁ f) (limit X) , limit Y ]
      lim⇒lim f = K⇒lim f (limit _)

      module lim⇒lim {X Y} (f : X C.⇒ Y) = Co.Cone⇒ F[-, Y ] (lim⇒lim f)

      module FCone (K : Co.Cone F) where
        open Co.Cone F K public
        module N   = Functor N
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
          { F₀           = λ X → apex X
          ; F₁           = λ {A B} f → lim⇒lim.arr f
          ; identity     = λ {X} →
            terminal.!-unique X record
            { arr     = D.id
            ; commute = D.identityʳ ○ ⟺ (elimˡ (F₀.identity _))
            }
          ; homomorphism = λ {X Y Z} {f g} →
            terminal.!-unique₂ Z
              {nat-map-Cone (F[-,-].₁ (g C.∘ f)) (limit X)}
              {terminal.! Z}
              {record { commute = λ {j} →
              begin
                proj Z j ∘ lim⇒lim.arr g ∘ lim⇒lim.arr f
                  ≈⟨ pullˡ (lim⇒lim.commute g) ⟩
                (F₀.₁ j g ∘ proj Y j) ∘ lim⇒lim.arr f
                  ≈⟨ pullʳ (lim⇒lim.commute f) ⟩
                F₀.₁ j g ∘ F₀.₁ j f ∘ proj X j
                  ≈˘⟨ pushˡ (F₀.homomorphism j) ⟩
                F₀.₁ j (g C.∘ f) ∘ proj X j
                  ∎ }}
          ; F-resp-≈     = λ {A B} {f g} eq → terminal.!-unique B record
            { commute = lim⇒lim.commute g ○ ∘-resp-≈ˡ (F₀.F-resp-≈ _ (C.Equiv.sym eq)) }
          }
        ; apex = record
          { ψ       = λ j → ntHelper record
            { η       = λ X → proj X j
            ; commute = λ _ → LimFX.commute _
            }
          ; commute = λ f {X} → limit-commute X f
          }
        }
        where open D
              open D.HomReasoning
              open MR D

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
              { η       = λ X → rep X (FXcone X K)
              ; commute = λ {X Y} f →
                terminal.!-unique₂ Y
                  {nat-map-Cone (F[-,-].₁ f) (FXcone X K)}
                  {record { commute = λ {j} →
                  begin
                    proj Y j ∘ rep Y (FXcone Y K) ∘ K.N.₁ f ≈⟨ pullˡ (LimFX.commute Y) ⟩
                    K.ψ.η j Y ∘ K.N.F₁ f                    ≈⟨ K.ψ.commute j f ⟩
                    F₀.₁ j f ∘ K.ψ.η j X                    ∎ }}
                  {record { commute = λ {j} →
                  begin
                    proj Y j ∘ lim⇒lim.arr f ∘ rep X (FXcone X K) ≈⟨ pullˡ (lim⇒lim.commute f) ⟩
                    (F₀.₁ j f ∘ proj X j) ∘ rep X (FXcone X K)    ≈⟨ pullʳ (LimFX.commute X) ⟩
                    F₀.₁ j f ∘ K.ψ.η j X                          ∎ }}
              }
            ; commute = λ {_} {X} → LimFX.commute X
            }
          ; !-unique = λ K⇒⊤ {X} → terminal.!-unique X (K⇒⊤′ X K⇒⊤)
          }
        }      
        where open D
              open D.HomReasoning
              open MR D

      ev : C.Obj → Functor D^C D
      ev = evalF C D

      module _ (L : Limit F) (X : C.Obj) where
        private
          module ev = Functor (ev X)
          open Mor D^C
          module DM = Mor D
          open Morₚ D
          open D.HomReasoning
          open MR D

        L′ : Limit (ev X ∘F F)
        L′ = Com (ev X ∘F F)

        Fiso : F[-, X ] ≃ ev X ∘F F
        Fiso = record
          { F⇒G = ntHelper record
            { η       = λ _ → D.id
            ; commute = λ _ → id-comm-sym ○ D.∘-resp-≈ˡ (introʳ (F₀.identity _))
            }
          ; F⇐G = ntHelper record
            { η       = λ _ → D.id
            ; commute = λ _ → D.∘-resp-≈ʳ (elimʳ (F₀.identity _)) ○ id-comm-sym
            }
          ; iso = λ _ → record
            { isoˡ = D.identity²
            ; isoʳ = D.identity²
            }
          }

        apex-iso : Limit.apex L ≅ Limit.apex complete
        apex-iso = up-to-iso F L complete

        apex-iso′ : Limit.apex (Com F[-, X ]) DM.≅ Limit.apex L′
        apex-iso′ = ≃⇒lim≅ Fiso (Com F[-, X ]) L′

        project-iso : Functor.F₀ (Limit.apex L) X DM.≅ Limit.apex L′
        project-iso = record
          { from = ai.from D.∘ from.η X
          ; to   = to.η X D.∘ ai.to
          ; iso  = Iso-∘ (record { isoˡ = isoˡ ; isoʳ = isoʳ }) ai.iso
          }
          where open _≅_ apex-iso
                module from = NaturalTransformation from
                module to   = NaturalTransformation to
                module ai   = DM._≅_ apex-iso′

  Functors-Complete : Complete o″ ℓ″ e″ D^C
  Functors-Complete = complete

  evalF-Continuous : ∀ X → Continuous o″ ℓ″ e″ (evalF C D X)
  evalF-Continuous X {J} {F} L = Com (evalF C D X ∘F F) , project-iso F L X

module _ (prods : AllProductsOf (o′ ⊔ ℓ′)) (equalizer : ∀ {A B} (f g : A C.⇒ B) → Equalizer f g) where
  private
    module Prods {I} (P : I → C.Obj) = IndexedProductOf (prods P)
    open C.HomReasoning

    module _ {J : Category o′ ℓ′ e′} (F : Functor J C) where
      private
        module J  = Category J
        open Functor F
        open MR C
        module OP = Prods {Lift ℓ′ J.Obj} (λ j → F₀ (lower j))
        module MP = Prods {∃₂ J._⇒_} (λ { (_ , B , _) → F₀ B })

      src : C.Obj
      src = OP.X

      dst : C.Obj
      dst = MP.X

      ϕ⇒ : (i : ∃₂ J._⇒_) → let (_ , B , _) = i in src C.⇒ F₀ B
      ϕ⇒ (_ , B , _) = OP.π (lift B)

      ϕ : src C.⇒ dst
      ϕ = MP.⟨ ϕ⇒ ⟩

      ψ⇒ : (i : ∃₂ J._⇒_) → let (_ , B , _) = i in src C.⇒ F₀ B
      ψ⇒ (A , B , f) = F₁ f C.∘ OP.π (lift A)

      ψ : src C.⇒ dst
      ψ = MP.⟨ ψ⇒ ⟩

      module eq = Equalizer (equalizer ϕ ψ)

      ⊤ : Co.Cone F
      ⊤ = record
        { N    = eq.obj
        ; apex = record
          { ψ       = λ X → OP.π (lift X) C.∘ eq.arr
          ; commute = λ {X Y} f → begin
            F₁ f C.∘ OP.π (lift X) C.∘ eq.arr ≈˘⟨ pushˡ (MP.commute ψ⇒ _) ⟩
            (MP.π (-, -, f) C.∘ ψ) C.∘ eq.arr ≈˘⟨ pushʳ eq.equality ⟩
            MP.π (-, -, f) C.∘ ϕ C.∘ eq.arr   ≈⟨ pullˡ (MP.commute ϕ⇒ _ ) ⟩
            OP.π (lift Y) C.∘ eq.arr          ∎
          }
        }

      module _ {K : Co.Cone F} where
        private
          module K = Co.Cone F K

        K⇒ : K.N C.⇒ src
        K⇒ = OP.⟨ (λ j → K.ψ (lower j)) ⟩

        Keq : (i : ∃₂ J._⇒_) → ϕ⇒ i C.∘ K⇒ C.≈ ψ⇒ i C.∘ K⇒
        Keq i@(A , B , f) = begin
          ϕ⇒ i C.∘ K⇒    ≈⟨ OP.commute _ _ ⟩
          K.ψ B          ≈˘⟨ K.commute _ ⟩
          F₁ f C.∘ K.ψ A ≈˘⟨ pullʳ (OP.commute _ _) ⟩
          ψ⇒ i C.∘ K⇒    ∎

        !-eq : ϕ C.∘ K⇒ C.≈ ψ C.∘ K⇒
        !-eq = begin
          ϕ C.∘ K⇒                   ≈⟨ MP.⟨⟩∘ _ _ ⟩
          MP.⟨ (λ i → ϕ⇒ i C.∘ K⇒) ⟩ ≈⟨ MP.⟨⟩-cong _ _ Keq ⟩
          MP.⟨ (λ i → ψ⇒ i C.∘ K⇒) ⟩ ≈˘⟨ MP.⟨⟩∘ _ _ ⟩
          ψ C.∘ K⇒                   ∎

        ! : Co.Cones F [ K , ⊤ ]
        ! = record
          { arr     = eq.equalize {h = K⇒} !-eq
          ; commute = λ {j} → begin
            (OP.π (lift j) C.∘ eq.arr) C.∘ eq.equalize !-eq ≈˘⟨ pushʳ eq.universal ⟩
            OP.π (lift j) C.∘ K⇒                            ≈⟨ OP.commute _ _ ⟩
            K.ψ j                                           ∎
          }

        !-unique : (f : Co.Cones F [ K , ⊤ ]) → Co.Cones F [ ! ≈ f ]
        !-unique f = ⟺ (eq.unique eq)
          where module f = Co.Cone⇒ F f
                eq : K⇒ C.≈ eq.arr C.∘ f.arr
                eq = OP.unique′ _ _ λ i → begin
                  OP.π i C.∘ K⇒                 ≈⟨ OP.commute _ _ ⟩
                  K.ψ (lower i)                 ≈˘⟨ f.commute ⟩
                  (OP.π i C.∘ eq.arr) C.∘ f.arr ≈⟨ C.assoc ⟩
                  OP.π i C.∘ eq.arr C.∘ f.arr   ∎

      complete : Limit F
      complete = record
        { terminal = record
          { ⊤        = ⊤
          ; !        = !
          ; !-unique = !-unique
          }
        }

  AllProducts×Equalizer⇒Complete : Complete o′ ℓ′ e′ C
  AllProducts×Equalizer⇒Complete = complete
