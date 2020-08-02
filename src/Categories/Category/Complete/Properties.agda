{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Complete.Properties {o ℓ e} (C : Category o ℓ e) where

open import Level
open import Data.Product
open import Relation.Binary

open import Categories.Category.Complete
open import Categories.Category.Complete.Finitely
open import Categories.Category.Construction.Functors
open import Categories.Diagram.Limit as Lim
open import Categories.Diagram.Limit.Properties
open import Categories.Diagram.Equalizer.Limit C
open import Categories.Diagram.Cone.Properties
open import Categories.Object.Terminal
open import Categories.Object.Product.Limit C
open import Categories.Object.Terminal.Limit C
open import Categories.Functor
open import Categories.Functor.Limits
open import Categories.Functor.Properties
open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_)

import Categories.Category.Construction.Cones as Co
import Categories.Morphism.Reasoning as MR
import Categories.Morphism as Mor

-- exports
open import Categories.Category.Complete.Properties.Construction public
open import Categories.Category.Complete.Properties.SolutionSet public


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
    ; equalizer = complete⇒equalizer Com
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

      ev : C.Obj → Functor D^C D
      ev = evalF C D

      F[-,_] : C.Obj → Functor J D
      F[-, X ] = ev X ∘F F

      F[-,-] : Functor C (Functors J D)
      F[-,-] = record
        { F₀           = F[-,_]
        ; F₁           = λ {A B} f → ntHelper record
          { η       = λ j → F₀.₁ j f
          ; commute = λ {j k} g → begin
            F₀.₁ k f D.∘ F₁.η g A D.∘ F₀.₁ j C.id   ≈⟨ pullˡ (F₁.sym-commute g f) ⟩
            (F₁.η g B D.∘ F₀.₁ j f) D.∘ F₀.₁ j C.id ≈⟨ elimʳ (F₀.identity _) ⟩
            F₁.η g B D.∘ F₀.₁ j f                   ≈⟨ introʳ (F₀.identity _) ⟩∘⟨refl ⟩
            (F₁.η g B D.∘ F₀.₁ j C.id) D.∘ F₀.₁ j f ∎
          }
        ; identity     = F₀.identity _
        ; homomorphism = F₀.homomorphism _
        ; F-resp-≈     = λ eq → F₀.F-resp-≈ _ eq
        }
        where open D.HomReasoning
              open MR D

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
          ; commute = λ f → D.∘-resp-≈ˡ (elimʳ (F₀.identity _)) ○ commute f
          }
        }
        where open FCone K
              open D.HomReasoning
              open MR D

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
          ; commute = λ f {X} → ∘-resp-≈ˡ (introʳ (F₀.identity _)) ○ limit-commute X f
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
          { ⊤             = ⊤
          ; ⊤-is-terminal = record
            { !        = λ {K} →
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
        }
        where open D
              open D.HomReasoning
              open MR D

      module _ (L : Limit F) (X : C.Obj) where
        module LimExpanded (L : Limit F) where
          private
            module L = Limit L
          open L public
          module apex   = Functor L.apex
          module proj j = NaturalTransformation (L.proj j)

        module L = LimExpanded L
        module complete = LimExpanded complete

        open MR D
        open D.HomReasoning

        cone-iso :  Mor._≅_ (Co.Cones F) complete.limit L.limit
        cone-iso = up-to-iso-cone F complete L
        module cone-iso where
          open Mor._≅_ cone-iso public
          module from where
            open Co.Cone⇒ F from public
            module arr = NaturalTransformation arr
          module to where
            open Co.Cone⇒ F to public
            module arr = NaturalTransformation arr

          ft-iso : Mor._≅_ D^C complete.apex L.apex
          ft-iso = Lim.up-to-iso F complete L
          module ft-iso = Mor._≅_ ft-iso

          apex-iso : ∀ X → Mor._≅_ D (complete.apex.₀ X) (L.apex.₀ X)
          apex-iso X = record
            { from = NaturalTransformation.η ft-iso.from X
            ; to   = NaturalTransformation.η ft-iso.to X
            ; iso  = record
              { isoˡ = ft-iso.isoˡ
              ; isoʳ = ft-iso.isoʳ
              }
            }

        ! : {K : Co.Cone F[-, X ]} → Co.Cone⇒ F[-, X ] K (F-map-Coneˡ (ev X) L.limit)
        ! {K} = record
          { arr     = cone-iso.from.arr.η X D.∘ rep X K
          ; commute = λ {j} → begin
            (L.proj.η j X D.∘ L.apex.₁ C.id) D.∘ cone-iso.from.arr.η X D.∘ rep X K
              ≈⟨ elimʳ L.apex.identity ⟩∘⟨refl ⟩
            L.proj.η j X D.∘ cone-iso.from.arr.η X D.∘ rep X K
              ≈⟨ pullˡ cone-iso.from.commute ⟩
            complete.proj.η j X D.∘ rep X K
              ≈⟨ LimFX.commute X {_} {K} ⟩
            ψ j
              ∎
          }
          where open Co.Cone _ K
        module ! K = Co.Cone⇒ _ (! {K})

        !-unique : {K : Co.Cone F[-, X ]} (f : Co.Cone⇒ F[-, X ] K (F-map-Coneˡ (ev X) L.limit)) →
                   !.arr K D.≈ Co.Cone⇒.arr f
        !-unique {K} f = ⟺ (switch-tofromˡ (cone-iso.apex-iso X) target)
          where open Co.Cone _ K
                module f = Co.Cone⇒ _ f
                target : cone-iso.to.arr.η X D.∘ f.arr D.≈ rep X K
                target = terminal.!-unique₂ X {K}
                         {record
                           { arr     = cone-iso.to.arr.η X D.∘ f.arr
                           ; commute = λ {j} → begin
                             proj X j D.∘ cone-iso.to.arr.η X D.∘ f.arr ≈⟨ pullˡ cone-iso.to.commute ⟩
                             L.proj.η j X D.∘ f.arr                     ≈⟨ introʳ L.apex.identity ⟩∘⟨refl ⟩
                             (L.proj.η j X D.∘ L.apex.₁ C.id) D.∘ f.arr ≈⟨ f.commute ⟩
                             ψ j                                        ∎
                           }}
                         {record
                           { arr     = rep X K
                           ; commute = λ {j} → begin
                             proj X j D.∘ rep X K                       ≈⟨ LimFX.commute X ⟩
                             ψ j                                        ∎
                           }}

        preserves : IsTerminal (Co.Cones F[-, X ]) (F-map-Coneˡ (ev X) L.limit)
        preserves = record
          { !        = !
          ; !-unique = !-unique
          }

  Functors-Complete : Complete o″ ℓ″ e″ D^C
  Functors-Complete = complete

  evalF-Continuous : ∀ X → Continuous o″ ℓ″ e″ (evalF C D X)
  evalF-Continuous X {J} {F} L = preserves F L X
