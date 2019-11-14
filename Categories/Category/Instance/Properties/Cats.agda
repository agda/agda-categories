{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Properties.Cats where

open import Data.Product

open import Categories.Category
open import Categories.Category.Instance.Cats
open import Categories.Category.Product
open import Categories.Category.Construction.Functors
open import Categories.Category.Cartesian
open import Categories.Category.CartesianClosed
open import Categories.Category.Monoidal.Instance.Cats
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Properties
open import Categories.Functor.Bifunctor
open import Categories.Functor.Bifunctor.Properties
open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; _≃_; _ⓘˡ_; _ⓘʳ_; module ≃)
open import Categories.NaturalTransformation.Properties

import Categories.Object.Product as P
import Categories.Morphism.Reasoning as MR

private
  module Car {l} = Cartesian (Product.Cats-is {l} {l} {l})

Cats-CCC : ∀ {l} → CartesianClosed (Cats l l l)
Cats-CCC {l} = record
  { cartesian = Product.Cats-is
  ; exp       = λ {C D} → record
    { B^A      = Functors C D
    ; product  = Car.product
    ; eval     = eval
    ; λg       = λg
    ; β        = β
    ; λ-unique = λ-unique
    }
  }
  where open P (Cats l l l) renaming (Product to Pro)
        λg : ∀ {E C D : Category l l l} (p : Pro E C) → Functor (Pro.A×B p) D → Functor E (Functors C D)
        λg {E} {C} {D} p F = record
          { F₀           = λ e → record
              { F₀           = λ c → F₀ (rewrap.F₀ (e , c))
              ; F₁           = λ f → F₁ (rewrap.F₁ (E.id , f))
              ; identity     = begin
                  F₁ (rewrap.F₁ (E.id , C.id)) ≈⟨ F-resp-≈ rewrap.identity ⟩
                  F₁ EC.id                     ≈⟨ identity ⟩
                  D.id                         ∎
              ; homomorphism = λ {_ _ _} {f g} → begin
                F₁ (rewrap.F₁ (E.id , g C.∘ f))                         ≈⟨ F-resp-≈ (Functor.homomorphism (appˡ rewrap e)) ⟩
                F₁ (rewrap.F₁ (E.id , g) EC.∘ rewrap.F₁ (E.id , f))     ≈⟨ homomorphism ⟩
                F₁ (rewrap.F₁ (E.id , g)) D.∘ F₁ (rewrap.F₁ (E.id , f)) ∎
              ; F-resp-≈     = λ {_ _} {f g} eq → F-resp-≈ (Functor.F-resp-≈ (appˡ rewrap e) eq)
              }
          ; F₁           = λ {A B} f → record
            { η       = λ c → F₁ (rewrap.F₁ (f , C.id))
            ; commute = λ g → begin
              F₁ (rewrap.F₁ (f , C.id)) D.∘ F₁ (rewrap.F₁ (E.id , g)) ≈˘⟨ homomorphism ⟩
              F₁ (rewrap.F₁ (f , C.id) EC.∘ rewrap.F₁ (E.id , g))     ≈˘⟨ F-resp-≈ [ rewrap ]-commute ⟩
              F₁ (rewrap.F₁ (E.id , g) EC.∘ rewrap.F₁ (f , C.id))     ≈⟨ homomorphism ⟩
              F₁ (rewrap.F₁ (E.id , g)) D.∘ F₁ (rewrap.F₁ (f , C.id)) ∎
            }
          ; identity     = F-resp-≈ rewrap.identity ○ identity
          ; homomorphism = λ {_ _ _} {f g} → begin
            F₁ (rewrap.F₁ (g E.∘ f , C.id))                         ≈⟨ F-resp-≈ (Functor.homomorphism (appʳ rewrap _)) ⟩
            F₁ (rewrap.F₁ (g , C.id) EC.∘ rewrap.F₁ (f , C.id))     ≈⟨ homomorphism ⟩
            F₁ (rewrap.F₁ (g , C.id)) D.∘ F₁ (rewrap.F₁ (f , C.id)) ∎
          ; F-resp-≈     = λ eq → F-resp-≈ (Functor.F-resp-≈ (appʳ rewrap _) eq)
          }
          where module E = Category E
                module C = Category C
                module D = Category D
                open Functor F
                open Pro p renaming (A×B to EC)
                module EC = Category EC
                open D.HomReasoning
                rewrap : Bifunctor E C EC
                rewrap = ⟨ πˡ , πʳ ⟩
                module rewrap = Functor rewrap

        β : ∀ {E C D : Category l l l} (p : Pro E C) {F : Functor (Pro.A×B p) D} →
              eval ∘F (λg p F ∘F Pro.π₁ p ※ idF ∘F Pro.π₂ p) ≃ F
        β {E} {C} {D} p {F} = record
          { F⇒G = record
            { η       = natiso.⇒.η
            ; commute = λ {X Y} f → begin
              natiso.⇒.η Y D.∘ Functor.F₁ (eval ∘F (λg p F ∘F π₁ ※ idF ∘F π₂)) f
                ≡⟨⟩
              natiso.⇒.η Y D.∘ F₁ (rewrap.F₁ (Functor.F₁ π₁ f , C.id)) D.∘ F₁ (rewrap.F₁ (E.id , Functor.F₁ π₂ f))
                ≈˘⟨ refl⟩∘⟨ (F-resp-≈ [ rewrap ]-decompose₁ ○ homomorphism) ⟩
              natiso.⇒.η Y D.∘ F₁ (Functor.F₁ (⟨ πˡ , πʳ ⟩ ∘F (π₁ ※ π₂)) f)
                ≈⟨ natiso.⇒.commute f ⟩
              F₁ f D.∘ natiso.⇒.η X
                ∎
            }
          ; F⇐G = record
            { η       = natiso.⇐.η
            ; commute = λ {X Y} f → begin
              natiso.⇐.η Y D.∘ F₁ f
                ≈⟨ natiso.⇐.commute f ⟩
              F₁ (Functor.F₁ (⟨ πˡ , πʳ ⟩ ∘F (π₁ ※ π₂)) f) D.∘ natiso.⇐.η X
                ≈⟨ (F-resp-≈ [ rewrap ]-decompose₁ ○ homomorphism) ⟩∘⟨refl ⟩
              Functor.F₁ (eval ∘F (λg p F ∘F π₁ ※ idF ∘F π₂)) f D.∘ natiso.⇐.η X
                ∎
            }
          ; iso = natiso.iso
          }
          where module E = Category E
                module C = Category C
                module D = Category D
                open Functor F
                open Pro p renaming (A×B to EC)
                module EC = Category EC
                open D.HomReasoning
                rewrap : Bifunctor E C EC
                rewrap = ⟨ πˡ , πʳ ⟩
                module rewrap = Functor rewrap
                natiso : F ∘F ⟨ πˡ , πʳ ⟩ ∘F (π₁ ※ π₂) ≃ F ∘F idF
                natiso = F ⓘˡ repack∘repack≈id Car.product p
                module natiso = NaturalIsomorphism natiso

        λg-cong : ∀ {E C D : Category l l l} (p : Pro E C) {F G : Functor (Pro.A×B p) D} (F≃G : F ≃ G) →
                    λg p F ≃ λg p G
        λg-cong {E} {C} {D} p {F} {G} F≃G = record
          { F⇒G = record
            { η       = λ e → record
              { η       = λ c → mapped.⇒.η (e , c)
              ; commute = λ f → mapped.⇒.commute (E.id , f)
              }
            ; commute = λ f → mapped.⇒.commute (f , C.id)
            }
          ; F⇐G = record
            { η       = λ e → record
              { η       = λ c → mapped.⇐.η (e , c)
              ; commute = λ f → mapped.⇐.commute (E.id , f)
              }
            ; commute = λ f → mapped.⇐.commute (f , C.id)
            }
          ; iso = λ e → record
            { isoˡ = mapped.iso.isoˡ _
            ; isoʳ = mapped.iso.isoʳ _
            }
          }
          where module E = Category E
                module C = Category C
                open Pro p renaming (A×B to EC)
                rewrap = ⟨ πˡ , πʳ ⟩
                module rewrap = Functor rewrap
                mapped = F≃G ⓘʳ rewrap
                module mapped = NaturalIsomorphism mapped

        λ-unique : ∀ {E C D : Category l l l} (p : Pro E C) {F : Functor (Pro.A×B p) D} {G : Functor E (Functors C D)} →
                     eval ∘F (G ∘F Pro.π₁ p ※ idF ∘F Pro.π₂ p) ≃ F →
                     G ≃ (λg p F)
        λ-unique {E} {C} {D} p {F} {G} iso = ≃.trans (≃.sym cancel) (λg-cong p iso)
          where module E = Category E
                module C = Category C
                module D = Category D
                module G = Functor G
                open Functor F
                open Pro p renaming (A×B to EC)
                module EC = Category EC
                open D.HomReasoning
                open MR D
                rewrap : Bifunctor E C EC
                rewrap = ⟨ πˡ , πʳ ⟩
                module rewrap = Functor rewrap
                natiso : F ∘F ⟨ πˡ , πʳ ⟩ ∘F (π₁ ※ π₂) ≃ F ∘F idF
                natiso = F ⓘˡ repack∘repack≈id Car.product p
                module natiso = NaturalIsomorphism natiso
                project₁′ = project₁ {h = πˡ} {πʳ}
                module project₁′ = NaturalIsomorphism project₁′
                project₂′ = project₂ {h = πˡ} {πʳ}
                module project₂′ = NaturalIsomorphism project₂′
                Gproject₁′ = G ⓘˡ project₁ {h = πˡ} {πʳ}
                module Gproject₁′ = NaturalIsomorphism Gproject₁′
                module π₂r = Functor (π₂ ∘F rewrap)
                module π₁r = Functor (π₁ ∘F rewrap)

                cancel : λg p (eval ∘F (G ∘F Pro.π₁ p ※ idF ∘F Pro.π₂ p)) ≃ G
                cancel = record
                  { F⇒G = record
                    { η       = λ e → 
                      let module Ge  = Functor (G.F₀ e)
                      in record
                      { η       = λ c →
                        let module α = NaturalTransformation (Gproject₁′.⇒.η (e , c))
                        in Ge.F₁ (project₂′.⇒.η (e , c)) D.∘ α.η (π₂r.F₀ (e , c))
                      ; commute = λ {X Y} f →
                        let module α = NaturalTransformation (Gproject₁′.⇒.η (e , X))
                            module γ = NaturalTransformation (Gproject₁′.⇒.η (e , Y))
                            module δ = NaturalTransformation (G.F₁ (π₁r.F₁ (E.id , f)))
                        in begin
                          (Ge.F₁ (project₂′.⇒.η (e , Y)) D.∘ γ.η (π₂r.F₀ (e , Y))) D.∘
                            Functor.F₁ (Functor.F₀ (λg p (eval ∘F (G ∘F π₁ ※ idF ∘F π₂))) e) f
                            ≡⟨⟩
                          (Ge.F₁ (project₂′.⇒.η (e , Y)) D.∘ γ.η (π₂r.F₀ (e , Y))) D.∘
                            δ.η (π₂r.F₀ (e , Y)) D.∘ Functor.F₁ (G.F₀ (π₁r.F₀ (e , X))) (π₂r.F₁ (E.id , f))
                            ≈⟨ refl⟩∘⟨ δ.commute (π₂r.F₁ (E.id , f)) ⟩
                          (Ge.F₁ (project₂′.⇒.η (e , Y)) D.∘ γ.η (π₂r.F₀ (e , Y))) D.∘
                            Functor.F₁ (G.F₀ (π₁r.F₀ (e , Y))) (π₂r.F₁ (E.id , f)) D.∘ δ.η (π₂r.F₀ (e , X))
                            ≈⟨ center (γ.commute (π₂r.F₁ (E.id , f))) ⟩
                          Ge.F₁ (project₂′.⇒.η (e , Y)) D.∘
                          (Ge.F₁ (π₂r.F₁ (E.id , f)) D.∘ γ.η (π₂r.F₀ (e , X))) D.∘
                          δ.η (π₂r.F₀ (e , X))
                            ≈⟨ center⁻¹ refl ([ G ]-resp-∘ (E.Equiv.trans (project₁′.⇒.commute (E.id , f)) E.identityˡ)) ⟩
                          (Ge.F₁ (project₂′.⇒.η (e , Y)) D.∘ Ge.F₁ (π₂r.F₁ (E.id , f))) D.∘ α.η (π₂r.F₀ (e , X))
                            ≈⟨ pushˡ ([ G.F₀ e ]-resp-square (project₂′.⇒.commute (E.id , f))) ⟩
                          Ge.F₁ f D.∘ Ge.F₁ (project₂′.⇒.η (e , X)) D.∘ α.η (π₂r.F₀ (e , X))
                            ∎
                      }
                    ; commute = λ {X Y} f {c} →
                      let module GX = Functor (G.F₀ X)
                          module GY = Functor (G.F₀ Y)
                          module α  = NaturalTransformation (Gproject₁′.⇒.η (X , c))
                          module γ  = NaturalTransformation (Gproject₁′.⇒.η (Y , c))
                          module δ  = NaturalTransformation (G.F₁ (π₁r.F₁ (f , C.id)))
                       in begin
                         (GY.F₁ (project₂′.⇒.η (Y , c)) D.∘ γ.η (π₂r.F₀ (Y , c))) D.∘
                         NaturalTransformation.η (Functor.F₁ (λg p (eval ∘F (G ∘F π₁ ※ idF ∘F π₂))) f) c
                           ≡⟨⟩
                         (GY.F₁ (project₂′.⇒.η (Y , c)) D.∘ γ.η (π₂r.F₀ (Y , c))) D.∘
                         δ.η (π₂r.F₀ (Y , c)) D.∘ Functor.F₁ (G.F₀ (π₁r.F₀ (X , c))) (π₂r.F₁ (f , C.id))
                           ≈⟨ refl⟩∘⟨ δ.commute (π₂r.F₁ (f , C.id)) ⟩
                         (GY.F₁ (project₂′.⇒.η (Y , c)) D.∘ γ.η (π₂r.F₀ (Y , c))) D.∘
                         Functor.F₁ (G.F₀ (π₁r.F₀ (Y , c))) (π₂r.F₁ (f , C.id)) D.∘ δ.η (π₂r.F₀ (X , c))
                           ≈⟨ center (γ.commute (π₂r.F₁ (f , C.id))) ⟩
                         GY.F₁ (project₂′.⇒.η (Y , c)) D.∘
                         (GY.F₁ (π₂r.F₁ (f , C.id)) D.∘ γ.η (π₂r.F₀ (X , c))) D.∘
                         δ.η (π₂r.F₀ (X , c))
                           ≈⟨ center⁻¹ ([ G.F₀ Y ]-resp-square (project₂′.⇒.commute (f , C.id)))
                                       ([ G ]-resp-square (project₁′.⇒.commute (f , C.id))) ⟩
                         (GY.F₁ C.id D.∘ GY.F₁ (project₂′.⇒.η (X , c))) D.∘
                         NaturalTransformation.η (G.F₁ f) (π₂r.F₀ (X , c)) D.∘ α.η (π₂r.F₀ (X , c))
                           ≈⟨ elimˡ GY.identity ⟩∘⟨refl ⟩
                         GY.F₁ (project₂′.⇒.η (X , c)) D.∘ NaturalTransformation.η (G.F₁ f) (π₂r.F₀ (X , c)) D.∘ α.η (π₂r.F₀ (X , c))
                           ≈⟨ pullˡ (⟺ (NaturalTransformation.commute (G.F₁ f) (project₂′.⇒.η (X , c)))) ○ D.assoc ⟩
                         NaturalTransformation.η (G.F₁ f) c D.∘ GX.F₁ (project₂′.⇒.η (X , c)) D.∘ α.η (π₂r.F₀ (X , c))
                           ∎
                    }
                  ; F⇐G = record
                    { η       = λ e →
                      let module Ge  = Functor (G.F₀ e)
                      in record
                      { η       = λ c →
                        let module α = NaturalTransformation (Gproject₁′.⇐.η (e , c))
                        in α.η (π₂r.F₀ (e , c)) D.∘ Ge.F₁ (project₂′.⇐.η (e , c))
                      ; commute = λ {X Y} f →
                        let module α = NaturalTransformation (Gproject₁′.⇐.η (e , X))
                            module γ = NaturalTransformation (Gproject₁′.⇐.η (e , Y))
                            module δ = NaturalTransformation (G.F₁ (π₁r.F₁ (E.id , f)))
                        in begin
                          (γ.η (π₂r.F₀ (e , Y)) D.∘ Ge.F₁ (project₂′.⇐.η (e , Y))) D.∘ Ge.F₁ f
                            ≈⟨ D.assoc ⟩
                          γ.η (π₂r.F₀ (e , Y)) D.∘ Ge.F₁ (project₂′.⇐.η (e , Y)) D.∘ Ge.F₁ f
                            ≈˘⟨ center⁻¹ ([ G ]-resp-∘ (E.Equiv.trans (E.Equiv.sym (project₁′.⇐.commute (E.id , f))) E.identityʳ))
                                         ([ G.F₀ e ]-resp-square (C.Equiv.sym (project₂′.⇐.commute (E.id , f)))) ⟩
                          δ.η (π₂r.F₀ (e , Y)) D.∘
                          (α.η (π₂r.F₀ (e , Y)) D.∘ Ge.F₁ (π₂r.F₁ (E.id , f))) D.∘
                          Ge.F₁ (project₂′.⇐.η (e , X))
                            ≈˘⟨ center (⟺ (α.commute (π₂r.F₁ (E.id , f)))) ⟩
                          (δ.η (π₂r.F₀ (e , Y)) D.∘ Functor.F₁ (G.F₀ (π₁r.F₀ (e , X))) (π₂r.F₁ (E.id , f)))
                            D.∘ α.η (π₂r.F₀ (e , X)) D.∘ Ge.F₁ (project₂′.⇐.η (e , X))
                            ∎
                      }
                    ; commute = λ {X Y} f {c} →
                      let module GX = Functor (G.F₀ X)
                          module GY = Functor (G.F₀ Y)
                          module α  = NaturalTransformation (Gproject₁′.⇐.η (X , c))
                          module γ  = NaturalTransformation (Gproject₁′.⇐.η (Y , c))
                          module δ  = NaturalTransformation (G.F₁ (π₁r.F₁ (f , C.id)))
                       in begin
                         (γ.η (π₂r.F₀ (Y , c)) D.∘ GY.F₁ (project₂′.⇐.η (Y , c))) D.∘ NaturalTransformation.η (G.F₁ f) c
                           ≈˘⟨ pullʳ (NaturalTransformation.commute (G.F₁ f) (project₂′.⇐.η (Y , c))) ○ D.sym-assoc ⟩
                         (γ.η (π₂r.F₀ (Y , c)) D.∘ NaturalTransformation.η (G.F₁ f) (π₂r.F₀ (Y , c))) D.∘ GX.F₁ (project₂′.⇐.η (Y , c))
                           ≈˘⟨ center⁻¹ ([ G ]-resp-square (E.Equiv.sym (project₁′.⇐.commute (f , C.id))))
                                        ([ G.F₀ X ]-resp-square (C.Equiv.sym (project₂′.⇐.commute (f , C.id))) ○ elimʳ GX.identity) ⟩
                         δ.η (π₂r.F₀ (Y , c)) D.∘
                         (α.η (π₂r.F₀ (Y , c)) D.∘ GX.F₁ (π₂r.F₁ (f , C.id))) D.∘
                         GX.F₁ (project₂′.⇐.η (X , c))
                           ≈˘⟨ center (⟺ (α.commute (π₂r.F₁ (f , C.id)))) ⟩
                         (δ.η (π₂r.F₀ (Y , c)) D.∘ Functor.F₁ (G.F₀ (π₁r.F₀ (X , c))) (π₂r.F₁ (f , C.id))) D.∘
                         α.η (π₂r.F₀ (X , c)) D.∘ GX.F₁ (project₂′.⇐.η (X , c))
                           ∎
                    }
                  ; iso = λ e → record
                    { isoˡ = center ([ G.F₀ e ]-resp-∘ (project₂′.iso.isoˡ _)) ○
                             D.∘-resp-≈ʳ (elimˡ (Functor.identity (G.F₀ e))) ○
                             Gproject₁′.iso.isoˡ _
                    ; isoʳ = center (Gproject₁′.iso.isoʳ _) ○
                             D.∘-resp-≈ʳ D.identityˡ ○
                             [ G.F₀ e ]-resp-∘ (project₂′.iso.isoʳ _) ○
                             Functor.identity (G.F₀ e)
                    }
                  }
