{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Profunctor where

open import Level
open import Data.Empty using (⊥)
open import Data.Product using (_,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using () renaming (_∘′_ to _∙_)
open import Function.Equality using (_⟨$⟩_; cong)
open import Relation.Binary using (Setoid; module Setoid)
open import Relation.Binary.Construct.Closure.SymmetricTransitive as ST using (Plus⇔; minimal)
import Relation.Binary.Reasoning.Setoid as SetoidR

open import Data.Product
open import Relation.Binary.Bundles
open import Categories.Category
open import Categories.Category.Construction.Functors using (Functors; curry)
open import Categories.Category.Instance.Cats using (Cats)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Product using ()
open import Categories.Functor hiding (id)
open import Categories.Functor.Bifunctor using (Bifunctor; appˡ; appʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.Functor.Construction.LiftSetoids using (LiftSetoids)
open import Categories.Functor.Hom using (Hom[_][-,-])
open import Categories.Morphism.Reasoning using (id-comm; id-comm-sym)
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ᵥ_; _∘ˡ_; id)
open import Categories.NaturalTransformation.Equivalence using (_≃_; ≃-isEquivalence)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)
open import Categories.NaturalTransformation.Properties using (appˡ-nat; appʳ-nat)
open import Function.Equality using (Π; _⟨$⟩_; cong)

open Setoid renaming (_≈_ to _[[_≈_]])

record Profunctor {o ℓ e} {o′ ℓ′ e′} ℓ″ e″ (C : Category o ℓ e) (D : Category o′ ℓ′ e′) : Set (o ⊔ o′ ⊔ suc (ℓ ⊔ ℓ′ ⊔ ℓ″ ⊔ e ⊔ e′ ⊔ e″)) where
  constructor pro
  field
    bimodule : Bifunctor (Category.op D) C (Setoids (ℓ ⊔ ℓ′ ⊔ ℓ″) (e ⊔ e′ ⊔ e″))
  open Bifunctor bimodule public

  cograph : Category _ _ _
  cograph = record
    { Obj = D.Obj ⊎ C.Obj
    ; _⇒_ = λ
      { (inj₁ d) (inj₁ d′) → Lift (ℓ ⊔ ℓ″) (D [ d , d′ ])
      ; (inj₁ d) (inj₂ c) → Setoid.Carrier (F₀ (d , c))
      ; (inj₂ c) (inj₁ d) → Lift _ ⊥
      ; (inj₂ c) (inj₂ c′) → Lift (ℓ′ ⊔ ℓ″) (C [ c , c′ ])
      }
    ; _≈_ = λ
      { {inj₁ d} {inj₁ d′} f g → Lift (e ⊔ e″) (D [ lower f ≈ lower g ])
      ; {inj₁ d} {inj₂ c} p q → Setoid._≈_ (F₀ (d , c)) p q
      ; {inj₂ c} {inj₁ d} () ()
      ; {inj₂ c} {inj₂ c′} f g → Lift (e′ ⊔ e″) (C [ lower f ≈ lower g ])
      }
    ; id = λ
      { {inj₁ d} → lift D.id
      ; {inj₂ c} → lift C.id
      }
    ; _∘_ = λ
      { {inj₁ dA} {inj₁ dB} {inj₁ dC} f g → lift (D [ lower f ∘ lower g ])
      ; {inj₁ dA} {inj₁ dB} {inj₂ cC} p g → ₁ˡ (lower g) ⟨$⟩ p
      ; {inj₁ dA} {inj₂ cB} {inj₂ cC} f q → ₁ʳ (lower f) ⟨$⟩ q
      ; {inj₂ cA} {inj₂ cB} {inj₂ cC} f g → lift (C [ lower f ∘ lower g ])
      }
    ; assoc = λ
      { {inj₁ dA} {inj₁ dB} {inj₁ dC} {inj₁ dD} {f} {g} {h} → lift D.assoc
      ; {inj₁ dA} {inj₁ dB} {inj₁ dC} {inj₂ cD} {f} {g} {r} → Setoid.sym (F₀ _) (homomorphismˡ (Setoid.refl (F₀ _)))
      ; {inj₁ dA} {inj₁ dB} {inj₂ cC} {inj₂ cD} {f} {q} {h} → Setoid.sym (F₀ _) ([ bimodule ]-commute (Setoid.refl (F₀ _)))
      ; {inj₁ dA} {inj₂ cB} {inj₂ cC} {inj₂ cD} {p} {g} {h} → homomorphismʳ (Setoid.refl (F₀ _))
      ; {inj₂ cA} {inj₂ cB} {inj₂ cC} {inj₂ cD} {f} {g} {h} → lift C.assoc
      }
    ; sym-assoc = λ
      { {inj₁ dA} {inj₁ dB} {inj₁ dC} {inj₁ dD} {f} {g} {h} → lift D.sym-assoc
      ; {inj₁ dA} {inj₁ dB} {inj₁ dC} {inj₂ cD} {f} {g} {r} → homomorphismˡ (Setoid.refl (F₀ _))
      ; {inj₁ dA} {inj₁ dB} {inj₂ cC} {inj₂ cD} {f} {q} {h} → [ bimodule ]-commute (Setoid.refl (F₀ _))
      ; {inj₁ dA} {inj₂ cB} {inj₂ cC} {inj₂ cD} {p} {g} {h} → Setoid.sym (F₀ _) (homomorphismʳ (Setoid.refl (F₀ _)))
      ; {inj₂ cA} {inj₂ cB} {inj₂ cC} {inj₂ cD} {f} {g} {h} → lift C.sym-assoc
      }
    ; identityˡ = λ
      { {inj₁ dA} {inj₁ dB} {f} → lift D.identityˡ
      ; {inj₁ dA} {inj₂ cB} {p} → identity (Setoid.refl (F₀ _))
      ; {inj₂ cA} {inj₂ cB} {f} → lift C.identityˡ
      }
    ; identityʳ = λ
      { {inj₁ dA} {inj₁ dB} {f} → lift D.identityʳ
      ; {inj₁ dA} {inj₂ cB} {p} → identity (Setoid.refl (F₀ _))
      ; {inj₂ cA} {inj₂ cB} {f} → lift C.identityʳ
      }
    ; identity² = λ
      { {inj₁ d} → lift D.identity²
      ; {inj₂ c} → lift C.identity²
      }
    ; equiv = λ
      { {inj₁ dA} {inj₁ dB} → record { refl = lift D.Equiv.refl ; sym = λ x → lift (D.Equiv.sym (lower x)) ; trans = λ x y → lift (D.Equiv.trans (lower x) (lower y)) }
      ; {inj₁ dA} {inj₂ cB} → record { refl = Setoid.refl (F₀ _) ; sym = Setoid.sym (F₀ _) ; trans = Setoid.trans (F₀ _) }
      ; {inj₂ cA} {inj₁ dB} → record { refl = λ {} ; sym = λ {} ; trans = λ {} }
      ; {inj₂ cA} {inj₂ cB} → record { refl = lift C.Equiv.refl ; sym = λ x → lift (C.Equiv.sym (lower x)) ; trans = λ x y → lift (C.Equiv.trans (lower x) (lower y)) }}
    ; ∘-resp-≈ = λ
      { {inj₁ dA} {inj₁ dB} {inj₁ dC} {f} {h} {g} {i} → λ x y → lift (D.∘-resp-≈ (lower x) (lower y))
      ; {inj₁ dA} {inj₁ dB} {inj₂ cC} {f} {h} {g} {i} → λ f≈h g≈i → resp-≈ˡ (lower g≈i) f≈h
      ; {inj₁ dA} {inj₂ cB} {inj₂ cC} {f} {h} {g} {i} → λ f≈h g≈i → resp-≈ʳ (lower f≈h) g≈i
      ; {inj₂ cA} {inj₂ cB} {inj₂ cC} {f} {h} {g} {i} → λ x y → lift (C.∘-resp-≈ (lower x) (lower y))
      }
    }
    where
    module C = Category C
    module D = Category D

  module cograph where
    open Category cograph public

    Inj₁ : Functor D cograph
    Inj₁ = record
      { F₀ = inj₁
      ; F₁ = lift
      ; identity = lift (Category.Equiv.refl D)
      ; homomorphism = lift (Category.Equiv.refl D)
      ; F-resp-≈ = lift
      }
    module Inj₁ = Functor Inj₁

    Inj₂ : Functor C cograph
    Inj₂ = record
      { F₀ = inj₂
      ; F₁ = lift
      ; identity = lift (Category.Equiv.refl C)
      ; homomorphism = lift (Category.Equiv.refl C)
      ; F-resp-≈ = lift
      }
    module Inj₂ = Functor Inj₂

-- Calling the profunctor identity "id" is a bad idea
proid : ∀ {o ℓ e} → {C : Category o ℓ e} → Profunctor zero zero C C
proid {C = C} = pro (Hom[ C ][-,-])

module FormalComposite {o ℓ e} {ℓ′ e′ ℓ″ e″} (C : Category o ℓ e) (F : Functor C (Setoids ℓ′ e′)) (G : Functor (Category.op C) (Setoids ℓ″ e″)) where
  open Category C
  open Functor F
  module G = Functor G

  record T : Set (o ⊔ ℓ′ ⊔ ℓ″) where
    field
      rendezvous : Obj
      in-side : Setoid.Carrier (F₀ rendezvous)
      out-side : Setoid.Carrier (G.₀ rendezvous)

  record Twines (A B : T) : Set (ℓ ⊔ e′ ⊔ e″) where
    field
      twiner : C [ T.rendezvous A , T.rendezvous B ]
      in-tertwines : F₀ (T.rendezvous B) [[ T.in-side B ≈ F₁ twiner ⟨$⟩ (T.in-side A) ]]
      out-ertwines : G.₀ (T.rendezvous A) [[ T.out-side A ≈ G.₁ twiner ⟨$⟩ (T.out-side B) ]]

  open Twines

  category : Category _ _ _
  category = record
    { Obj = T
    ; _⇒_ = Twines
    ; _≈_ = λ f g → C [ Twines.twiner f ≈ Twines.twiner g ]
    ; id = λ {c} → record
      { twiner = Category.id C
      ; in-tertwines = let x = F₀ (T.rendezvous c) in sym x (identity (refl x))
      ; out-ertwines = let x = G.₀ (T.rendezvous c) in sym x (G.identity (refl x)) }
    ; _∘_ = λ {a b c} f g → record
      { twiner = twiner f ∘ twiner g
      ; in-tertwines = let open SetoidR (F₀ (T.rendezvous c)) in
        begin
          T.in-side c
        ≈⟨ in-tertwines f ⟩
          F₁ (twiner f) ⟨$⟩ T.in-side b
        ≈⟨ F-resp-≈ Equiv.refl (in-tertwines g) ⟩
          F₁ (twiner f) ⟨$⟩ (F₁ (twiner g) ⟨$⟩ T.in-side a)
        ≈⟨ sym (F₀ (T.rendezvous c)) (homomorphism (refl (F₀ (T.rendezvous a)))) ⟩
          F₁ (twiner f ∘ twiner g) ⟨$⟩ T.in-side a
        ∎
      ; out-ertwines = let open SetoidR (G.₀ (T.rendezvous a)) in
        begin
          T.out-side a
        ≈⟨ out-ertwines g ⟩
          G.₁ (twiner g) ⟨$⟩ T.out-side b
        ≈⟨ G.F-resp-≈ Equiv.refl (out-ertwines f) ⟩
          G.₁ (twiner g) ⟨$⟩ (G.₁ (twiner f) ⟨$⟩ T.out-side c)
        ≈⟨ sym (G.₀ (T.rendezvous a)) (G.homomorphism (refl (G.₀ (T.rendezvous c)))) ⟩
          G.₁ (twiner f ∘ twiner g) ⟨$⟩ T.out-side c
        ∎
      }
    ; assoc = assoc
    ; sym-assoc = sym-assoc
    ; identityˡ = identityˡ
    ; identityʳ = identityʳ
    ; identity² = identity²
    ; equiv = record { refl = Equiv.refl ; sym = Equiv.sym ; trans = Equiv.trans }
    ; ∘-resp-≈ = ∘-resp-≈
    }

  setoid = ST.setoid Twines (Category.id category)

-- this is the left adjoint to Disc : Setoids ⇒ Cats
Π₀ : ∀ {o ℓ e} → Functor (Cats o ℓ e) (Setoids o (o ⊔ ℓ))
Π₀ = record
  { F₀ = λ C → ST.setoid (Category._⇒_ C) (Category.id C)
  ; F₁ = λ F → record
    { _⟨$⟩_ = Functor.F₀ F
    ; cong = ST.gmap (Functor.F₀ F) (Functor.F₁ F)
    }
  ; identity = λ x → x
  ; homomorphism = λ {_ _ _ F G} → ST.gmap (Functor.F₀ G ∙ Functor.F₀ F) (Functor.F₁ G ∙ Functor.F₁ F)
  ; F-resp-≈ = my-resp _ _
  }
  where
  my-resp : ∀ {A B : Category _ _ _} (f g : Functor A B) (f≅g : NaturalIsomorphism f g) {x y} → Plus⇔ (Category._⇒_ A) x y → Plus⇔ (Category._⇒_ B) (Functor.F₀ f x) (Functor.F₀ g y)
  my-resp {A} {B} f g f≅g {x} {y} (Plus⇔.forth m) = Plus⇔.forth (B [ NaturalIsomorphism.⇒.η f≅g _ ∘ Functor.F₁ f m ])
  my-resp {A} {B} f g f≅g {x} {y} (Plus⇔.back m) = Plus⇔.back (B [ Functor.F₁ f m ∘ NaturalIsomorphism.⇐.η f≅g _ ])
  my-resp {A} {B} f g f≅g {x} {y} (Plus⇔.forth⁺ m ms) = Plus⇔.forth⁺ (B [ NaturalIsomorphism.⇒.η f≅g _ ∘ Functor.F₁ f m ]) (ST.gmap (Functor.F₀ g) (Functor.F₁ g) ms)
  my-resp {A} {B} f g f≅g {x} {y} (Plus⇔.back⁺ m ms) = Plus⇔.back⁺ (B [ Functor.F₁ f m ∘ NaturalIsomorphism.⇐.η f≅g _ ]) (ST.gmap (Functor.F₀ g) (Functor.F₁ g) ms)

_ⓟ′_ : ∀ {oC ℓC eC oD ℓD eD oE ℓE eE ℓP eP ℓQ eQ} {C : Category oC ℓC eC} {D : Category oD ℓD eD} {E : Category oE ℓE eE} (P : Profunctor ℓP eP D E) (Q : Profunctor ℓQ eQ C D) → Bifunctor (Category.op E) C (Cats (oD ⊔ ℓC ⊔ ℓD ⊔ ℓE ⊔ ℓP ⊔ ℓQ) (ℓD ⊔ eC ⊔ eD ⊔ eE ⊔ eP ⊔ eQ) (eD))
_ⓟ′_ {C = C} {D = D} {E = E} P Q = record
  { F₀ = my-F₀
  ; F₁ = my-F₁
  ; identity = my-identity
  ; homomorphism = my-homomorphism _ _ _ _
  ; F-resp-≈ = λ (e , c) → my-resp c e
  }
  where
  module P = Profunctor P
  module Q = Profunctor Q
  module C = Category C
  module D = Category D
  module E = Category E
  open FormalComposite.T

  my-F₀ : (Category.Obj E × Category.Obj C) → Category _ _ _
  my-F₀ (e , c) = FormalComposite.category D (appˡ P.bimodule e) (appʳ Q.bimodule c)
  my-F₁$ : ∀ {cA cB eA eB} → (E [ eB , eA ] × C [ cA , cB ]) → FormalComposite.T D (appˡ P.bimodule eA) (appʳ Q.bimodule cA) → FormalComposite.T D (appˡ P.bimodule eB) (appʳ Q.bimodule cB)
  my-F₁$ (g , f) x = record
    { rendezvous = rendezvous x
    ; in-side = P.₁ (g , D.id) ⟨$⟩ in-side x
    ; out-side = Q.₁ (D.id , f) ⟨$⟩ out-side x
    }
  my-F₁ : ∀ {cA cB eA eB} → (E [ eB , eA ] × C [ cA , cB ]) → Cats _ _ _ [ my-F₀ (eA , cA) , my-F₀ (eB , cB) ]
  my-F₁ (g , f) = record
    { F₀ = my-F₁$ (g , f)
    ; F₁ = λ {x y} h → record
      { twiner = FormalComposite.Twines.twiner h
      ; in-tertwines = let open SetoidR (P.₀ (_ , rendezvous y)) in
        begin
          P.₁ˡ g ⟨$⟩ in-side y
        ≈⟨ cong (P.₁ˡ g) (FormalComposite.Twines.in-tertwines h) ⟩
          P.₁ˡ g ⟨$⟩ (P.₁ʳ (FormalComposite.Twines.twiner h) ⟨$⟩ in-side x)
        ≈˘⟨ [ P.bimodule ]-commute (refl (P.₀ _)) ⟩
          P.₁ʳ (FormalComposite.Twines.twiner h) ⟨$⟩ (P.₁ˡ g ⟨$⟩ in-side x)
        ∎
      ; out-ertwines = let open SetoidR (Q.₀ (rendezvous x , _)) in
        begin
          Q.₁ʳ f ⟨$⟩ out-side x
        ≈⟨ cong (Q.₁ (D.id , f)) (FormalComposite.Twines.out-ertwines h) ⟩
          Q.₁ʳ f ⟨$⟩ (Q.₁ˡ (FormalComposite.Twines.twiner h) ⟨$⟩ out-side y)
        ≈⟨ [ Q.bimodule ]-commute (refl (Q.₀ _)) ⟩
          Q.₁ˡ (FormalComposite.Twines.twiner h) ⟨$⟩ (Q.₁ʳ f ⟨$⟩ out-side y)
        ∎
      }
    ; identity = D.Equiv.refl
    ; homomorphism = D.Equiv.refl
    ; F-resp-≈ = Function.id
    }
  my-identity : ∀ {c e} → Cats _ _ _ [ my-F₁ (E.id {e} , C.id {c}) ≈ Category.id (Cats _ _ _) ]
  my-identity {c} {e} = record
    { F⇒G = record
      { η = λ x → record
        { twiner = D.id
        ; in-tertwines = Setoid.sym (P.₀ _) (P.identity (P.identity (Setoid.refl (P.₀ _))))
        ; out-ertwines = Setoid.refl (Q.₀ _)
        }
      ; commute = λ f → id-comm-sym D
      ; sym-commute = λ f → id-comm D
      }
    ; F⇐G = record
      { η = λ x → record
        { twiner = D.id
        ; in-tertwines = Setoid.refl (P.₀ _)
        ; out-ertwines = Setoid.sym (Q.₀ _) (Q.identity (Q.identity (Setoid.refl (Q.₀ _))))
        }
      ; commute = λ f → id-comm-sym D
      ; sym-commute = λ f → id-comm D
      }
    ; iso = λ X → record
      { isoˡ = D.identity²
      ; isoʳ = D.identity²
      }
    }
  my-homomorphism : ∀ {cX cY cZ eX eY eZ} (cf : C [ cX , cY ]) (ef : E [ eY , eX ]) (cg : C [ cY , cZ ]) (eg : E [ eZ , eY ]) → Cats _ _ _ [ my-F₁ (E [ ef ∘ eg ] , C [ cg ∘ cf ]) ≈ Cats _ _ _ [ my-F₁ (eg , cg) ∘ my-F₁ (ef , cf) ] ]
  my-homomorphism {cX} {cY} {cZ} {eX} {eY} {eZ} cf ef cg eg = record
    { F⇒G = record
      { η = λ X → record
        { twiner = D.id
        ; in-tertwines = let open SetoidR (P.₀ (eZ , rendezvous X)) in
          begin
            P.₁ˡ eg ⟨$⟩ (P.₁ˡ ef ⟨$⟩ in-side X)
          ≈˘⟨ P.homomorphismˡ (Setoid.refl (P.₀ _)) ⟩
            P.₁ˡ (E [ ef ∘ eg ]) ⟨$⟩ in-side X
          ≈˘⟨ P.identity (Setoid.refl (P.₀ _)) ⟩
            P.₁ʳ D.id ⟨$⟩ (P.₁ˡ (E [ ef ∘ eg ]) ⟨$⟩ in-side X)
          ∎
        ; out-ertwines = let open SetoidR (Q.₀ (rendezvous X , cZ)) in
          begin
            Q.₁ʳ (C [ cg ∘ cf ]) ⟨$⟩ out-side X
          ≈⟨ Q.homomorphismʳ (Setoid.refl (Q.₀ _)) ⟩
            Q.₁ʳ cg ⟨$⟩ (Q.₁ʳ cf ⟨$⟩ out-side X)
          ≈˘⟨ Q.identity (Setoid.refl (Q.₀ _)) ⟩
            Q.₁ˡ D.id ⟨$⟩ (Q.₁ʳ cg ⟨$⟩ (Q.₁ʳ cf ⟨$⟩ out-side X))
          ∎
        }
      ; commute = λ f → id-comm-sym D
      ; sym-commute = λ f → id-comm D
      }
    ; F⇐G = record
      { η = λ X → record
        { twiner = D.id
        ; in-tertwines = let open SetoidR (P.₀ (eZ , rendezvous X)) in
          begin
            P.₁ˡ (E [ ef ∘ eg ]) ⟨$⟩ in-side X
          ≈⟨ P.homomorphismˡ (Setoid.refl (P.₀ _)) ⟩
            P.₁ˡ eg ⟨$⟩ (P.₁ˡ ef ⟨$⟩ in-side X)
          ≈˘⟨ P.identity (Setoid.refl (P.₀ _)) ⟩
            P.₁ʳ D.id ⟨$⟩ (P.₁ˡ eg ⟨$⟩ (P.₁ˡ ef ⟨$⟩ in-side X))
          ∎
        ; out-ertwines = let open SetoidR (Q.₀ (rendezvous X , cZ)) in
          begin
            Q.₁ʳ cg ⟨$⟩ (Q.₁ʳ cf ⟨$⟩ out-side X)
          ≈˘⟨ Q.homomorphismʳ (Setoid.refl (Q.₀ _)) ⟩
            Q.₁ʳ (C [ cg ∘ cf ]) ⟨$⟩ out-side X
          ≈˘⟨ Q.identity (Setoid.refl (Q.₀ _)) ⟩
            Q.₁ˡ D.id ⟨$⟩ (Q.₁ʳ (C [ cg ∘ cf ]) ⟨$⟩ out-side X)
          ∎
        }
      ; commute = λ f → id-comm-sym D
      ; sym-commute = λ f → id-comm D
      }
    ; iso = λ X → record { isoˡ = D.identity² ; isoʳ = D.identity² } }
  my-resp : ∀ {cA cB eA eB} {cf cg : C [ cA , cB ]} {ef eg : E [ eB , eA ]} → C [ cf ≈ cg ] → E [ ef ≈ eg ] → Cats _ _ _ [ my-F₁ (ef , cf) ≈ my-F₁ (eg , cg) ]
  my-resp {cA} {cB} {eA} {eB} {cf} {cg} {ef} {eg} cf≈cg ef≈eg = record
    { F⇒G = record
      { η = λ X → record
        { twiner = D.id
        ; in-tertwines = Setoid.sym (P.₀ _) (P.identity (P.resp-≈ˡ ef≈eg (Setoid.refl (P.₀ _))))
        ; out-ertwines = Setoid.sym (Q.₀ _) (Q.identity (Q.resp-≈ʳ (C.Equiv.sym cf≈cg) (Setoid.refl (Q.₀ _))))
        }
      ; commute = λ f → id-comm-sym D
      ; sym-commute = λ f → id-comm D
      }
    ; F⇐G = record
      { η = λ X → record
        { twiner = D.id
        ; in-tertwines = Setoid.sym (P.₀ _) (P.identity (P.resp-≈ˡ (E.Equiv.sym ef≈eg) (Setoid.refl (P.₀ _))))
        ; out-ertwines = Setoid.sym (Q.₀ _) (Q.identity (Q.resp-≈ʳ cf≈cg (Setoid.refl (Q.₀ _))))
        }
      ; commute = λ f → id-comm-sym D
      ; sym-commute = λ f → id-comm D
      }
    ; iso = λ X → record { isoˡ = D.identity² ; isoʳ = D.identity² }
    }

_ⓟ_ : ∀ {oC ℓC eC oD ℓD eD oE ℓE eE ℓP eP ℓQ eQ} {C : Category oC ℓC eC} {D : Category oD ℓD eD} {E : Category oE ℓE eE} (P : Profunctor ℓP eP D E) (Q : Profunctor ℓQ eQ C D) → Profunctor (oD ⊔ ℓD ⊔ ℓP ⊔ ℓQ) (ℓC ⊔ oD ⊔ ℓD ⊔ eD ⊔ ℓE ⊔ ℓP ⊔ eP ⊔ ℓQ ⊔ eQ) C E
_ⓟ_ P Q = pro (Π₀ ∘F (P ⓟ′ Q))

-- formulas from https://ncatlab.org/nlab/show/2-category+equipped+with+proarrows#limits
-- XXX actually prove these are adjoints to composition

_▻_ : ∀ {oC ℓC eC oD ℓD eD oE ℓE eE ℓP eP ℓQ eQ} {C : Category oC ℓC eC} {D : Category oD ℓD eD} {E : Category oE ℓE eE} (P : Profunctor ℓP eP D E) (Q : Profunctor ℓQ eQ C E) → Profunctor (oE ⊔ ℓE ⊔ ℓP ⊔ ℓQ ⊔ eC ⊔ eD ⊔ eE ⊔ eP ⊔ eQ) (oE ⊔ ℓC ⊔ ℓD ⊔ ℓE ⊔ ℓP ⊔ ℓQ ⊔ eE ⊔ eP ⊔ eQ) C D
_▻_ {oC} {ℓC} {eC} {oD} {ℓD} {eD} {oE} {ℓE} {eE} {ℓP} {eP} {ℓQ} {eQ} {C} {D} {E} P Q = pro (record
  { F₀ = λ (d , c) → Category.hom-setoid (Functors E.op (Setoids _ _)) {LiftSetoids (ℓC ⊔ ℓQ) (eC ⊔ eQ) ∘F appʳ P.bimodule d} {LiftSetoids (ℓD ⊔ ℓP) (eD ⊔ eP) ∘F appʳ Q.bimodule c}
  ; F₁ = λ (df , cf) → record
    { _⟨$⟩_ = λ ϕ → (LiftSetoids (ℓD ⊔ ℓP) (eD ⊔ eP) ∘ˡ appʳ-nat Q.bimodule cf) ∘ᵥ ϕ ∘ᵥ LiftSetoids (ℓC ⊔ ℓQ) (eC ⊔ eQ) ∘ˡ appʳ-nat P.bimodule df
    ; cong = λ {σ τ} σ≈τ {e x y} x≈y → lift (cong (Q.₁ʳ cf) (lower (σ≈τ (lift (cong (P.₁ʳ df) (lower x≈y))))))
    }
  ; identity = λ {(d , c)} {σ τ} σ≈τ {e x y} x≈y → lift (Q.identity (lower (σ≈τ (lift (P.identity (lower x≈y))))))
  ; homomorphism = λ {(dX , cX) (dY , cY) (dZ , cZ) (df , cf) (dg , cg) σ τ} σ≈τ {e x y} x≈y → lift (Q.homomorphismʳ (lower (σ≈τ (lift (P.homomorphismʳ (lower x≈y))))))
  ; F-resp-≈ = λ {(dA , cA) (dB , cB) (df , cf) (dg , cg)} (df≈dg , cf≈cg) {σ τ} σ≈τ {e x y} x≈y → lift (Q.resp-≈ʳ cf≈cg (lower (σ≈τ (lift (P.resp-≈ʳ df≈dg (lower x≈y))))))
  })
  where
  module P = Profunctor P
  module Q = Profunctor Q
  module C = Category C
  module D = Category D
  module E = Category E

_◅_ : ∀ {oC ℓC eC oD ℓD eD oE ℓE eE ℓP eP ℓQ eQ} {C : Category oC ℓC eC} {D : Category oD ℓD eD} {E : Category oE ℓE eE} (P : Profunctor ℓP eP C E) (Q : Profunctor ℓQ eQ C D) → Profunctor (oC ⊔ ℓC ⊔ ℓP ⊔ ℓQ ⊔ eC ⊔ eD ⊔ eE ⊔ eP ⊔ eQ) (oC ⊔ ℓC ⊔ ℓD ⊔ ℓE ⊔ ℓP ⊔ ℓQ ⊔ eC ⊔ eP ⊔ eQ) D E
_◅_ {oC} {ℓC} {eC} {oD} {ℓD} {eD} {oE} {ℓE} {eE} {ℓP} {eP} {ℓQ} {eQ} {C} {D} {E} P Q = pro (record
  { F₀ = λ (e , d) → Category.hom-setoid (Functors C (Setoids _ _)) {LiftSetoids (ℓE ⊔ ℓP) (eE ⊔ eP) ∘F appˡ Q.bimodule d} {LiftSetoids (ℓD ⊔ ℓQ) (eD ⊔ eQ) ∘F appˡ P.bimodule e}
  ; F₁ = λ (ef , df) → record
    { _⟨$⟩_ = λ ϕ → (LiftSetoids (ℓD ⊔ ℓQ) (eD ⊔ eQ) ∘ˡ appˡ-nat P.bimodule ef) ∘ᵥ ϕ ∘ᵥ LiftSetoids (ℓE ⊔ ℓP) (eE ⊔ eP) ∘ˡ appˡ-nat Q.bimodule df
    ; cong = λ {σ τ} σ≈τ {e x y} x≈y → lift (cong (P.₁ˡ ef) (lower (σ≈τ (lift (cong (Q.₁ˡ df) (lower x≈y))))))
    }
  ; identity = λ {(d , c)} {σ τ} σ≈τ {e x y} x≈y → lift (P.identity (lower (σ≈τ (lift (Q.identity (lower x≈y))))))
  ; homomorphism = λ {(eX , dX) (eY , dY) (eZ , dZ) (ef , df) (eg , dg) σ τ} σ≈τ {c x y} x≈y → lift (P.homomorphismˡ (lower (σ≈τ (lift (Q.homomorphismˡ (lower x≈y))))))
  ; F-resp-≈ = λ {(eA , dA) (eB , dB) (ef , df) (eg , dg)} (ef≈eg , df≈dg) {σ τ} σ≈τ {c x y} x≈y → lift (P.resp-≈ˡ ef≈eg (lower (σ≈τ (lift (Q.resp-≈ˡ df≈dg (lower x≈y))))))
  })
  where
  module P = Profunctor P
  module Q = Profunctor Q
  module C = Category C
  module D = Category D
  module E = Category E

module _ {o ℓ e} {o′} (C : Category o ℓ e) (D : Category o′ ℓ e) where
  module C = Category C
  open module D = Category D hiding (id)
  open D.HomReasoning
  open import Categories.Morphism.Reasoning D using (assoc²''; elimˡ; elimʳ)

  -- representable profunctors
  -- hom(f,1)
  repˡ : ∀ (F : Functor C D) → Profunctor ℓ e D C
  repˡ F = pro record
    { F₀ = λ (c , d) → record
      { Carrier = D [ F₀ c , d ]
      ; _≈_ = D._≈_
      ; isEquivalence = D.equiv
      }
    ; F₁ = λ (f , g) → record
      { _⟨$⟩_ = λ x → g ∘ x ∘ F₁ f
      ; cong  = λ x → begin _ ≈⟨ refl⟩∘⟨ x ⟩∘⟨refl ⟩ _ ∎
      }
    ; identity = λ {x} {y} {y'} y≈y' → begin
        D.id ∘ y ∘ F₁ C.id ≈⟨ D.identityˡ ⟩
        y ∘ F₁ C.id        ≈⟨ elimʳ identity ⟩
        y                  ≈⟨ y≈y' ⟩
        y'                 ∎
    ; homomorphism = λ { {f = f0 , f1} {g = g0 , g1} {x} {y} x≈y → begin
        (g1 ∘ f1) ∘ x ∘ F₁ (f0 C.∘ g0)  ≈⟨ refl⟩∘⟨ x≈y ⟩∘⟨ F.homomorphism ⟩
        (g1 ∘ f1) ∘ y ∘ F₁ f0 ∘ F₁ g0   ≈⟨ refl⟩∘⟨ D.sym-assoc ⟩
        (g1 ∘ f1) ∘ (y ∘ F₁ f0) ∘ F₁ g0 ≈⟨ Equiv.sym assoc²'' ⟩
        g1 ∘ (f1 ∘ y ∘ F₁ f0) ∘ F₁ g0   ∎
      }
    ; F-resp-≈ = λ { {f = f0 , f1} {g = g0 , g1} (f0≈g0 , f1≈g1) {x} {y} x≈y → begin
        f1 ∘ x ∘ F₁ f0 ≈⟨ f1≈g1 ⟩∘⟨ x≈y ⟩∘⟨ F-resp-≈ f0≈g0 ⟩
        g1 ∘ y ∘ F₁ g0 ∎
      }
    }
    where
      open module F = Functor F

  -- hom(1,f)
  repʳ : (F : Functor C D) → Profunctor ℓ e C D
  repʳ F = pro record
    { F₀ = λ (c , d) → record
      { Carrier = D [ c , F₀ d ]
      ; _≈_ = D._≈_
      ; isEquivalence = D.equiv
      }
    ; F₁ = λ (f , g) → record
      { _⟨$⟩_ = λ x → F₁ g ∘ x ∘ f
      ; cong  = λ x → begin _ ≈⟨ refl⟩∘⟨ x ⟩∘⟨refl ⟩ _ ∎
      }
    ; identity = λ {x} {y} {y'} y≈y' → begin
        F₁ C.id ∘ y ∘ D.id ≈⟨ elimˡ identity ⟩
        y ∘ D.id           ≈⟨ D.identityʳ ⟩
        y                  ≈⟨ y≈y' ⟩
        y'                 ∎
    ; homomorphism = λ { {f = f0 , f1} {g = g0 , g1} {x} {y} x≈y → begin
        F₁ (g1 C.∘ f1) ∘ x ∘ f0 ∘ g0    ≈⟨ F.homomorphism ⟩∘⟨ x≈y ⟩∘⟨refl ⟩
        (F₁ g1 ∘ F₁ f1) ∘ y ∘ f0 ∘ g0   ≈⟨ refl⟩∘⟨ D.sym-assoc ⟩
        (F₁ g1 ∘ F₁ f1) ∘ (y ∘ f0) ∘ g0 ≈⟨ Equiv.sym assoc²'' ⟩
        F₁ g1 ∘ (F₁ f1 ∘ y ∘ f0) ∘ g0   ∎
      }
    ; F-resp-≈ = λ { {f = f0 , f1} {g = g0 , g1} (f0≈g0 , f1≈g1) {x} {y} x≈y → begin
        F₁ f1 ∘ x ∘ f0 ≈⟨ F-resp-≈ f1≈g1 ⟩∘⟨ x≈y ⟩∘⟨ f0≈g0 ⟩
        F₁ g1 ∘ y ∘ g0 ∎
      }
    }
    where
      open module F = Functor F

-- each Prof(C,D) is a category
homProf : {o o′ ℓ e : Level} → (C : Category o ℓ e) → (D : Category o′ ℓ e) → Category _ _ _
homProf {ℓ = ℓ} {e} C D = record
  { Obj = Profunctor ℓ e C D
  ; _⇒_ = λ P Q → NaturalTransformation (Profunctor.bimodule P) (Profunctor.bimodule Q)
  ; _≈_ = _≃_
  ; id = id
  ; _∘_ = _∘ᵥ_
  ; assoc     = λ { {f = f} {g} {h} → assoc-lemma {f = f} {g} {h}}
  ; sym-assoc = λ { {f = f} {g} {h} → sym-assoc-lemma {f = f} {g} {h}}
  ; identityˡ = λ { {f = f} → id-lemmaˡ {f = f} }
  ; identityʳ = λ { {f = f} → id-lemmaʳ {f = f} }
  ; identity² = λ z → z
  ; equiv = ≃-isEquivalence
  ; ∘-resp-≈ = λ { {f = f} {h} {g} {i} eq eq' → ∘ᵥ-resp-≃ {f = f} {h} {g} {i} eq eq' }
  }
  where
    id-lemmaˡ : ∀ {o o′ ℓ ℓ′ e e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {P K : Functor C D}
            {f : NaturalTransformation P K} → id ∘ᵥ f ≃ f
    id-lemmaˡ {D = D} = Category.identityˡ D

    id-lemmaʳ : ∀ {o o′ ℓ ℓ′ e e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {P K : Functor C D}
            {f : NaturalTransformation P K} → f ∘ᵥ id ≃ f
    id-lemmaʳ {D = D} = Category.identityʳ D

    assoc-lemma : ∀ {o o′ ℓ ℓ′ e e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {E F G H : Functor C D}
              {f : NaturalTransformation E F}
              {g : NaturalTransformation F G}
              {h : NaturalTransformation G H}
               → (h ∘ᵥ g) ∘ᵥ f ≃ h ∘ᵥ g ∘ᵥ f
    assoc-lemma {D = D} = Category.assoc D

    sym-assoc-lemma : ∀ {o o′ ℓ ℓ′ e e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {E F G H : Functor C D}
              {f : NaturalTransformation E F}
              {g : NaturalTransformation F G}
              {h : NaturalTransformation G H}
               → h ∘ᵥ g ∘ᵥ f ≃ (h ∘ᵥ g) ∘ᵥ f
    sym-assoc-lemma {D = D} = Category.sym-assoc D

    ∘ᵥ-resp-≃ : ∀ {o o′ ℓ ℓ′ e e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {R P K : Functor C D}
        {f h : NaturalTransformation P K}
        {g i : NaturalTransformation R P} → f ≃ h → g ≃ i → f ∘ᵥ g ≃ h ∘ᵥ i
    ∘ᵥ-resp-≃ {D = D} fh gi = Category.∘-resp-≈ D fh gi
