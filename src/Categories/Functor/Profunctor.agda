{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Profunctor where

open import Level
open import Data.Product using (_,_; _×_)
open import Function using () -- renaming (_∘′_ to _∙_)
open import Function.Bundles using (_⟨$⟩_; Func)
open Func using (cong)
open import Relation.Binary using (Setoid; module Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidR

open import Categories.Category
open import Categories.Category.Construction.Functors using (Functors)
open import Categories.Category.Instance.Cats using (Cats)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor hiding (id)
open import Categories.Functor.Bifunctor using (Bifunctor; appˡ; appʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.Functor.Construction.LiftSetoids using (LiftSetoids)
open import Categories.Functor.Hom using (Hom[_][-,-])
open import Categories.Functor.Instance.ConnectedComponents using (Π₀)
open import Categories.Functor.Profunctor.FormalComposite
open import Categories.Morphism.Reasoning using (id-comm; id-comm-sym)
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ᵥ_; _∘ˡ_; id)
open import Categories.NaturalTransformation.Equivalence using (_≃_; ≃-isEquivalence)
open import Categories.NaturalTransformation.Properties using (appˡ-nat; appʳ-nat)

open Setoid renaming (_≈_ to _[[_≈_]])

record Profunctor {o ℓ e} {o′ ℓ′ e′} ℓ″ e″
         (C : Category o ℓ e) (D : Category o′ ℓ′ e′)
         : Set (o ⊔ o′ ⊔ suc (ℓ ⊔ ℓ′ ⊔ ℓ″ ⊔ e ⊔ e′ ⊔ e″)) where
  constructor pro
  field
    bimodule : Bifunctor (Category.op D) C (Setoids ℓ″ e″)
  open Bifunctor bimodule public

  dom : Category o ℓ e
  dom = C

  cod : Category o′ ℓ′ e′
  cod = D

private variable
  o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ o‴ ℓ‴ e‴ ℓP eP ℓQ eQ : Level
  C D E : Category o ℓ e
  P Q : Profunctor ℓ e C D
  
-- Calling the profunctor identity "id" is a bad idea
proid : ∀ {o ℓ e} → {C : Category o ℓ e} → Profunctor _ _ C C
proid {C = C} = pro (Hom[ C ][-,-])

_ⓟ′_ : ∀ {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {E : Category o″ ℓ″ e″}
         (P : Profunctor ℓP eP D E) (Q : Profunctor ℓQ eQ C D) →
         Bifunctor (Category.op E) C (Cats _ _ _)
_ⓟ′_ {C = C} {D} {E} P Q = record
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

  my-F₀ : (E.Obj × C.Obj) → Category _ _ _
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
  my-identity : ∀ {c e} →
    Cats _ _ _ [ my-F₁ (E.id {e} , C.id {c}) ≈ Category.id (Cats _ _ _) ]
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
  my-homomorphism : ∀ {cX cY cZ eX eY eZ}
    (cf : C [ cX , cY ]) (ef : E [ eY , eX ])
    (cg : C [ cY , cZ ]) (eg : E [ eZ , eY ])
    → Cats _ _ _ [ my-F₁ (E [ ef ∘ eg ] , C [ cg ∘ cf ]) ≈ Cats _ _ _ [ my-F₁ (eg , cg) ∘ my-F₁ (ef , cf) ] ]
  my-homomorphism {cX} {cY} {cZ} {eX} {eY} {eZ} cf ef cg eg = record
    { F⇒G = record
      { η = λ X → record
        { twiner = D.id
        ; in-tertwines = let open SetoidR (P.₀ (eZ , rendezvous X)) in
          begin
            P.₁ˡ eg ⟨$⟩ (P.₁ˡ ef ⟨$⟩ in-side X)
          ≈˘⟨ P.homomorphismˡ (Setoid.refl (P.₀ _)) ⟩
            P.₁ˡ (P.cod [ ef ∘ eg ]) ⟨$⟩ in-side X
          ≈˘⟨ P.identity (Setoid.refl (P.₀ _)) ⟩
            P.₁ʳ D.id ⟨$⟩ (P.₁ˡ (P.cod [ ef ∘ eg ]) ⟨$⟩ in-side X)
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
  my-resp : ∀ {cA cB eA eB}
    {cf cg : C [ cA , cB ]} {ef eg : E [ eB , eA ]}
    → C [ cf ≈ cg ] → E [ ef ≈ eg ]
    → Cats _ _ _ [ my-F₁ (ef , cf) ≈ my-F₁ (eg , cg) ]
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

_ⓟ_ : (P : Profunctor ℓ e D E) (Q : Profunctor ℓ′ e′ C D) → Profunctor _ _ C E
_ⓟ_ P Q = pro (Π₀ ∘F (P ⓟ′ Q))

-- formulas from https://ncatlab.org/nlab/show/2-category+equipped+with+proarrows#limits
-- XXX actually prove these are adjoints to composition

_▻_ : ∀ {oC ℓC eC oD ℓD eD oE ℓE eE ℓP eP ℓQ eQ}
  {C : Category oC ℓC eC} {D : Category oD ℓD eD} {E : Category oE ℓE eE}
  (P : Profunctor ℓP eP D E) (Q : Profunctor ℓQ eQ C E) → Profunctor _ _ C D
_▻_ {oC} {ℓC} {eC} {oD} {ℓD} {eD} {oE} {ℓE} {eE} {ℓP} {eP} {ℓQ} {eQ} {C} {D} {E} P Q = pro (record
  { F₀ = λ (d , c) → Category.hom-setoid (Functors E.op (Setoids _ _))
      {LiftSetoids (ℓC ⊔ ℓQ) (eC ⊔ eQ) ∘F appʳ P.bimodule d}
      {LiftSetoids (ℓC ⊔ ℓP) (eC ⊔ eP) ∘F appʳ Q.bimodule c}
  ; F₁ = λ (df , cf) → record
    { to = λ ϕ →
        (LiftSetoids (ℓC ⊔ ℓP) (eC ⊔ eP) ∘ˡ appʳ-nat Q.bimodule cf)
        ∘ᵥ ϕ
        ∘ᵥ (LiftSetoids (ℓC ⊔ ℓQ) (eC ⊔ eQ) ∘ˡ appʳ-nat P.bimodule df)
    ; cong = λ {σ τ} σ≈τ {e x y} x≈y →
        lift (cong (Q.₁ʳ cf) (lower (σ≈τ (lift (cong (P.₁ʳ df) (lower x≈y))))))
    }
  ; identity = λ {(d , c)} {σ τ} σ≈τ {e x y} x≈y →
      lift (Q.identity (lower (σ≈τ (lift (P.identity (lower x≈y))))))
  ; homomorphism = λ {(dX , cX) (dY , cY) (dZ , cZ) (df , cf) (dg , cg) σ τ} σ≈τ {e x y} x≈y →
      lift (Q.homomorphismʳ (lower (σ≈τ (lift (P.homomorphismʳ (lower x≈y))))))
  ; F-resp-≈ = λ {(dA , cA) (dB , cB) (df , cf) (dg , cg)} (df≈dg , cf≈cg) {σ τ} σ≈τ {e x y} x≈y →
      lift (Q.resp-≈ʳ cf≈cg (lower (σ≈τ (lift (P.resp-≈ʳ df≈dg (lower x≈y))))))
  })
  where
  module P = Profunctor P
  module Q = Profunctor Q
  module C = Category C
  module D = Category D
  module E = Category E

_◅_ : ∀ {oC ℓC eC oD ℓD eD oE ℓE eE ℓP eP ℓQ eQ}
  {C : Category oC ℓC eC} {D : Category oD ℓD eD} {E : Category oE ℓE eE}
  (P : Profunctor ℓP eP C E) (Q : Profunctor ℓQ eQ C D) → Profunctor _ _ D E
_◅_ {oC} {ℓC} {eC} {oD} {ℓD} {eD} {oE} {ℓE} {eE} {ℓP} {eP} {ℓQ} {eQ} {C} {D} {E} P Q = pro (record
  { F₀ = λ (e , d) → Category.hom-setoid (Functors C (Setoids _ _))
      {LiftSetoids (ℓE ⊔ ℓP) (eE ⊔ eP) ∘F appˡ Q.bimodule d}
      {LiftSetoids (ℓE ⊔ ℓQ) (eE ⊔ eQ) ∘F appˡ P.bimodule e}
  ; F₁ = λ (ef , df) → record
    { to = λ ϕ →
        (LiftSetoids (ℓE ⊔ ℓQ) (eE ⊔ eQ) ∘ˡ appˡ-nat P.bimodule ef)
        ∘ᵥ ϕ
        ∘ᵥ (LiftSetoids (ℓE ⊔ ℓP) (eE ⊔ eP) ∘ˡ appˡ-nat Q.bimodule df)
    ; cong = λ {σ τ} σ≈τ {e x y} x≈y →
        lift (cong (P.₁ˡ ef) (lower (σ≈τ (lift (cong (Q.₁ˡ df) (lower x≈y))))))
    }
  ; identity = λ {(d , c)} {σ τ} σ≈τ {e x y} x≈y →
      lift (P.identity (lower (σ≈τ (lift (Q.identity (lower x≈y))))))
  ; homomorphism = λ {(eX , dX) (eY , dY) (eZ , dZ) (ef , df) (eg , dg) σ τ} σ≈τ {c x y} x≈y →
      lift (P.homomorphismˡ (lower (σ≈τ (lift (Q.homomorphismˡ (lower x≈y))))))
  ; F-resp-≈ = λ {(eA , dA) (eB , dB) (ef , df) (eg , dg)} (ef≈eg , df≈dg) {σ τ} σ≈τ {c x y} x≈y →
      lift (P.resp-≈ˡ ef≈eg (lower (σ≈τ (lift (Q.resp-≈ˡ df≈dg (lower x≈y))))))
  })
  where
  module P = Profunctor P
  module Q = Profunctor Q
  module C = Category C
  module D = Category D
  module E = Category E

module _ {o ℓ e} {o′} (C : Category o ℓ e) (D : Category o′ ℓ e) where
  private
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
      { to = λ x → g ∘ x ∘ F₁ f
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
      { to = λ x → F₁ g ∘ x ∘ f
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
