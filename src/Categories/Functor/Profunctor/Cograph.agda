{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Profunctor.Cograph where

open import Level
open import Data.Empty.Polymorphic using (⊥)
open import Data.Product using (_,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (Func; _⟨$⟩_)
open Func using (cong)
open import Relation.Binary using (Setoid; module Setoid)

open import Categories.Category
open import Categories.Functor hiding (id)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.Functor.Profunctor

module _ {o ℓ e o′ ℓ′ e′ ℓ″ e″}
    {C : Category o ℓ e} {D : Category o′ ℓ′ e′} (P : Profunctor ℓ″ e″ C D)
    where
  open Profunctor P

  cograph : Category _ _ _
  cograph = record
    { Obj = D.Obj ⊎ C.Obj
    ; _⇒_ = λ
      { (inj₁ d) (inj₁ d′) → Lift (ℓ ⊔ ℓ″) (D [ d , d′ ])
      ; (inj₁ d) (inj₂ c) → Lift (ℓ ⊔ ℓ′) (Setoid.Carrier (F₀ (d , c)))
      ; (inj₂ c) (inj₁ d) → ⊥
      ; (inj₂ c) (inj₂ c′) → Lift (ℓ′ ⊔ ℓ″) (C [ c , c′ ])
      }
    ; _≈_ = λ
      { {inj₁ d} {inj₁ d′} f g → Lift (e ⊔ e″) (D [ lower f ≈ lower g ])
      ; {inj₁ d} {inj₂ c} p q → Lift (e ⊔ e′) (Setoid._≈_ (F₀ (d , c)) (lower p) (lower q))
      ; {inj₂ c} {inj₁ d} () ()
      ; {inj₂ c} {inj₂ c′} f g → Lift (e′ ⊔ e″) (C [ lower f ≈ lower g ])
      }
    ; id = λ
      { {inj₁ d} → lift D.id
      ; {inj₂ c} → lift C.id
      }
    ; _∘_ = λ
      { {inj₁ dA} {inj₁ dB} {inj₁ dC} f g → lift (D [ lower f ∘ lower g ])
      ; {inj₁ dA} {inj₁ dB} {inj₂ cC} p g → lift (₁ˡ (lower g) ⟨$⟩ lower p)
      ; {inj₁ dA} {inj₂ cB} {inj₂ cC} f q → lift (₁ʳ (lower f) ⟨$⟩ lower q)
      ; {inj₂ cA} {inj₂ cB} {inj₂ cC} f g → lift (C [ lower f ∘ lower g ])
      }
    ; assoc = λ
      { {inj₁ dA} {inj₁ dB} {inj₁ dC} {inj₁ dD} {f} {g} {h} → lift D.assoc
      ; {inj₁ dA} {inj₁ dB} {inj₁ dC} {inj₂ cD} {f} {g} {r} →
          lift (Setoid.sym (F₀ _) (homomorphismˡ (Setoid.refl (F₀ _))))
      ; {inj₁ dA} {inj₁ dB} {inj₂ cC} {inj₂ cD} {f} {q} {h} →
          lift (Setoid.sym (F₀ _) ([ bimodule ]-commute (Setoid.refl (F₀ _))))
      ; {inj₁ dA} {inj₂ cB} {inj₂ cC} {inj₂ cD} {p} {g} {h} →
          lift (homomorphismʳ (Setoid.refl (F₀ _)))
      ; {inj₂ cA} {inj₂ cB} {inj₂ cC} {inj₂ cD} {f} {g} {h} → lift C.assoc
      }
    ; sym-assoc = λ
      { {inj₁ dA} {inj₁ dB} {inj₁ dC} {inj₁ dD} {f} {g} {h} → lift D.sym-assoc
      ; {inj₁ dA} {inj₁ dB} {inj₁ dC} {inj₂ cD} {f} {g} {r} →
          lift (homomorphismˡ (Setoid.refl (F₀ _)))
      ; {inj₁ dA} {inj₁ dB} {inj₂ cC} {inj₂ cD} {f} {q} {h} →
          lift ([ bimodule ]-commute (Setoid.refl (F₀ _)))
      ; {inj₁ dA} {inj₂ cB} {inj₂ cC} {inj₂ cD} {p} {g} {h} →
          lift (Setoid.sym (F₀ _) (homomorphismʳ (Setoid.refl (F₀ _))))
      ; {inj₂ cA} {inj₂ cB} {inj₂ cC} {inj₂ cD} {f} {g} {h} → lift C.sym-assoc
      }
    ; identityˡ = λ
      { {inj₁ dA} {inj₁ dB} {f} → lift D.identityˡ
      ; {inj₁ dA} {inj₂ cB} {p} → lift (identity (Setoid.refl (F₀ _)))
      ; {inj₂ cA} {inj₂ cB} {f} → lift C.identityˡ
      }
    ; identityʳ = λ
      { {inj₁ dA} {inj₁ dB} {f} → lift D.identityʳ
      ; {inj₁ dA} {inj₂ cB} {p} → lift (identity (Setoid.refl (F₀ _)))
      ; {inj₂ cA} {inj₂ cB} {f} → lift C.identityʳ
      }
    ; identity² = λ
      { {inj₁ d} → lift D.identity²
      ; {inj₂ c} → lift C.identity²
      }
    ; equiv = λ
      { {inj₁ dA} {inj₁ dB} → record
          { refl = lift D.Equiv.refl
          ; sym = λ x → lift (D.Equiv.sym (lower x))
          ; trans = λ x y → lift (D.Equiv.trans (lower x) (lower y))
          }
      ; {inj₁ dA} {inj₂ cB} → record
          { refl = lift (Setoid.refl (F₀ _))
          ; sym = λ x → lift (Setoid.sym (F₀ _) (lower x))
          ; trans = λ x y → lift (Setoid.trans (F₀ _) (lower x) (lower y))
          }
      ; {inj₂ cA} {inj₁ dB} → record
          { refl = λ {}
          ; sym = λ {}
          ; trans = λ {}
          }
      ; {inj₂ cA} {inj₂ cB} → record
          { refl = lift C.Equiv.refl
          ; sym = λ x → lift (C.Equiv.sym (lower x))
          ; trans = λ x y → lift (C.Equiv.trans (lower x) (lower y))
          }
      }
    ; ∘-resp-≈ = λ
      { {inj₁ dA} {inj₁ dB} {inj₁ dC} {f} {h} {g} {i} →
          λ x y → lift (D.∘-resp-≈ (lower x) (lower y))
      ; {inj₁ dA} {inj₁ dB} {inj₂ cC} {f} {h} {g} {i} →
          λ f≈h g≈i → lift (resp-≈ˡ (lower g≈i) (lower f≈h))
      ; {inj₁ dA} {inj₂ cB} {inj₂ cC} {f} {h} {g} {i} →
          λ f≈h g≈i → lift (resp-≈ʳ (lower f≈h) (lower g≈i))
      ; {inj₂ cA} {inj₂ cB} {inj₂ cC} {f} {h} {g} {i} →
          λ x y → lift (C.∘-resp-≈ (lower x) (lower y))
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
