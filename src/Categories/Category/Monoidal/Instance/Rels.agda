{-# OPTIONS --without-K --safe #-}
module Categories.Category.Monoidal.Instance.Rels where

-- The category of relations is cartesian and (by self-duality) co-cartesian.
-- Perhaps slightly counter-intuitively if you're used to categories which act
-- like Sets, the product acts on objects as the disjoint union.
-- It also exhibits another monoidality, based on cartesian products of sets,
-- which is symmetric and closed.

open import Data.Empty.Polymorphic using (⊥; ⊥-elim)
import Data.Product as ×
open × using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit.Polymorphic using (⊤)
open import Function using (case_of_; flip)
open import Level using (Lift; lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Cartesian.Monoidal using (module CartesianMonoidal)
open import Categories.Category.Core using (Category)
open import Categories.Category.Cocartesian using (Cocartesian)
open import Categories.Category.Instance.Rels using (Rels)
open import Categories.Category.Monoidal using (Monoidal; monoidalHelper)
open import Categories.Category.Monoidal.Symmetric using (Symmetric; symmetricHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)

module _ {o ℓ} where

  Rels-Cartesian : Cartesian (Rels o ℓ)
  Rels-Cartesian = record
    { terminal = record
      { ⊤ = ⊥
      ; ⊤-is-terminal = record
        { ! = λ { _ (lift ()) }
        ; !-unique = λ _ → (λ { {_} {lift ()} }) , (λ { {_} {lift ()} })
        }
      }
    ; products = record
      { product = λ {A} {B} → record
        { A×B = A ⊎ B
        ; π₁ = [ (λ x y → Lift ℓ (x ≡ y) ) , (λ _ _ → ⊥) ]′
        ; π₂ = [ (λ _ _ → ⊥) , (λ x y → Lift ℓ (x ≡ y)) ]′
        ; ⟨_,_⟩ = λ L R c → [ L c , R c ]′
        ; project₁ = (λ { (inj₁ x , r , lift refl) → r})
          , λ r → inj₁ _ , r , lift refl
        ; project₂ = (λ { (inj₂ _ , r , lift refl) → r })
          , (λ r → inj₂ _ , r , lift refl)
        ; unique =
            λ { (p , q) (p′ , q′) → (λ { {_} {inj₁ a} r → case (q {_} {a} r) of λ { (inj₁ .a , s , lift refl) → s}
                                       ; {_} {inj₂ b} r → case (q′ {_} {b} r) of λ { (inj₂ .b , s , lift refl) → s} })
                                   , λ { {_} {inj₁ a} hxa → p (inj₁ a , hxa , lift refl)
                                       ; {_} {inj₂ b} hxb → p′ (inj₂ b , hxb , lift refl) } }
        }
      }
    }

  -- because Rels is dual to itself, the proof that it is cocartesian resembles the proof that it's cartesian
  -- Rels is not self-dual 'on the nose', so we can't use duality proper.
  Rels-Cocartesian : Cocartesian (Rels o ℓ)
  Rels-Cocartesian = record
    { initial = record
      { ⊥ = ⊥
      ; ⊥-is-initial = record
        { ! = λ ()
        ; !-unique = λ _ → (λ { {()} }) , (λ { {()} })
        }
      }
    ; coproducts = record
      { coproduct = λ {A} {B} → record
        { A+B = A ⊎ B
        ; i₁ = λ a → [ (λ a′ → Lift ℓ (a ≡ a′)) , (λ _ → ⊥) ]′
        ; i₂ = λ b → [ (λ _ → ⊥) , (λ b′ → Lift ℓ (b ≡ b′)) ]′
        ; [_,_] = λ L R a+b c → [ flip L c , flip R c ]′ a+b
        ; inject₁ = (λ { (inj₁ x , lift refl , fxy) → fxy})
          , λ r → inj₁ _ , lift refl , r
        ; inject₂ = (λ { (inj₂ _ , lift refl , r) → r })
          , (λ r → inj₂ _ , lift refl , r)
        ; unique = λ { (p , q) (p′ , q′) → (λ { {inj₁ a} r → case (q {a} r) of λ { (inj₁ .a , lift refl , s) → s}
                                              ; {inj₂ b} r → case (q′ {b} r) of λ { (inj₂ .b , lift refl , s) → s} })
                                          , λ { {inj₁ a} hxa → p (inj₁ a , lift refl , hxa)
                                              ; {inj₂ b} hxb → p′ (inj₂ b , lift refl , hxb) } }
        }
      }
    }

  Rels-Monoidal : Monoidal (Rels o ℓ)
  Rels-Monoidal = monoidalHelper _ record
    { ⊗ = record
      { F₀ = λ { (A , B) → A ×.× B }
      ; F₁ = λ {(R , S) (a , b) (c , d) → R a c ×.× S b d}
      ; identity = record
        { fst = λ { (lift refl , lift refl) → lift refl }
        ; snd = λ { (lift refl) → lift refl , lift refl }
        }
      ; homomorphism = record
        { fst = λ { ((b , aRb , bTc) , (y , xSy , yUz)) → (b , y) , (aRb , xSy) , (bTc , yUz) }
        ; snd = λ { ((b , y) , (aRb , xSy) , (bTc , yUz)) → (b , aRb , bTc) , (y , xSy , yUz) }
        }
      ; F-resp-≈ = λ
        { ((R⇒T , T⇒R) , (S⇒U , U⇒S)) → record
          { fst = λ { (aRb , xSy) → R⇒T aRb , S⇒U xSy  }
          ; snd = λ { (aTb , xUy) → T⇒R aTb , U⇒S xUy }
          }
        }
      }
    ; unit = ⊤
    ; unitorˡ = record
      { from = λ { (_ , x) y → Lift ℓ (x ≡ y) }
      ; to   = λ { x (_ , y) → Lift ℓ (x ≡ y) }
      ; iso = record
        { isoˡ = record
          { fst = λ { (_ , (lift refl , lift refl)) → lift refl }
          ; snd = λ { (lift refl) → _ , (lift refl , lift refl) }
          }
        ; isoʳ = record
          { fst = λ { (_ , (lift refl , lift refl)) → lift refl }
          ; snd = λ { (lift refl) → (_ , (lift refl , lift refl)) }
          }
        }
      }
    ; unitorʳ = record
      { from = λ { (x , _) y → Lift ℓ (x ≡ y) }
      ; to   = λ { x (y , _) → Lift ℓ (x ≡ y) }
      ; iso = record
        { isoˡ = record
          { fst = λ { (_ , (lift refl , lift refl)) → lift refl }
          ; snd = λ { (lift refl) → _ , (lift refl , lift refl) }
          }
        ; isoʳ = record
          { fst = λ { (_ , (lift refl , lift refl)) → lift refl }
          ; snd = λ { (lift refl) → _ , (lift refl , lift refl) }
          }
        }
      }
    ; associator = record
      { from = λ { ((x₁ , y₁) , z₁) (x₂ , (y₂ , z₂)) → Lift ℓ (x₁ ≡ x₂) ×.× Lift ℓ (y₁ ≡ y₂) ×.× Lift ℓ (z₁ ≡ z₂) }
      ; to   = λ { (x₁ , (y₁ , z₁)) ((x₂ , y₂) , z₂) → Lift ℓ (x₁ ≡ x₂) ×.× Lift ℓ (y₁ ≡ y₂) ×.× Lift ℓ (z₁ ≡ z₂) }
      ; iso = record
        { isoˡ = record
          { fst = λ { (_ , ((lift refl , lift refl , lift refl) , (lift refl , lift refl , lift refl))) → lift refl }
          ; snd = λ { (lift refl) → _ , ((lift refl , lift refl , lift refl) , (lift refl , lift refl , lift refl)) }
          }
        ; isoʳ = record
          { fst = λ { (_ , ((lift refl , lift refl , lift refl) , (lift refl , lift refl , lift refl))) → lift refl }
          ; snd = λ { (lift refl) → _ , ((lift refl , lift refl , lift refl) , (lift refl , lift refl , lift refl)) }
          }
        }
      }
    ; unitorˡ-commute = record
      { fst = λ { (_ , ((lift refl , x) , lift refl)) → _ , (lift refl , x) }
      ; snd = λ { (_ , (lift refl , x)) → _ , ((lift refl , x) , lift refl) }
      }
    ; unitorʳ-commute = record
      { fst = λ { (_ , ((x , lift refl) , lift refl)) →  _ , (lift refl , x) }
      ; snd = λ { (_ , (lift refl , x)) → _ , ((x , lift refl) , lift refl) }
      }
    ; assoc-commute = record
      { fst = λ { (_ , ((a , b) , c) , (lift refl , lift refl , lift refl)) → _ , (lift refl , lift refl , lift refl) , (a , (b , c)) }
      ; snd = λ { (_ , (lift refl , lift refl , lift refl) , (a , (b , c))) → _ , ((a , b) , c) , (lift refl , lift refl , lift refl) }
      }
    ; triangle = record
      { fst = λ { (_ , ((lift refl , lift refl , lift refl) , (lift refl , lift refl))) → lift refl , lift refl }
      ; snd = λ { (lift refl , lift refl) → _ , ((lift refl , lift refl , lift refl) , (lift refl , lift refl)) }
      }
    ; pentagon = record
      { fst = λ { (_ , ((_ , (((lift refl , lift refl , lift refl) , lift refl) , (lift refl , lift refl , lift refl))) , (lift refl , (lift refl , lift refl , lift refl)))) → _ , (lift refl , lift refl , lift refl) , (lift refl , lift refl , lift refl) }
      ; snd = λ { (_ , (lift refl , lift refl , lift refl) , (lift refl , lift refl , lift refl)) → _ , ((_ , (((lift refl , lift refl , lift refl) , lift refl) , (lift refl , lift refl , lift refl))) , (lift refl , (lift refl , lift refl , lift refl))) }
      }
    }

  Rels-Symmetric : Symmetric Rels-Monoidal
  Rels-Symmetric = symmetricHelper _ record
    { braiding = niHelper record
      { η =   λ { (X , Y) (x₁ , y₁) (y₂ , x₂) → Lift ℓ (x₁ ≡ x₂) ×.× Lift ℓ (y₁ ≡ y₂) }
      ; η⁻¹ = λ { (X , Y) (y₁ , x₁) (x₂ , y₂) → Lift ℓ (x₁ ≡ x₂) ×.× Lift ℓ (y₁ ≡ y₂) }
      ; commute = λ
        { (R , S) → record
          { fst = λ { (_ , (r , s) , (lift refl , lift refl)) → _ , (lift refl , lift refl) , (s , r) }
          ; snd = λ { (_ , (lift refl , lift refl) , (s , r)) → _ , (r , s) , (lift refl , lift refl) }
          }
        }
      ; iso = λ
        { (X , Y) → record
          { isoˡ = record
            { fst = λ { (_ , (lift refl , lift refl) , (lift refl , lift refl)) → lift refl }
            ; snd = λ { (lift refl) → _ , (lift refl , lift refl) , (lift refl , lift refl) }
            }
          ; isoʳ = record
            { fst = λ { (_ , (lift refl , lift refl) , (lift refl , lift refl)) → lift refl }
            ; snd = λ { (lift refl) → _ , (lift refl , lift refl) , (lift refl , lift refl) }
            }
          }
        }
      }
    ; commutative = record
      { fst = λ { (_ , (lift refl , lift refl) , (lift refl , lift refl)) → lift refl }
      ; snd = λ { (lift refl) → _ , (lift refl , lift refl) , (lift refl , lift refl) }
      }
    ; hexagon = record
      { fst = λ { (_ , (_ , ((lift refl , lift refl) , lift refl) , (lift refl , (lift refl , lift refl))) , (lift refl , lift refl , lift refl)) → _ , (_ , (lift refl , lift refl , lift refl) , (lift refl , lift refl)) , lift refl , lift refl , lift refl }
      ; snd = λ { (_ , (_ , (lift refl , lift refl , lift refl) , lift refl , lift refl) , lift refl , lift refl , lift refl) → _ , (_ , ((lift refl , lift refl) , lift refl) , lift refl , lift refl , lift refl) , lift refl , lift refl , lift refl }
      }
    }
