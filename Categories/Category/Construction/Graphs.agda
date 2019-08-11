{-# OPTIONS --without-K --safe #-}

module Categories.Category.Construction.Graphs where

open import Level
open import Function using (_$_) renaming (id to idFun)
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties hiding (trans)

open import Categories.Category
open import Categories.Utils.EqReasoning

-- a graph has vertices Obj and edges _⇒_, where edges form a setoid over _≈_.
record Graph o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  infix 4 _≈_ _⇒_

  field
    Obj   : Set o
    _⇒_   : Rel Obj ℓ
    _≈_   : ∀ {A B} → Rel (A ⇒ B) e
    equiv : ∀ {A B} → IsEquivalence (_≈_ {A} {B})

private
  variable
    o o′ ℓ ℓ′ e e′ : Level

-- TODO: move this to stdlib
module _ {i t} {I : Set i} {T : Rel I t} where

  ◅◅-identityʳ : ∀ {i j} → (xs : Star T i j) → xs ◅◅ ε ≡ xs
  ◅◅-identityʳ ε        = ≡.refl
  ◅◅-identityʳ (x ◅ xs) = ≡.cong (x ◅_) (◅◅-identityʳ xs)

module _ (G : Graph o ℓ e) where
  open Graph G
  private
    module equiv {A B} = IsEquivalence (equiv {A} {B})

  data [_]_≈*_ : ∀ {A B} → Star _⇒_ A B → Star _⇒_ A B → Set (o ⊔ ℓ ⊔ e) where
    ε : ∀ {A} →  [_]_≈*_ (ε {x = A}) ε
    _◅_ : ∀ {A B C} {f g : A ⇒ B} {h i : Star _⇒_ B C} → f ≈ g → [_]_≈*_ h i → [_]_≈*_ (f ◅ h) (g ◅ i)

  refl : ∀ {A B} → Reflexive ([_]_≈*_ {A} {B})
  refl {_} {_} {ε}        = ε
  refl {A} {B} {eq ◅ eq′} = equiv.refl ◅ refl

  sym : ∀ {A B} → Symmetric ([_]_≈*_ {A} {B})
  sym ε          = ε
  sym (eq ◅ eq′) = equiv.sym eq ◅ sym eq′

  trans : ∀ {A B} → Transitive ([_]_≈*_ {A} {B})
  trans ε ε                    = ε
  trans (eq₁ ◅ eq₂) (eq ◅ eq′) = (equiv.trans eq₁ eq) ◅ (trans eq₂ eq′)

  isEquivalence : ∀ {A B} → IsEquivalence ([_]_≈*_ {A} {B})
  isEquivalence = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }

  private
    _≈*_ = [_]_≈*_

  Free : Category o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)
  Free = record
    { Obj       = Obj
    ; _⇒_       = Star _⇒_
    ; _≈_       = _≈*_
    ; id        = ε
    ; _∘_       = _▻▻_
    ; assoc     = λ {_ _ _ _} {f g h} →
      ≡.subst (λ x → x ≈* ((f ◅◅ g) ◅◅ h)) (◅◅-assoc f g h) refl
    ; identityˡ = λ {_ _ f} → ≡.subst ((f ◅◅ ε) ≈*_) (◅◅-identityʳ f) refl
    ; identityʳ = refl
    ; equiv     = isEquivalence
    ; ∘-resp-≈  = resp
    }
    where resp : ∀ {A B C} {f h : Star _⇒_ B C} {g i : Star _⇒_ A B} →
                   f ≈* h → g ≈* i → (f ▻▻ g) ≈* (h ▻▻ i)
          resp eq ε = eq
          resp eq (eq₁ ◅ eq₂) = eq₁ ◅ (resp eq eq₂)

record GraphMorphism (G : Graph o ℓ e) (G′ : Graph o′ ℓ′ e′) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private
    module G  = Graph G
    module G′ = Graph G′

  field
    M₀       : G.Obj → G′.Obj
    M₁       : ∀ {A B} → A G.⇒ B → M₀ A G′.⇒ M₀ B
    M-resp-≈ : ∀ {A B} {f g : A G.⇒ B} → f G.≈ g → M₁ f G′.≈ M₁ g

record GraphMorphism≈ {G : Graph o ℓ e} {G′ : Graph o′ ℓ′ e′}
                      (M M′ : GraphMorphism G G′) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private
    module G  = Graph G
    module G′ = Graph G′
    module M  = GraphMorphism M
    module M′ = GraphMorphism M′

  field
    M₀≡ : ∀ {X} → M.M₀ X ≡ M′.M₀ X
    M₁≡ : ∀ {A B} {f : A G.⇒ B} → ≡.subst₂ G′._⇒_ M₀≡ M₀≡ (M.M₁ f) ≡ M′.M₁ f

Graphs : ∀ o ℓ e → Category (suc (o ⊔ ℓ ⊔ e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
Graphs o ℓ e = record
  { Obj       = Graph o ℓ e
  ; _⇒_       = GraphMorphism
  ; _≈_       = GraphMorphism≈
  ; id        = record
    { M₀       = idFun
    ; M₁       = idFun
    ; M-resp-≈ = idFun
    }
  ; _∘_       = _∘_
  ; assoc     = record
    { M₀≡ = ≡.refl
    ; M₁≡ = ≡.refl
    }
  ; identityˡ = record
    { M₀≡ = ≡.refl
    ; M₁≡ = ≡.refl
    }
  ; identityʳ = record
    { M₀≡ = ≡.refl
    ; M₁≡ = ≡.refl
    }
  ; equiv     = λ {A B} → record
    { refl  = λ {eq} → record
      { M₀≡ = ≡.refl
      ; M₁≡ = ≡.refl
      }
    ; sym   = λ {i j} eq → record
      { M₀≡ = ≡.sym (M₀≡ eq)
      ; M₁≡ = λ {_ _ f} → begin
        ≡.subst₂ (Graph._⇒_ B) (≡.sym (M₀≡ eq)) (≡.sym (M₀≡ eq)) (M₁ j f)
          ≈˘⟨ ≡.cong (≡.subst₂ (Graph._⇒_ B) (≡.sym (M₀≡ eq)) (≡.sym (M₀≡ eq))) (M₁≡ eq) ⟩
        ≡.subst₂ (Graph._⇒_ B) (≡.sym (M₀≡ eq)) (≡.sym (M₀≡ eq))
          (≡.subst₂ (Graph._⇒_ B) (M₀≡ eq) (M₀≡ eq) (M₁ i f))
          ≈⟨ subst₂-sym-subst₂ (Graph._⇒_ B) {M₁ i f} (M₀≡ eq) (M₀≡ eq) ⟩
        M₁ i f
          ∎
      }
    ; trans = λ {i j k} eq eq′ → record
      { M₀≡ = ≡.trans (M₀≡ eq) (M₀≡ eq′)
      ; M₁≡ = λ {_ _ f} → begin
        ≡.subst₂ (Graph._⇒_ B) (≡.trans (M₀≡ eq) (M₀≡ eq′)) (≡.trans (M₀≡ eq) (M₀≡ eq′)) (M₁ i f)
          ≈˘⟨ subst₂-subst₂ (Graph._⇒_ B) (M₀≡ eq) (M₀≡ eq′) (M₀≡ eq) (M₀≡ eq′) ⟩
        ≡.subst₂ (Graph._⇒_ B) (M₀≡ eq′) (M₀≡ eq′) (≡.subst₂ (Graph._⇒_ B) (M₀≡ eq) (M₀≡ eq) (M₁ i f))
          ≈⟨ ≡.cong (≡.subst₂ (Graph._⇒_ B) (M₀≡ eq′) (M₀≡ eq′)) (M₁≡ eq) ⟩
        ≡.subst₂ (Graph._⇒_ B) (M₀≡ eq′) (M₀≡ eq′) (M₁ j f)
          ≈⟨ M₁≡ eq′ ⟩
        M₁ k f
          ∎
      }
    }
  ; ∘-resp-≈  = λ {_ B C} {f g h i} eq eq′ → record
    { M₀≡ = λ {X} → ≡.trans (≡.cong (M₀ f) (M₀≡ eq′)) (M₀≡ eq)
    ; M₁≡ = λ {_ _ j} → begin
      ≡.subst₂ (Graph._⇒_ C)
               (≡.trans (≡.cong (M₀ f) (M₀≡ eq′)) (M₀≡ eq))
               (≡.trans (≡.cong (M₀ f) (M₀≡ eq′)) (M₀≡ eq)) (M₁ f (M₁ h j))
        ≈˘⟨ subst₂-subst₂ (Graph._⇒_ C) (≡.cong (M₀ f) (M₀≡ eq′)) (M₀≡ eq) (≡.cong (M₀ f) (M₀≡ eq′)) (M₀≡ eq) ⟩
      ≡.subst₂ (Graph._⇒_ C) (M₀≡ eq) (M₀≡ eq)
               (≡.subst₂ (Graph._⇒_ C) (≡.cong (M₀ f) (M₀≡ eq′))
                         (≡.cong (M₀ f) (M₀≡ eq′)) (M₁ f (M₁ h j)))
        ≈⟨ ≡.cong (≡.subst₂ (Graph._⇒_ C) (M₀≡ eq) (M₀≡ eq)) $ subst₂-app (Graph._⇒_ C) (M₁ h j) (λ _ _ → M₁ f) (M₀≡ eq′) (M₀≡ eq′) ⟩
      ≡.subst₂ (Graph._⇒_ C) (M₀≡ eq) (M₀≡ eq) (M₁ f (≡.subst₂ (Graph._⇒_ B) (M₀≡ eq′) (M₀≡ eq′) (M₁ h j)))
        ≈⟨ ≡.cong (λ x → ≡.subst₂ (Graph._⇒_ C) (M₀≡ eq) (M₀≡ eq) (M₁ f x)) (M₁≡ eq′) ⟩
      ≡.subst₂ (Graph._⇒_ C) (M₀≡ eq) (M₀≡ eq) (M₁ f (M₁ i j))
        ≈⟨ M₁≡ eq ⟩
      M₁ g (M₁ i j)
        ∎
    }
  }
  where open GraphMorphism
        open GraphMorphism≈
        module EqR′ {s} {S : Set s} = EqR (≡.setoid S)
        open EqR′
        _∘_ : {A B C : Graph o ℓ e} → GraphMorphism B C → GraphMorphism A B → GraphMorphism A C
        M ∘ M′ = record
          { M₀       = λ X → M₀ M (M₀ M′ X)
          ; M₁       = λ f → M₁ M (M₁ M′ f)
          ; M-resp-≈ = λ eq → M-resp-≈ M (M-resp-≈ M′ eq)
          }
        
