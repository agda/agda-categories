{-# OPTIONS --without-K --safe #-}

module Data.Quiver.Morphism where

-- Morphism of Quivers, as well as some useful kit (identity, composition, equivalence)

open import Level
open import Function using () renaming (id to idFun; _∘_ to _⊚_)
open import Data.Quiver
open import Relation.Binary using (IsEquivalence; Reflexive; Symmetric; Transitive)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; naturality)
open import Relation.Binary.PropositionalEquality.Properties
  using (trans-symʳ; trans-symˡ)
open import Relation.Binary.PropositionalEquality.Subst.Properties
  using (module Shorthands; module Transport; module TransportOverQ; module TransportMor)

infix 4 _≃_

private
  variable
    o o′ ℓ ℓ′ e e′ : Level

-- A Morphism of Quivers. As this is meant to be used as the underlying part of a
-- Category, the fields should be named the same as for Functor.
record Morphism (G : Quiver o ℓ e) (G′ : Quiver o′ ℓ′ e′) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private
    module G  = Quiver G
    module G′ = Quiver G′

  field
    F₀       : G.Obj → G′.Obj
    F₁       : ∀ {A B} → A G.⇒ B → F₀ A G′.⇒ F₀ B
    F-resp-≈ : ∀ {A B} {f g : A G.⇒ B} → f G.≈ g → F₁ f G′.≈ F₁ g

id : {G : Quiver o ℓ e} → Morphism G G
id = record { F₀ = idFun ; F₁ = idFun ; F-resp-≈ = idFun }

_∘_ : {G₁ G₂ G₃ : Quiver o ℓ e} (m₁ : Morphism G₂ G₃) (m₂ : Morphism G₁ G₂) → Morphism G₁ G₃
m₁ ∘ m₂ = record
  { F₀ = F₀ m₁ ⊚ F₀ m₂
  ; F₁ = F₁ m₁ ⊚ F₁ m₂
  ; F-resp-≈ = F-resp-≈ m₁ ⊚ F-resp-≈ m₂
  }
  where open Morphism

-- Define Morphism equivalence here as well.  Note how it is mixed, with
-- propositional equivalence mixed with edge-setoid equivalence.
record _≃_ {G : Quiver o ℓ e} {G′ : Quiver o′ ℓ′ e′}
    (M M′ : Morphism G G′) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  open Quiver G using (_⇒_)
  open Quiver G′ using (_≈_)
  private
    module M  = Morphism M
    module M′ = Morphism M′
  open Shorthands (Quiver._⇒_ G′)

  -- Pick a presentation of equivalence for graph morphisms that works
  -- well with functor equality.

  field
    F₀≡ : ∀ {X} → M.F₀ X ≡ M′.F₀ X
    F₁≡ : ∀ {A B} {f : A ⇒ B} → M.F₁ f ▸ F₀≡ ≈ F₀≡ ◂ M′.F₁ f

-- make the items from Quiver, Morphism and equivalences visible
open Quiver
open Morphism
open _≃_

module _ {G : Quiver o ℓ e} {G′ : Quiver o′ ℓ′ e′} where
  private
    ≃-refl : Reflexive {A = Morphism G G′} _≃_
    ≃-refl = record { F₀≡ = refl ; F₁≡ = Equiv.refl G′}

    ≃-sym : Symmetric {A = Morphism G G′} _≃_
    ≃-sym {i} {j} eq = record
      { F₀≡ = sym (F₀≡ eq)
      ; F₁≡ = λ {_ _ f} →
        let open EdgeReasoning G′
            open Transport (_⇒_ G′)
            open TransportOverQ (_⇒_ G′) (_≈_ G′)
            e₁ = F₀≡ eq
        in begin
          F₁ j f ▸ sym e₁                        ≡˘⟨ cong (_◂ (F₁ j f ▸ _)) (trans-symˡ e₁) ⟩
          trans (sym e₁) e₁ ◂ (F₁ j f ▸ sym e₁)  ≡˘⟨ ◂-assocˡ (sym e₁) (F₁ j f ▸ sym e₁) ⟩
          sym e₁ ◂ e₁ ◂ (F₁ j f ▸ sym e₁)        ≡⟨ cong (sym e₁ ◂_) (◂-▸-comm e₁ (F₁ j f) (sym e₁)) ⟩
          sym e₁ ◂ ((e₁ ◂ F₁ j f) ▸ sym e₁)      ≈˘⟨ ◂-resp-≈ (sym e₁) (▸-resp-≈ (F₁≡ eq) (sym e₁)) ⟩
          sym e₁ ◂ (F₁ i f ▸ e₁ ▸ sym e₁)        ≡⟨ cong (sym e₁ ◂_) (▸-assocʳ (F₁ i f) (sym e₁)) ⟩
          sym e₁ ◂ (F₁ i f ▸ trans e₁ (sym e₁))  ≡⟨ cong (λ p → sym e₁ ◂ (F₁ i f ▸ p)) (trans-symʳ e₁) ⟩
          sym e₁ ◂ F₁ i f                        ∎
      }

    ≃-trans : Transitive {A = Morphism G G′} _≃_
    ≃-trans {i} {j} {k} eq eq′ = record
      { F₀≡ = trans (F₀≡ eq) (F₀≡ eq′)
      ; F₁≡ = λ {_ _ f} →
        let open EdgeReasoning G′
            open Transport (_⇒_ G′)
            open TransportOverQ (_⇒_ G′) (_≈_ G′)
        in begin
          F₁ i f ▸ trans (F₀≡ eq) (F₀≡ eq′)  ≡˘⟨ ▸-assocʳ (F₁ i f) (F₀≡ eq′) ⟩
          (F₁ i f ▸ F₀≡ eq) ▸ F₀≡ eq′        ≈⟨ ▸-resp-≈ (F₁≡ eq) (F₀≡ eq′) ⟩
          (F₀≡ eq ◂ F₁ j f) ▸ F₀≡ eq′        ≡˘⟨ ◂-▸-comm (F₀≡ eq) (F₁ j f) (F₀≡ eq′) ⟩
          F₀≡ eq ◂ (F₁ j f ▸ F₀≡ eq′)        ≈⟨ ◂-resp-≈ (F₀≡ eq) (F₁≡ eq′) ⟩
          F₀≡ eq ◂ (F₀≡ eq′ ◂ F₁ k f)        ≡⟨ ◂-assocˡ (F₀≡ eq) (F₁ k f) ⟩
          trans (F₀≡ eq) (F₀≡ eq′) ◂ F₁ k f  ∎
      }

  ≃-Equivalence : IsEquivalence _≃_
  ≃-Equivalence = record
      { refl  = ≃-refl
      ; sym   = ≃-sym
      ; trans = ≃-trans {- λ {G i j k} eq eq′ →  -}
      }

≃-resp-∘ : {A B C : Quiver o ℓ e} {f g : Morphism B C} {h i : Morphism A B} →
  f ≃ g → h ≃ i → (f ∘ h) ≃ (g ∘ i)
≃-resp-∘ {B = G} {H} {f} {g} {h} {i} eq eq′ = record
  { F₀≡ = trans (cong (F₀ f) (F₀≡ eq′)) (F₀≡ eq)
  ; F₁≡ = λ {_ _ j} →
    let open EdgeReasoning H
        open Transport (_⇒_ H)
        open TransportOverQ (_⇒_ H) (_≈_ H)
        open Transport (_⇒_ G) using () renaming (_▸_ to _▹_; _◂_ to _◃_)
        open TransportMor (_⇒_ G) (_⇒_ H)
        e₁ = F₀≡ eq
        e₂ = F₀≡ eq′
    in begin
      F₁ (f ∘ h) j ▸ trans (cong (F₀ f) e₂) e₁    ≡˘⟨ ▸-assocʳ (F₁ f (F₁ h j)) e₁ ⟩
      F₁ f (F₁ h j) ▸ cong (F₀ f) e₂ ▸ e₁         ≡˘⟨ cong (_▸ e₁) ( M-resp-▸ (F₀ f) (F₁ f) (F₁ h j) e₂) ⟩
      F₁ f (F₁ h j ▹ e₂) ▸ e₁                     ≈⟨ F₁≡ eq ⟩
      e₁ ◂ F₁ g (F₁ h j ▹ e₂)                     ≈⟨ ◂-resp-≈ e₁ (F-resp-≈ g (F₁≡ eq′)) ⟩
      e₁ ◂ F₁ g (e₂ ◃ F₁ i j)                     ≡⟨ cong (e₁ ◂_) (M-resp-◂ (F₀ g) (F₁ g) e₂ (F₁ i j) ) ⟩
      e₁ ◂ cong (F₀ g) e₂ ◂ F₁ g (F₁ i j)         ≡⟨ ◂-assocˡ e₁ (F₁ g (F₁ i j)) ⟩
      trans e₁ (cong (F₀ g) e₂) ◂ F₁ g (F₁ i j)   ≡˘⟨ cong (_◂ F₁ g (F₁ i j)) (naturality (λ _ → e₁)) ⟩
      trans (cong (F₀ f) e₂) e₁ ◂ F₁ g (F₁ i j)   ∎
  }
