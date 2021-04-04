{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Diagram.Pullback

module Categories.Bicategory.Construction.Spans {o ℓ e} {𝒞 : Category o ℓ e}
                                                (_×ₚ_ : ∀ {X Y Z} → (f : 𝒞 [ X , Z ]) (g : 𝒞 [ Y , Z ]) → Pullback 𝒞 f g) where

open import Level
open import Function using (_$_)

open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; uncurry)

open import Categories.Bicategory
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (refl; sym)

open import Categories.Category.Diagram.Span 𝒞
open import Categories.Category.Construction.Spans 𝒞 renaming (Spans to Spans₁)

open import Categories.Morphism
open import Categories.Morphism.Reasoning 𝒞

private
  module Spans₁ X Y = Category (Spans₁ X Y)

open Category 𝒞
open HomReasoning
open Equiv

open Span
open Span⇒
open Pullback

open Compositions _×ₚ_

private
  variable
    A B C D E : Obj

  --------------------------------------------------------------------------------
  -- Proofs about span compositions

⊚₁-identity : ∀ (f : Span B C) → (g : Span A B) → Spans₁ A C [ Spans₁.id B C {f} ⊚₁ Spans₁.id A B {g} ≈ Spans₁.id A C ]
⊚₁-identity f g = ⟺ (unique ((cod g) ×ₚ (dom f)) id-comm id-comm)

⊚₁-homomorphism : {f f′ f″ : Span B C} {g g′ g″ : Span A B}
                  → (α : Span⇒ f f′) → (α′ : Span⇒ f′ f″)
                  → (β : Span⇒ g g′) → (β′ : Span⇒ g′ g″)
                  → Spans₁ A C [ (Spans₁ B C [ α′ ∘ α ]) ⊚₁ (Spans₁ A B [ β′ ∘ β ]) ≈ Spans₁ A C [ α′ ⊚₁ β′ ∘ α ⊚₁ β ] ]
⊚₁-homomorphism {A} {B} {C} {f} {f′} {f″} {g} {g′} {g″} α α′ β β′ =
  let pullback  = (cod g) ×ₚ (dom f)
      pullback′ = (cod g′) ×ₚ(dom f′)
      pullback″ = (cod g″) ×ₚ (dom f″)
      α-chase = begin
        p₂ pullback″ ∘ universal pullback″ _ ∘ universal pullback′ _ ≈⟨ pullˡ (p₂∘universal≈h₂ pullback″) ⟩
        (arr α′ ∘ p₂ pullback′) ∘ universal pullback′ _ ≈⟨ extendˡ (p₂∘universal≈h₂ pullback′) ⟩
        (arr α′ ∘ arr α) ∘ p₂ pullback ∎
      β-chase = begin
        p₁ pullback″ ∘ universal pullback″ _ ∘ universal pullback′ _            ≈⟨ pullˡ (p₁∘universal≈h₁ pullback″) ⟩
        (arr β′ ∘ p₁ pullback′) ∘ universal pullback′ _ ≈⟨ extendˡ (p₁∘universal≈h₁ pullback′) ⟩
        (arr β′ ∘ arr β) ∘ p₁ pullback                                          ∎
  in ⟺ (unique pullback″ β-chase α-chase)

--------------------------------------------------------------------------------
-- Associators

module _ (f : Span C D) (g : Span B C) (h : Span A B) where
  private
    pullback-fg    = (cod g) ×ₚ (dom f)
    pullback-gh    = (cod h) ×ₚ (dom g)
    pullback-⟨fg⟩h = (cod h) ×ₚ (dom (f ⊚₀ g))
    pullback-f⟨gh⟩ = (cod (g ⊚₀ h)) ×ₚ (dom f)

  ⊚-assoc : Span⇒ ((f ⊚₀ g) ⊚₀ h) (f ⊚₀ (g ⊚₀ h))
  ⊚-assoc = record
    { arr = universal pullback-f⟨gh⟩ {h₁ = universal pullback-gh (commute pullback-⟨fg⟩h ○ assoc)} $ begin
        (cod g ∘ p₂ pullback-gh) ∘ universal pullback-gh _ ≈⟨ pullʳ (p₂∘universal≈h₂ pullback-gh) ⟩
        cod g ∘ p₁ pullback-fg ∘ p₂ pullback-⟨fg⟩h         ≈⟨ extendʳ (commute pullback-fg) ⟩
        dom f ∘ p₂ pullback-fg ∘ p₂ pullback-⟨fg⟩h         ∎
    ; commute-dom = begin
        ((dom h ∘ p₁ pullback-gh) ∘ p₁ pullback-f⟨gh⟩) ∘ universal pullback-f⟨gh⟩ _ ≈⟨ pullʳ (p₁∘universal≈h₁ pullback-f⟨gh⟩) ⟩
        (dom h ∘ p₁ pullback-gh) ∘ universal pullback-gh _                          ≈⟨ pullʳ (p₁∘universal≈h₁ pullback-gh) ⟩
        dom h ∘ p₁ pullback-⟨fg⟩h                                                   ∎
    ; commute-cod = begin
        (cod f ∘ p₂ pullback-f⟨gh⟩) ∘ universal pullback-f⟨gh⟩ _ ≈⟨ extendˡ (p₂∘universal≈h₂ pullback-f⟨gh⟩) ⟩
        (cod f ∘ p₂ pullback-fg) ∘ p₂ pullback-⟨fg⟩h             ∎
    }

  ⊚-assoc⁻¹ :  Span⇒ (f ⊚₀ (g ⊚₀ h)) ((f ⊚₀ g) ⊚₀ h)
  ⊚-assoc⁻¹ = record
    { arr = universal pullback-⟨fg⟩h {h₁ = p₁ pullback-gh ∘ p₁ pullback-f⟨gh⟩} {h₂ = universal pullback-fg (⟺ assoc ○ commute pullback-f⟨gh⟩)} $ begin
        cod h ∘ p₁ pullback-gh ∘ p₁ pullback-f⟨gh⟩         ≈⟨ extendʳ (commute pullback-gh) ⟩
        dom g ∘ p₂ pullback-gh ∘ p₁ pullback-f⟨gh⟩         ≈⟨ pushʳ (⟺ (p₁∘universal≈h₁ pullback-fg)) ⟩
        (dom g ∘ p₁ pullback-fg) ∘ universal pullback-fg _ ∎
      ; commute-dom = begin
        (dom h ∘ p₁ pullback-⟨fg⟩h) ∘ universal pullback-⟨fg⟩h _ ≈⟨ extendˡ (p₁∘universal≈h₁ pullback-⟨fg⟩h) ⟩
        (dom h ∘ p₁ pullback-gh) ∘ p₁ pullback-f⟨gh⟩             ∎
    ; commute-cod = begin
        ((cod f ∘ p₂ pullback-fg) ∘ p₂ pullback-⟨fg⟩h) ∘ universal pullback-⟨fg⟩h _ ≈⟨ pullʳ (p₂∘universal≈h₂ pullback-⟨fg⟩h) ⟩
        (cod f ∘ p₂ pullback-fg) ∘ universal pullback-fg _                          ≈⟨ pullʳ (p₂∘universal≈h₂ pullback-fg) ⟩
        cod f ∘ p₂ pullback-f⟨gh⟩                                                   ∎
    }

  ⊚-assoc-iso : Iso (Spans₁ A D) ⊚-assoc ⊚-assoc⁻¹
  ⊚-assoc-iso = record
    { isoˡ =
      let lemma-fgˡ = begin
            p₁ pullback-fg ∘ universal pullback-fg _ ∘ universal pullback-f⟨gh⟩ _ ≈⟨ pullˡ (p₁∘universal≈h₁ pullback-fg) ⟩
            (p₂ pullback-gh ∘ p₁ pullback-f⟨gh⟩) ∘ universal pullback-f⟨gh⟩ _     ≈⟨ pullʳ (p₁∘universal≈h₁ pullback-f⟨gh⟩) ⟩
            p₂ pullback-gh ∘ universal pullback-gh _                              ≈⟨ p₂∘universal≈h₂ pullback-gh ⟩
            p₁ pullback-fg ∘ p₂ pullback-⟨fg⟩h                                    ∎

          lemma-fgʳ = begin
            p₂ pullback-fg ∘ universal pullback-fg _ ∘ universal pullback-f⟨gh⟩ _ ≈⟨ pullˡ (p₂∘universal≈h₂ pullback-fg) ⟩
            p₂ pullback-f⟨gh⟩ ∘ universal pullback-f⟨gh⟩ _                        ≈⟨ p₂∘universal≈h₂ pullback-f⟨gh⟩ ⟩
            p₂ pullback-fg ∘ p₂ pullback-⟨fg⟩h                                    ∎

          lemmaˡ = begin
            p₁ pullback-⟨fg⟩h ∘ universal pullback-⟨fg⟩h _ ∘ universal pullback-f⟨gh⟩ _ ≈⟨ pullˡ (p₁∘universal≈h₁ pullback-⟨fg⟩h) ⟩
            (p₁ pullback-gh ∘ p₁ pullback-f⟨gh⟩) ∘ universal pullback-f⟨gh⟩ _           ≈⟨ pullʳ (p₁∘universal≈h₁ pullback-f⟨gh⟩) ⟩
            p₁ pullback-gh ∘ universal pullback-gh _                                    ≈⟨ p₁∘universal≈h₁ pullback-gh ⟩
            p₁ pullback-⟨fg⟩h                                                           ∎

          lemmaʳ = begin
            p₂ pullback-⟨fg⟩h ∘ universal pullback-⟨fg⟩h _ ∘ universal pullback-f⟨gh⟩ _ ≈⟨ pullˡ (p₂∘universal≈h₂ pullback-⟨fg⟩h) ⟩
            universal pullback-fg _ ∘ universal pullback-f⟨gh⟩ _                        ≈⟨ unique-diagram pullback-fg lemma-fgˡ lemma-fgʳ ⟩
            p₂ pullback-⟨fg⟩h                                                           ∎
      in unique pullback-⟨fg⟩h lemmaˡ lemmaʳ ○ ⟺ (Pullback.id-unique pullback-⟨fg⟩h)
    ; isoʳ =
      let lemma-ghˡ = begin
            p₁ pullback-gh ∘ universal pullback-gh _ ∘ universal pullback-⟨fg⟩h _ ≈⟨  pullˡ (p₁∘universal≈h₁ pullback-gh) ⟩
            p₁ pullback-⟨fg⟩h ∘ universal pullback-⟨fg⟩h _                        ≈⟨  p₁∘universal≈h₁ pullback-⟨fg⟩h ⟩
            p₁ pullback-gh ∘ p₁ pullback-f⟨gh⟩                                    ∎

          lemma-ghʳ = begin
            p₂ pullback-gh ∘ universal pullback-gh _ ∘ universal pullback-⟨fg⟩h _ ≈⟨ pullˡ (p₂∘universal≈h₂ pullback-gh) ⟩
            (p₁ pullback-fg ∘ p₂ pullback-⟨fg⟩h) ∘ universal pullback-⟨fg⟩h _     ≈⟨ pullʳ (p₂∘universal≈h₂ pullback-⟨fg⟩h) ⟩
            p₁ pullback-fg ∘ universal pullback-fg _                              ≈⟨ p₁∘universal≈h₁ pullback-fg ⟩
            p₂ pullback-gh ∘ p₁ pullback-f⟨gh⟩ ∎ 

          lemmaˡ = begin
            p₁ pullback-f⟨gh⟩ ∘ universal pullback-f⟨gh⟩ _ ∘ universal pullback-⟨fg⟩h _ ≈⟨ pullˡ (p₁∘universal≈h₁ pullback-f⟨gh⟩) ⟩
            universal pullback-gh _ ∘ universal pullback-⟨fg⟩h _                        ≈⟨ unique-diagram pullback-gh lemma-ghˡ lemma-ghʳ ⟩
            p₁ pullback-f⟨gh⟩                                                           ∎
          lemmaʳ = begin
            p₂ pullback-f⟨gh⟩ ∘ universal pullback-f⟨gh⟩ _ ∘ universal pullback-⟨fg⟩h _ ≈⟨ pullˡ (p₂∘universal≈h₂ pullback-f⟨gh⟩) ⟩
            (p₂ pullback-fg ∘ p₂ pullback-⟨fg⟩h) ∘ universal pullback-⟨fg⟩h _           ≈⟨ pullʳ (p₂∘universal≈h₂ pullback-⟨fg⟩h) ⟩
            p₂ pullback-fg ∘ universal pullback-fg _                                    ≈⟨ p₂∘universal≈h₂ pullback-fg ⟩
            p₂ pullback-f⟨gh⟩                                                           ∎
      in unique pullback-f⟨gh⟩ lemmaˡ lemmaʳ ○ ⟺ (Pullback.id-unique pullback-f⟨gh⟩)
    }

⊚-assoc-commute : ∀ {f f′ : Span C D} {g g′ : Span B C} {h h′ : Span A B} → (α : Span⇒ f f′) → (β : Span⇒ g g′) → (γ : Span⇒ h h′)
            → Spans₁ A D [ Spans₁ A D [ ⊚-assoc f′ g′ h′ ∘ (α ⊚₁ β) ⊚₁ γ ] ≈ Spans₁ A D [ α ⊚₁ (β ⊚₁ γ) ∘ ⊚-assoc f g h ] ]
⊚-assoc-commute {f = f} {f′ = f′} {g = g} {g′ = g′} {h = h} {h′ = h′} α β γ =
  let pullback-fg     = (cod g) ×ₚ (dom f)
      pullback-fg′    = (cod g′) ×ₚ (dom f′)
      pullback-gh     = (cod h) ×ₚ (dom g)
      pullback-gh′    = (cod h′) ×ₚ (dom g′)
      pullback-f⟨gh⟩  = (cod (g ⊚₀ h)) ×ₚ (dom f)
      pullback-f⟨gh⟩′ = (cod (g′ ⊚₀ h′)) ×ₚ (dom f′)
      pullback-⟨fg⟩h  = (cod h) ×ₚ (dom (f ⊚₀ g))
      pullback-⟨fg⟩h′ = (cod h′) ×ₚ (dom (f′ ⊚₀ g′))

      lemma-ghˡ′ = begin
        p₁ pullback-gh′ ∘ universal pullback-gh′ _ ∘ universal pullback-⟨fg⟩h′ _ ≈⟨ pullˡ (p₁∘universal≈h₁ pullback-gh′) ⟩
        p₁ pullback-⟨fg⟩h′ ∘ universal pullback-⟨fg⟩h′ _                         ≈⟨ p₁∘universal≈h₁ pullback-⟨fg⟩h′ ⟩
        arr γ ∘ p₁ pullback-⟨fg⟩h                                                ≈⟨ pushʳ (⟺ (p₁∘universal≈h₁ pullback-gh)) ⟩
        (arr γ ∘ p₁ pullback-gh) ∘ universal pullback-gh _                       ≈⟨ pushˡ (⟺ (p₁∘universal≈h₁ pullback-gh′)) ⟩
        p₁ pullback-gh′ ∘ universal pullback-gh′ _ ∘ universal pullback-gh _     ∎

      lemma-ghʳ′ = begin
        p₂ pullback-gh′ ∘ universal pullback-gh′ _ ∘ universal pullback-⟨fg⟩h′ _ ≈⟨ pullˡ (p₂∘universal≈h₂ pullback-gh′) ⟩
        (p₁ pullback-fg′ ∘ p₂ pullback-⟨fg⟩h′) ∘ universal pullback-⟨fg⟩h′ _     ≈⟨ pullʳ (p₂∘universal≈h₂ pullback-⟨fg⟩h′) ⟩
        p₁ pullback-fg′ ∘ universal pullback-fg′ _ ∘ p₂ pullback-⟨fg⟩h           ≈⟨ pullˡ (p₁∘universal≈h₁ pullback-fg′) ⟩
        (arr β ∘ p₁ pullback-fg) ∘ p₂ pullback-⟨fg⟩h                             ≈⟨ extendˡ (⟺ (p₂∘universal≈h₂ pullback-gh)) ⟩
        (arr β ∘ p₂ pullback-gh) ∘ universal pullback-gh _                       ≈⟨ pushˡ (⟺ (p₂∘universal≈h₂ pullback-gh′)) ⟩
        p₂ pullback-gh′ ∘ universal pullback-gh′ _ ∘ universal pullback-gh _     ∎

      lemmaˡ = begin
        p₁ pullback-f⟨gh⟩′ ∘ universal pullback-f⟨gh⟩′ _ ∘ universal pullback-⟨fg⟩h′ _ ≈⟨ pullˡ (p₁∘universal≈h₁ pullback-f⟨gh⟩′) ⟩
        universal pullback-gh′ _ ∘ universal pullback-⟨fg⟩h′ _                         ≈⟨ unique-diagram pullback-gh′ lemma-ghˡ′ lemma-ghʳ′ ⟩
        universal pullback-gh′ _ ∘ universal pullback-gh _                             ≈⟨ pushʳ (⟺ (p₁∘universal≈h₁ pullback-f⟨gh⟩)) ⟩
        (universal pullback-gh′ _ ∘ p₁ pullback-f⟨gh⟩) ∘ universal pullback-f⟨gh⟩ _    ≈⟨ pushˡ (⟺ (p₁∘universal≈h₁ pullback-f⟨gh⟩′)) ⟩
        p₁ pullback-f⟨gh⟩′ ∘ universal pullback-f⟨gh⟩′ _ ∘ universal pullback-f⟨gh⟩ _  ∎

      lemmaʳ = begin
        p₂ pullback-f⟨gh⟩′ ∘ universal pullback-f⟨gh⟩′ _ ∘ universal pullback-⟨fg⟩h′ _ ≈⟨ pullˡ (p₂∘universal≈h₂ pullback-f⟨gh⟩′) ⟩
        (p₂ pullback-fg′ ∘ p₂ pullback-⟨fg⟩h′) ∘ universal pullback-⟨fg⟩h′ _           ≈⟨ pullʳ (p₂∘universal≈h₂ pullback-⟨fg⟩h′) ⟩
        p₂ pullback-fg′ ∘ universal pullback-fg′ _ ∘ p₂ pullback-⟨fg⟩h                 ≈⟨ pullˡ (p₂∘universal≈h₂ pullback-fg′) ⟩
        (arr α ∘ p₂ pullback-fg) ∘ p₂ pullback-⟨fg⟩h                                   ≈⟨ extendˡ (⟺ (p₂∘universal≈h₂ pullback-f⟨gh⟩)) ⟩
        (arr α ∘ p₂ pullback-f⟨gh⟩) ∘ universal pullback-f⟨gh⟩ _                       ≈⟨ pushˡ (⟺ (p₂∘universal≈h₂ pullback-f⟨gh⟩′)) ⟩
        p₂ pullback-f⟨gh⟩′ ∘ universal pullback-f⟨gh⟩′ _ ∘ universal pullback-f⟨gh⟩ _  ∎

  in unique-diagram pullback-f⟨gh⟩′ lemmaˡ lemmaʳ


--------------------------------------------------------------------------------
-- Unitors

module _ (f : Span A B) where
  private
    pullback-dom-f = id ×ₚ (dom f)
    pullback-cod-f = (cod f) ×ₚ id

  ⊚-unitˡ : Span⇒ (id-span ⊚₀ f) f
  ⊚-unitˡ = record
    { arr = p₁ pullback-cod-f
    ; commute-dom = refl
    ; commute-cod = commute pullback-cod-f
    }

  ⊚-unitˡ⁻¹ : Span⇒ f (id-span ⊚₀ f)
  ⊚-unitˡ⁻¹ = record
    { arr = universal pullback-cod-f id-comm
    ; commute-dom = cancelʳ (p₁∘universal≈h₁ pullback-cod-f)
    ; commute-cod = pullʳ (p₂∘universal≈h₂ pullback-cod-f) ○ identityˡ
    }

  ⊚-unitˡ-iso : Iso (Spans₁ A B) ⊚-unitˡ ⊚-unitˡ⁻¹
  ⊚-unitˡ-iso = record
    { isoˡ = unique-diagram pullback-cod-f (pullˡ (p₁∘universal≈h₁ pullback-cod-f) ○ id-comm-sym) (pullˡ (p₂∘universal≈h₂ pullback-cod-f) ○ commute pullback-cod-f ○ id-comm-sym)
    ; isoʳ = p₁∘universal≈h₁ pullback-cod-f
    }

  ⊚-unitʳ : Span⇒ (f ⊚₀ id-span) f
  ⊚-unitʳ = record
    { arr = p₂ pullback-dom-f
    ; commute-dom = ⟺ (commute pullback-dom-f)
    ; commute-cod = refl
    }

  ⊚-unitʳ⁻¹ : Span⇒ f (f ⊚₀ id-span)
  ⊚-unitʳ⁻¹ = record
    { arr = universal pullback-dom-f id-comm-sym
    ; commute-dom = pullʳ (p₁∘universal≈h₁ pullback-dom-f) ○ identityˡ
    ; commute-cod = pullʳ (p₂∘universal≈h₂ pullback-dom-f) ○ identityʳ
    }

  ⊚-unitʳ-iso : Iso (Spans₁ A B) ⊚-unitʳ ⊚-unitʳ⁻¹
  ⊚-unitʳ-iso = record
    { isoˡ = unique-diagram pullback-dom-f (pullˡ (p₁∘universal≈h₁ pullback-dom-f) ○ ⟺ (commute pullback-dom-f) ○ id-comm-sym) (pullˡ (p₂∘universal≈h₂ pullback-dom-f) ○ id-comm-sym)
    ; isoʳ = p₂∘universal≈h₂ pullback-dom-f
    }

⊚-unitˡ-commute : ∀ {f f′ : Span A B} → (α : Span⇒ f f′) → Spans₁ A B [ Spans₁ A B [ ⊚-unitˡ f′ ∘ Spans₁.id B B ⊚₁ α ] ≈ Spans₁ A B [ α ∘ ⊚-unitˡ f ] ]
⊚-unitˡ-commute {f′ = f′} α = p₁∘universal≈h₁ ((cod f′) ×ₚ id)

⊚-unitʳ-commute : ∀ {f f′ : Span A B} → (α : Span⇒ f f′) → Spans₁ A B [ Spans₁ A B [ ⊚-unitʳ f′ ∘ α ⊚₁ Spans₁.id A A ] ≈ Spans₁ A B [ α ∘ ⊚-unitʳ f ] ]
⊚-unitʳ-commute {f′ = f′} α = p₂∘universal≈h₂ (id ×ₚ (dom f′))

--------------------------------------------------------------------------------
-- Coherence Conditions

triangle : (f : Span A B) → (g : Span B C) → Spans₁ A C [ Spans₁ A C [ Spans₁.id B C {g} ⊚₁ ⊚-unitˡ f ∘ ⊚-assoc g id-span f ] ≈ ⊚-unitʳ g ⊚₁ Spans₁.id A B {f} ]
triangle f g =
  let pullback-dom-g = id ×ₚ (dom g)
      pullback-cod-f = (cod f) ×ₚ id
      pullback-fg    = (cod f) ×ₚ (dom g)
      pullback-id-fg = (cod (id-span ⊚₀ f)) ×ₚ (dom g)
      pullback-f-id-g = (cod f) ×ₚ (dom (id-span ⊚₀ g))
  in unique pullback-fg (pullˡ (p₁∘universal≈h₁ pullback-fg) ○ pullʳ (p₁∘universal≈h₁ pullback-id-fg) ○ p₁∘universal≈h₁ pullback-cod-f ○ ⟺ identityˡ)
                        (pullˡ (p₂∘universal≈h₂ pullback-fg) ○ pullʳ (p₂∘universal≈h₂ pullback-id-fg) ○ identityˡ)


pentagon : (f : Span A B) → (g : Span B C) → (h : Span C D) → (i : Span D E)
         →  Spans₁ A E [ Spans₁ A E [ (Spans₁.id D E {i}) ⊚₁ (⊚-assoc h g f) ∘ Spans₁ A E [ ⊚-assoc i (h ⊚₀ g) f ∘ ⊚-assoc i h g ⊚₁ Spans₁.id A B {f} ] ] ≈ Spans₁ A E [ ⊚-assoc i h (g ⊚₀ f) ∘ ⊚-assoc (i ⊚₀ h) g f ] ]
pentagon {A} {B} {C} {D} {E} f g h i =
  let pullback-fg       = (cod f) ×ₚ (dom g)
      pullback-gh       = (cod g) ×ₚ (dom h)
      pullback-hi       = (cod h) ×ₚ (dom i)
      pullback-f⟨gh⟩    = (cod f) ×ₚ (dom (h ⊚₀ g))
      pullback-⟨fg⟩h    = (cod (g ⊚₀ f)) ×ₚ (dom h)
      pullback-⟨gh⟩i    = (cod (h ⊚₀ g)) ×ₚ (dom i)
      pullback-g⟨hi⟩    = (cod g) ×ₚ (dom (i ⊚₀ h))
      pullback-⟨⟨fg⟩h⟩i = (cod (h ⊚₀ (g ⊚₀ f))) ×ₚ (dom i)
      pullback-⟨f⟨gh⟩⟩i = (cod ((h ⊚₀ g) ⊚₀ f)) ×ₚ (dom i)
      pullback-⟨fg⟩⟨hi⟩ = (cod (g ⊚₀ f)) ×ₚ (dom (i ⊚₀ h))
      pullback-f⟨⟨gh⟩i⟩ = (cod f) ×ₚ (dom (i ⊚₀ (h ⊚₀ g)))
      pullback-f⟨g⟨hi⟩⟩ = (cod f) ×ₚ (dom ((i ⊚₀ h) ⊚₀ g))

      lemma-fgˡ = begin
        p₁ pullback-fg ∘ universal pullback-fg _ ∘ universal pullback-f⟨gh⟩ _ ∘ universal pullback-f⟨⟨gh⟩i⟩ _ ≈⟨ pullˡ (p₁∘universal≈h₁ pullback-fg) ⟩
        p₁ pullback-f⟨gh⟩ ∘ universal pullback-f⟨gh⟩ _ ∘ universal pullback-f⟨⟨gh⟩i⟩ _                        ≈⟨ pullˡ (p₁∘universal≈h₁ pullback-f⟨gh⟩) ⟩
        p₁ pullback-f⟨⟨gh⟩i⟩ ∘ universal pullback-f⟨⟨gh⟩i⟩ _                                                  ≈⟨ p₁∘universal≈h₁ pullback-f⟨⟨gh⟩i⟩ ⟩
        id ∘ p₁ pullback-f⟨g⟨hi⟩⟩                                                                             ≈⟨ identityˡ ⟩
        p₁ pullback-f⟨g⟨hi⟩⟩                                                                                  ≈˘⟨ p₁∘universal≈h₁ pullback-fg ⟩
        p₁ pullback-fg ∘ universal pullback-fg _                                                              ∎

      lemma-fgʳ = begin
        p₂ pullback-fg ∘ universal pullback-fg _ ∘ universal pullback-f⟨gh⟩ _ ∘ universal pullback-f⟨⟨gh⟩i⟩ _ ≈⟨ pullˡ (p₂∘universal≈h₂ pullback-fg) ⟩
        (p₁ pullback-gh ∘ p₂ pullback-f⟨gh⟩) ∘ universal pullback-f⟨gh⟩ _ ∘ universal pullback-f⟨⟨gh⟩i⟩ _     ≈⟨ center (p₂∘universal≈h₂ pullback-f⟨gh⟩) ⟩
        p₁ pullback-gh ∘ (p₁ pullback-⟨gh⟩i ∘ p₂ pullback-f⟨⟨gh⟩i⟩) ∘ universal pullback-f⟨⟨gh⟩i⟩ _           ≈⟨ center⁻¹ refl (p₂∘universal≈h₂ pullback-f⟨⟨gh⟩i⟩) ⟩
        (p₁ pullback-gh ∘ p₁ pullback-⟨gh⟩i) ∘ universal pullback-⟨gh⟩i _ ∘ p₂ pullback-f⟨g⟨hi⟩⟩              ≈⟨ center (p₁∘universal≈h₁ pullback-⟨gh⟩i) ⟩ 
        p₁ pullback-gh ∘ universal pullback-gh _ ∘ p₂ pullback-f⟨g⟨hi⟩⟩                                       ≈⟨ pullˡ (p₁∘universal≈h₁ pullback-gh) ⟩
        p₁ pullback-g⟨hi⟩ ∘ p₂ pullback-f⟨g⟨hi⟩⟩                                                              ≈˘⟨ p₂∘universal≈h₂ pullback-fg ⟩
        p₂ pullback-fg ∘ universal pullback-fg _                                                              ∎

      lemma-⟨fg⟩hˡ = begin
        p₁ pullback-⟨fg⟩h ∘ universal pullback-⟨fg⟩h _ ∘ universal pullback-f⟨gh⟩ _ ∘ universal pullback-f⟨⟨gh⟩i⟩ _ ≈⟨ pullˡ (p₁∘universal≈h₁ pullback-⟨fg⟩h) ⟩
        universal pullback-fg _ ∘ universal pullback-f⟨gh⟩ _ ∘ universal pullback-f⟨⟨gh⟩i⟩ _                        ≈⟨ unique-diagram pullback-fg lemma-fgˡ lemma-fgʳ ⟩
        universal pullback-fg _                                                                                     ≈˘⟨ p₁∘universal≈h₁ pullback-⟨fg⟩⟨hi⟩ ⟩
        p₁ pullback-⟨fg⟩⟨hi⟩ ∘ universal pullback-⟨fg⟩⟨hi⟩ _                                                        ≈⟨ pushˡ (⟺ (p₁∘universal≈h₁ pullback-⟨fg⟩h)) ⟩
        p₁ pullback-⟨fg⟩h ∘ universal pullback-⟨fg⟩h _ ∘ universal pullback-⟨fg⟩⟨hi⟩ _                              ∎

      lemma-⟨fg⟩hʳ = begin
        p₂ pullback-⟨fg⟩h ∘ universal pullback-⟨fg⟩h _ ∘ universal pullback-f⟨gh⟩ _ ∘ universal pullback-f⟨⟨gh⟩i⟩ _ ≈⟨ pullˡ (p₂∘universal≈h₂ pullback-⟨fg⟩h) ⟩
        (p₂ pullback-gh ∘ p₂ pullback-f⟨gh⟩) ∘ universal pullback-f⟨gh⟩ _ ∘ universal pullback-f⟨⟨gh⟩i⟩ _           ≈⟨ center (p₂∘universal≈h₂ pullback-f⟨gh⟩) ⟩
        p₂ pullback-gh ∘ (p₁ pullback-⟨gh⟩i ∘ p₂ pullback-f⟨⟨gh⟩i⟩) ∘ universal pullback-f⟨⟨gh⟩i⟩ _                 ≈⟨ center⁻¹ refl (p₂∘universal≈h₂ pullback-f⟨⟨gh⟩i⟩) ⟩
        (p₂ pullback-gh ∘ p₁ pullback-⟨gh⟩i) ∘ universal pullback-⟨gh⟩i _ ∘ p₂ pullback-f⟨g⟨hi⟩⟩                    ≈⟨ center (p₁∘universal≈h₁ pullback-⟨gh⟩i) ⟩
        p₂ pullback-gh ∘ universal pullback-gh _ ∘ p₂ pullback-f⟨g⟨hi⟩⟩                                             ≈⟨ extendʳ (p₂∘universal≈h₂ pullback-gh) ⟩
        p₁ pullback-hi ∘ p₂ pullback-g⟨hi⟩ ∘ p₂ pullback-f⟨g⟨hi⟩⟩                                                   ≈⟨ pushʳ (⟺ (p₂∘universal≈h₂ pullback-⟨fg⟩⟨hi⟩)) ⟩
        (p₁ pullback-hi ∘ p₂ pullback-⟨fg⟩⟨hi⟩) ∘ universal pullback-⟨fg⟩⟨hi⟩ _                                     ≈⟨ pushˡ (⟺ (p₂∘universal≈h₂ pullback-⟨fg⟩h)) ⟩
        p₂ pullback-⟨fg⟩h ∘ universal pullback-⟨fg⟩h _ ∘ universal pullback-⟨fg⟩⟨hi⟩ _                              ∎

      lemmaˡ = begin
        p₁ pullback-⟨⟨fg⟩h⟩i ∘ universal pullback-⟨⟨fg⟩h⟩i _ ∘ universal pullback-⟨f⟨gh⟩⟩i _ ∘ universal pullback-f⟨⟨gh⟩i⟩ _ ≈⟨ pullˡ (p₁∘universal≈h₁ pullback-⟨⟨fg⟩h⟩i) ⟩
        (universal pullback-⟨fg⟩h _ ∘ p₁ pullback-⟨f⟨gh⟩⟩i) ∘ universal pullback-⟨f⟨gh⟩⟩i _ ∘ universal pullback-f⟨⟨gh⟩i⟩ _  ≈⟨ center (p₁∘universal≈h₁ pullback-⟨f⟨gh⟩⟩i) ⟩
        universal pullback-⟨fg⟩h _ ∘ universal pullback-f⟨gh⟩ _ ∘ universal pullback-f⟨⟨gh⟩i⟩ _                              ≈⟨ unique-diagram pullback-⟨fg⟩h lemma-⟨fg⟩hˡ lemma-⟨fg⟩hʳ ⟩
        universal pullback-⟨fg⟩h _ ∘ universal pullback-⟨fg⟩⟨hi⟩ _                                                           ≈⟨ pushˡ (⟺ (p₁∘universal≈h₁ pullback-⟨⟨fg⟩h⟩i)) ⟩
        p₁ pullback-⟨⟨fg⟩h⟩i ∘ universal pullback-⟨⟨fg⟩h⟩i _ ∘ universal pullback-⟨fg⟩⟨hi⟩ _                                 ∎

      lemmaʳ = begin
        p₂ pullback-⟨⟨fg⟩h⟩i ∘ universal pullback-⟨⟨fg⟩h⟩i _ ∘ universal pullback-⟨f⟨gh⟩⟩i _ ∘ universal pullback-f⟨⟨gh⟩i⟩ _ ≈⟨ pullˡ (p₂∘universal≈h₂ pullback-⟨⟨fg⟩h⟩i) ⟩
        (id ∘ p₂ pullback-⟨f⟨gh⟩⟩i) ∘ universal pullback-⟨f⟨gh⟩⟩i _ ∘ universal pullback-f⟨⟨gh⟩i⟩ _                          ≈⟨ center (p₂∘universal≈h₂ pullback-⟨f⟨gh⟩⟩i) ⟩
        id ∘ (p₂ pullback-⟨gh⟩i ∘ p₂ pullback-f⟨⟨gh⟩i⟩) ∘ universal pullback-f⟨⟨gh⟩i⟩ _                                      ≈⟨ center⁻¹ identityˡ (p₂∘universal≈h₂ pullback-f⟨⟨gh⟩i⟩) ⟩
        p₂ pullback-⟨gh⟩i ∘ universal pullback-⟨gh⟩i _ ∘ p₂ pullback-f⟨g⟨hi⟩⟩                                                ≈⟨ pullˡ (p₂∘universal≈h₂ pullback-⟨gh⟩i) ⟩
        (p₂ pullback-hi ∘ p₂ pullback-g⟨hi⟩) ∘ p₂ pullback-f⟨g⟨hi⟩⟩                                                          ≈⟨ extendˡ (⟺ (p₂∘universal≈h₂ pullback-⟨fg⟩⟨hi⟩)) ⟩
        (p₂ pullback-hi ∘ p₂ pullback-⟨fg⟩⟨hi⟩) ∘ universal pullback-⟨fg⟩⟨hi⟩ _                                              ≈⟨ pushˡ (⟺ (p₂∘universal≈h₂ pullback-⟨⟨fg⟩h⟩i)) ⟩
        p₂ pullback-⟨⟨fg⟩h⟩i ∘ universal pullback-⟨⟨fg⟩h⟩i _ ∘ universal pullback-⟨fg⟩⟨hi⟩ _                                 ∎

  in unique-diagram pullback-⟨⟨fg⟩h⟩i lemmaˡ lemmaʳ

Spans : Bicategory (o ⊔ ℓ) (o ⊔ ℓ ⊔ e) e o
Spans = record
  { enriched = record
    { Obj = Obj
    ; hom = Spans₁
    ; id = λ {A} → record
      { F₀ = λ _ → id-span
      ; F₁ = λ _ → Spans₁.id A A
      ; identity = refl
      ; homomorphism = ⟺ identity²
      ; F-resp-≈ = λ _ → refl
      }
    ; ⊚ = record
      { F₀ = λ (f , g) → f ⊚₀ g
      ; F₁ = λ (α , β) → α ⊚₁ β
      ; identity = λ {(f , g)} → ⊚₁-identity f g
      ; homomorphism = λ {X} {Y} {Z} {(α , α′)} {(β , β′)} → ⊚₁-homomorphism α β α′ β′
      ; F-resp-≈ = λ {(f , g)} {(f′ , g′)} {_} {_} (α-eq , β-eq) → universal-resp-≈ ((cod g′) ×ₚ (dom f′)) (∘-resp-≈ˡ β-eq) (∘-resp-≈ˡ α-eq)
      }
    ; ⊚-assoc = niHelper record
      { η = λ ((f , g) , h) → ⊚-assoc f g h
      ; η⁻¹ = λ ((f , g) , h) → ⊚-assoc⁻¹ f g h
      ; commute = λ ((α , β) , γ) → ⊚-assoc-commute α β γ
      ; iso = λ ((f , g) , h) → ⊚-assoc-iso f g h
      }
    ; unitˡ = niHelper record
      { η = λ (_ , f) → ⊚-unitˡ f
      ; η⁻¹ = λ (_ , f) → ⊚-unitˡ⁻¹ f
      ; commute = λ (_ , α) → ⊚-unitˡ-commute α
      ; iso = λ (_ , f) → ⊚-unitˡ-iso f
      }
    ; unitʳ = niHelper record
      { η = λ (f , _) → ⊚-unitʳ f
      ; η⁻¹ = λ (f , _) → ⊚-unitʳ⁻¹ f
      ; commute = λ (α , _) → ⊚-unitʳ-commute α
      ; iso = λ (f , _) → ⊚-unitʳ-iso f
      }
    }
  ; triangle = λ {_} {_} {_} {f} {g} → triangle f g
  ; pentagon = λ {_} {_} {_} {_} {_} {f} {g} {h} {i} → pentagon f g h i
  }
