{-# OPTIONS --without-K --lossy-unification --safe #-}

module Categories.Diagram.End.Fubini where

open import Level
open import Data.Product using (Σ; _,_; _×_) renaming (proj₁ to fst; proj₂ to snd)
open import Function using (_$_)

open import Categories.Category using (Category)
open import Categories.Category.Construction.Functors using (Functors; curry)
open import Categories.Category.Product using (πˡ; πʳ; _⁂_; _※_; Swap) renaming (Product to _×ᶜ_)
open import Categories.Diagram.End using () renaming (End to ∫)
open import Categories.Diagram.End.Properties using (end-η-commute; end-unique)
open import Categories.Diagram.End.Parameterized using () renaming (EndF to ⨏)
open import Categories.Diagram.Wedge using (Wedge)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Bifunctor using (Bifunctor; appˡ)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.NaturalTransformation.Dinatural using (DinaturalTransformation; dtHelper)

import Categories.Morphism as M
import Categories.Morphism.Reasoning as MR

variable
  o ℓ e : Level
  C P D : Category o ℓ e

module Functor-Swaps  (F : Bifunctor (Category.op C ×ᶜ Category.op P) (C ×ᶜ P) D) where
  private
    module C = Category C
    module P = Category P

  -- just shuffling arguments
  -- An end of F ′ can be taken iterated, instead of in the product category
  _′ : Bifunctor (P.op ×ᶜ P) (C.op ×ᶜ C) D
  _′ = F ∘F ((πˡ ∘F πʳ ※ πˡ ∘F πˡ) ※ (πʳ ∘F πʳ ※ πʳ ∘F πˡ))

  -- An end of F ′′ is the same as F, but the order in the product category is reversed
  _′′ : Bifunctor (Category.op P ×ᶜ Category.op C) (P ×ᶜ C) D
  _′′ = F ∘F (Swap ⁂ Swap)

open Functor-Swaps

module _  (F : Bifunctor (Category.op C ×ᶜ Category.op P) (C ×ᶜ P) D)
          {ω : ∀ ((p , q) : Category.Obj P × Category.Obj P) → ∫ (appˡ (F ′) (p , q))}
           where
  open M D
  private
    module C = Category C
    module P = Category P
    module D = Category D
    open module F = Functor F using (F₀; F₁; F-resp-≈)
    ∫F = (⨏ (F ′) {ω})
    module ∫F = Functor ∫F

    module ω ((p , q) : P.Obj × P.Obj) = ∫ (ω (p , q))

  open _≅_
  open Iso
  open DinaturalTransformation using (α)
  open NaturalTransformation using (η)
  open Wedge renaming (E to apex)
  open Category D
  open import Categories.Morphism.Reasoning D
  open HomReasoning
  -- we show that wedges of (∫.E e₀) are in bijection with wedges of F
  -- following MacLane §IX.8
  private module _ (ρ : Wedge ∫F) where
    private
      open module ρ = Wedge ρ using () renaming (E to x)
    -- first, our wedge gives us a wedge in the product
    ξ : Wedge F
    ξ .apex = x
    ξ .dinatural = dtHelper record
      { α = λ { (c , p) → ω.dinatural.α (p , p) c ∘ ρ.dinatural.α p }
      ; commute = λ { {c , p} {d , q} (f , s) → begin
          F₁ ((C.id , P.id) , (f , s)) ∘ (ω.dinatural.α (p , p) c ∘ ρ.dinatural.α p) ∘ id
            ≈⟨ refl⟩∘⟨ identityʳ ⟩
          -- First we show dinaturality in C, which is 'trivial'
          F₁ ((C.id , P.id) , (f , s)) ∘ (ω.dinatural.α (p , p) c ∘ ρ.dinatural.α p)
            ≈⟨ (F-resp-≈ ((C.Equiv.sym C.identity² , P.Equiv.sym P.identity²) , (C.Equiv.sym C.identityˡ , P.Equiv.sym P.identityʳ)) ○ F.homomorphism) ⟩∘⟨refl ○ pullˡ assoc ⟩
          (F₁ ((C.id , P.id) , (C.id , s)) ∘ F₁ ((C.id , P.id) , (f , P.id)) ∘ ω.dinatural.α (p , p) c) ∘ ρ.dinatural.α p
            ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ ⟺ identityʳ) ⟩∘⟨refl ⟩
          (F₁ ((C.id , P.id) , (C.id , s)) ∘ F₁ ((C.id , P.id) , (f , P.id)) ∘ ω.dinatural.α (p , p) c ∘ id) ∘ ρ.dinatural.α p
            ≈⟨ (refl⟩∘⟨ ω.dinatural.commute (p , p) f) ⟩∘⟨refl ⟩
          (F₁ ((C.id , P.id) , (C.id , s)) ∘ F₁ ((f , P.id) , (C.id , P.id)) ∘ ω.dinatural.α (p , p) d ∘ id) ∘ ρ.dinatural.α p
            ≈⟨ extendʳ (⟺ F.homomorphism ○ F-resp-≈ ((MR.id-comm C , P.Equiv.refl) , (C.Equiv.refl , MR.id-comm P)) ○ F.homomorphism) ⟩∘⟨refl ⟩
          -- now, we must show dinaturality in P
          -- First, some reassosiations to make things easier
          (F₁ ((f , P.id) , (C.id , P.id)) ∘ F₁ ((C.id , P.id) , (C.id , s)) ∘ ω.dinatural.α (p , p) d ∘ id) ∘ ρ.dinatural.α p
            ≈⟨ assoc ○ refl⟩∘⟨ assoc ○ refl⟩∘⟨ refl⟩∘⟨ identityʳ ⟩∘⟨refl ⟩
          F₁ ((f , P.id) , (C.id , P.id)) ∘ (F₁ ((C.id , P.id) , (C.id , s)) ∘ ω.dinatural.α (p , p) d ∘ ρ.dinatural.α p)
          -- this is the hard part: we use commutativity from the bottom face of the cube.
          -- The fact that this exists (an arrow between ∫ F (p,p,- ,-) to ∫ F (p,q,- ,-)) is due to functorality of ∫ and curry₀.
          -- The square commutes by universiality of ω
            ≈⟨ refl⟩∘⟨ extendʳ (⟺ (end-η-commute ⦃ ω (p , p) ⦄ ⦃ ω (p , q) ⦄ (curry.₀.₁ (F ′) (P.id , s)) d)) ⟩
          -- now we can use dinaturality in ρ, which annoyingly has an `id` tacked on the end
          F₁ ((f , P.id) , (C.id , P.id)) ∘ ω.dinatural.α (p , q) d ∘ ∫F.F₁ (P.id , s) ∘ ρ.dinatural.α p
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨  ⟺ identityʳ ⟩
          F₁ ((f , P.id) , (C.id , P.id)) ∘ ω.dinatural.α (p , q) d ∘ ∫F.F₁ (P.id , s) ∘ ρ.dinatural.α p ∘ id
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ρ.dinatural.commute s ⟩
          F₁ ((f , P.id) , (C.id , P.id)) ∘ ω.dinatural.α (p , q) d ∘ ∫F.F₁ (s , P.id) ∘ ρ.dinatural.α q ∘ id
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ identityʳ ⟩
          F₁ ((f , P.id) , (C.id , P.id)) ∘ ω.dinatural.α (p , q) d ∘ ∫F.F₁ (s , P.id) ∘ ρ.dinatural.α q
          -- and now we're done. step backward through the previous isomorphisms to get dinaturality in f and s together
            ≈⟨ refl⟩∘⟨ extendʳ (end-η-commute ⦃ ω (q , q) ⦄ ⦃ ω (p , q) ⦄ (curry.₀.₁ (F ′) (s , P.id)) d) ⟩
          F₁ ((f , P.id) , (C.id , P.id)) ∘ (F₁ ((C.id , s) , (C.id , P.id)) ∘ ω.dinatural.α (q , q) d ∘ ρ.dinatural.α q)
            ≈⟨ pullˡ (⟺ F.homomorphism ○ F-resp-≈ ((C.identityˡ , P.identityʳ) , (C.identity² , P.identity²))) ⟩
          F₁ ((f , s) , (C.id , P.id)) ∘ ω.dinatural.α (q , q) d ∘ ρ.dinatural.α q
            ≈˘⟨ refl⟩∘⟨ identityʳ ⟩
          F₁ ((f , s) , (C.id , P.id)) ∘ (ω.dinatural.α (q , q) d ∘ ρ.dinatural.α q) ∘ id
          ∎
        }
      }

  -- now the opposite direction
  private module _ (ξ : Wedge F) where
    private
      open module ξ = Wedge ξ using () renaming (E to x)
    ρ : Wedge ∫F
    ρ .apex = x
    ρ .dinatural = dtHelper record
      { α = λ p → ω.factor (p , p) record
        { E = x
        ; dinatural = dtHelper record
          { α = λ c → ξ.dinatural.α (c , p)
          ; commute = λ f → ξ.dinatural.commute (f , P.id)
          }
        }
          -- end-η-commute ⦃ ω (?) ⦄ ⦃ ω (?) ⦄ (curry.₀.₁ (F ′) (?)) ?
      ; commute = λ {p} {q} f → ω.unique′ (p , q) λ {c} → begin
        ω.dinatural.α (p , q) c ∘ ∫F.₁ (P.id , f) ∘ ω.factor (p , p) _ ∘ id
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ identityʳ ⟩
        ω.dinatural.α (p , q) c ∘ ∫F.₁ (P.id , f) ∘ ω.factor (p , p) _
          ≈⟨ extendʳ $ end-η-commute ⦃ ω (p , p) ⦄ ⦃ ω (p , q) ⦄ (curry.₀.₁ (F ′) (P.id , f)) c ⟩
        F₁ ((C.id , P.id) , (C.id , f)) ∘ ω.dinatural.α (p , p) c ∘ ∫.factor (ω (p , p)) _
          ≈⟨ refl⟩∘⟨ ω.universal (p , p) ⟩
        F₁ ((C.id , P.id) , (C.id , f)) ∘ ξ.dinatural.α (c , p)
          ≈˘⟨ refl⟩∘⟨ identityʳ ⟩
        F₁ ((C.id , P.id) , (C.id , f)) ∘ ξ.dinatural.α (c , p) ∘ id
          ≈⟨ ξ.dinatural.commute (C.id , f) ⟩
        F₁ ((C.id , f) , (C.id , P.id)) ∘ ξ.dinatural.α (c , q) ∘ id
          ≈⟨ refl⟩∘⟨ identityʳ ⟩
        F₁ ((C.id , f) , (C.id , P.id)) ∘ ξ.dinatural.α (c , q)
          ≈˘⟨ refl⟩∘⟨ ω.universal (q , q) ⟩
        F₁ ((C.id , f) , (C.id , P.id)) ∘ ω.dinatural.α (q , q) c ∘ ω.factor (q , q) _
          ≈˘⟨ extendʳ $ end-η-commute ⦃ ω (q , q) ⦄ ⦃ ω (p , q) ⦄ (curry.₀.₁ (F ′) (f , P.id)) c ⟩
        ω.dinatural.α (p , q) c ∘ ∫F.₁ (f , P.id) ∘ ω.factor (q , q) _
          ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ identityʳ ⟩
        ω.dinatural.α (p , q) c ∘ ∫F.₁ (f , P.id) ∘ ω.factor (q , q) _ ∘ id
          ∎
      }
  -- This construction is actually stronger than Fubini. It states that the
  -- iterated end _is_ an end in the product category.
  -- Thus the product end need not exist.
  module _ {{eᵢ : ∫ (⨏ (F ′) {ω})}} where
    private
      module eᵢ = ∫ eᵢ
    eₚ : ∫ F
    eₚ .∫.wedge = ξ eᵢ.wedge
    eₚ .∫.factor W = eᵢ.factor (ρ W)
    eₚ .∫.universal {W} {c , p} = begin
      ξ eᵢ.wedge .dinatural.α (c , p) ∘ eᵢ.factor (ρ W)               ≈⟨ Equiv.refl ⟩
      (ω.dinatural.α (p , p) c ∘ eᵢ.dinatural.α p)  ∘ eᵢ.factor (ρ W) ≈⟨ assoc ⟩
      ω.dinatural.α (p , p) c ∘ (eᵢ.dinatural.α p  ∘ eᵢ.factor (ρ W)) ≈⟨ refl⟩∘⟨ eᵢ.universal {ρ W} {p} ⟩
      ω.dinatural.α (p , p) c ∘ (ρ W) .dinatural.α p                  ≈⟨ ω.universal (p , p) ⟩
      W .dinatural.α  (c , p)                                         ∎
    eₚ .∫.unique {W} {g} h = eᵢ.unique λ {A = p} → Equiv.sym $ ω.unique (p , p) (sym-assoc ○ h)
    module eₚ = ∫ eₚ

    -- corollary: if a product end exists, it is iso
    Fubini : {eₚ' : ∫ F} → ∫.E eᵢ ≅ ∫.E eₚ'
    Fubini {eₚ'} = end-unique eₚ eₚ'

  -- TODO show that an end ∫ F yields an end of ∫ (⨏ (F ′) {ω})

module _ (F : Bifunctor (Category.op C ×ᶜ Category.op P) (C ×ᶜ P) D)
         {ωᴾ : ∀ ((p , q) : Category.Obj P × Category.Obj P) → ∫ (appˡ (F ′) (p , q))}
         {ωᶜ : ∀ ((c , d) : Category.Obj C × Category.Obj C) → ∫ (appˡ (F ′′ ′)(c , d))}
         {{e₁ : ∫ (⨏ (F ′) {ωᴾ})}} {{e₂ : ∫ (⨏ (F ′′ ′) {ωᶜ})}} where
  open M D
  -- since `F` and `F′′` are functors from different categories we can't construct a
  -- natural isomorphism between them. Instead it is best to show that eₚ F is an end in
  -- ∫ (F ′′) or vice-versa, and then Fubini follows due to uniqueness of ends
  open Wedge renaming (E to apex)
  private
    eₚ′′ : ∫ (F ′′)
    eₚ′′  .∫.wedge .apex = eₚ.wedge.E F
    eₚ′′  .∫.wedge .dinatural = dtHelper record
      { α = λ (p , c) → eₚ.dinatural.α F (c , p)
      ; commute = λ (s , f) → eₚ.dinatural.commute F (f , s)
      }
    eₚ′′  .∫.factor W = eₚ.factor F record
      { W ; dinatural = dtHelper record
        { α = λ (c , p) → W.dinatural.α (p , c)
        ; commute = λ (f , s) → W.dinatural.commute (s , f)
        }
      }
      where module W = Wedge W
    eₚ′′  .∫.universal {W} {p , c} = eₚ.universal F
    eₚ′′  .∫.unique {W} {g} h = eₚ.unique F h

  Fubini′ : ∫.E e₁ ≅ ∫.E e₂
  Fubini′ = ≅.trans (Fubini F {ωᴾ} {eₚ' = eₚ F}) $
            ≅.trans (end-unique eₚ′′ (eₚ (F ′′)))
                    (≅.sym (Fubini (F ′′) {ωᶜ} {eₚ' = eₚ (F ′′)}))
