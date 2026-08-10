{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Cartesian using (Cartesian)

-- Defines the following properties of a Category:
-- Cartesian.GSMonoidal
--    a Cartesian category is GS-monoidal
--
--  (for the counital copy structure it also carries, which adds only that the
--   comultiplication is natural, see Cartesian.CounitalCopy)
--
-- The comonoid at every object is the diagonal and the terminal map, and each
-- gs-monoidal law is a statement about two maps into a product, so every proof
-- below is the same move: rewrite both sides into ⟨_,_⟩ form and compare
-- components.

module Categories.Category.Cartesian.GSMonoidal
  {o ℓ e} (𝒞 : Category o ℓ e) (cartesian : Cartesian 𝒞) where

open Category 𝒞
open HomReasoning

open import Categories.Category.Cartesian.SymmetricMonoidal using (symmetric)
open import Categories.Category.Monoidal.GSMonoidal using (GSMonoidal)

open import Categories.Morphism.Reasoning 𝒞 using (pullʳ)

private
  variable
    A B : Obj

open Cartesian cartesian using
  ( ⊤; !; !-unique₂; π₁; π₂; ⟨_,_⟩; _×₁_; Δ; Δ∘; ×₁∘Δ; ×₁∘⟨⟩
  ; ⟨⟩-cong₂; ⟨⟩-congʳ; ⟨⟩-congˡ; project₂; η
  ; swap; swap∘⟨⟩; assocˡ; assocʳ; assocˡ∘⟨⟩; assocʳ∘⟨⟩ )

-- The comonoid.  Read the three laws in the opposite monoidal category, which
-- is where Categories.Object.Monoid.IsMonoid states them, so their composites
-- run backwards from the usual monoid ones.

coassoc : (Δ {A} ×₁ id) ∘ Δ ≈ (assocʳ ∘ (id ×₁ Δ)) ∘ Δ
coassoc = begin
  (Δ ×₁ id) ∘ Δ            ≈⟨ ×₁∘Δ ⟩
  ⟨ Δ , id ⟩               ≈˘⟨ assocʳ∘⟨⟩ ⟩
  assocʳ ∘ ⟨ id , Δ ⟩      ≈˘⟨ refl⟩∘⟨ ×₁∘Δ ⟩
  assocʳ ∘ (id ×₁ Δ) ∘ Δ   ≈˘⟨ assoc ⟩
  (assocʳ ∘ (id ×₁ Δ)) ∘ Δ ∎

counitˡ : ⟨ ! , id {A} ⟩ ≈ (! ×₁ id) ∘ Δ
counitˡ = ⟺ ×₁∘Δ

counitʳ : ⟨ id {A} , ! ⟩ ≈ (id ×₁ !) ∘ Δ
counitʳ = ⟺ ×₁∘Δ

-- Cocommutative, and trivial at the unit: there, both π₁ and π₂ are the unique
-- map to the terminal object, so the diagonal and the unitor invert each other.

cocomm : swap ∘ Δ {A} ≈ Δ
cocomm = swap∘⟨⟩

inverse₁ : Δ {⊤} ∘ π₂ ≈ id
inverse₁ = begin
  Δ ∘ π₂      ≈⟨ Δ∘ ⟩
  ⟨ π₂ , π₂ ⟩ ≈⟨ ⟨⟩-congʳ !-unique₂ ⟩
  ⟨ π₁ , π₂ ⟩ ≈⟨ η ⟩
  id          ∎

inverse₂ : π₂ ∘ Δ {⊤} ≈ id
inverse₂ = project₂

-- Coherence with the tensor.  The five maps rearrange ⟨ ⟨ π₁ , π₁ ⟩ , ⟨ π₂ , π₂ ⟩ ⟩
-- into ⟨ ⟨ π₁ , π₂ ⟩ , ⟨ π₁ , π₂ ⟩ ⟩, which is the diagonal of a product.

preserves : assocʳ ∘ (id ×₁ assocˡ) ∘ (id ×₁ ((swap ×₁ id) ∘ assocʳ)) ∘ assocˡ ∘ (Δ {A} ×₁ Δ {B})
          ≈ Δ
preserves = begin
  assocʳ ∘ (id ×₁ assocˡ) ∘ (id ×₁ ((swap ×₁ id) ∘ assocʳ)) ∘ assocˡ ∘ (Δ ×₁ Δ)
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟨⟩-cong₂ Δ∘ Δ∘ ⟩
  assocʳ ∘ (id ×₁ assocˡ) ∘ (id ×₁ ((swap ×₁ id) ∘ assocʳ)) ∘ assocˡ ∘ ⟨ ⟨ π₁ , π₁ ⟩ , ⟨ π₂ , π₂ ⟩ ⟩
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assocˡ∘⟨⟩ ⟩
  assocʳ ∘ (id ×₁ assocˡ) ∘ (id ×₁ ((swap ×₁ id) ∘ assocʳ)) ∘ ⟨ π₁ , ⟨ π₁ , ⟨ π₂ , π₂ ⟩ ⟩ ⟩
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ×₁∘⟨⟩ ⟩
  assocʳ ∘ (id ×₁ assocˡ) ∘ ⟨ id ∘ π₁ , ((swap ×₁ id) ∘ assocʳ) ∘ ⟨ π₁ , ⟨ π₂ , π₂ ⟩ ⟩ ⟩
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟨⟩-cong₂ identityˡ (pullʳ assocʳ∘⟨⟩) ⟩
  assocʳ ∘ (id ×₁ assocˡ) ∘ ⟨ π₁ , (swap ×₁ id) ∘ ⟨ ⟨ π₁ , π₂ ⟩ , π₂ ⟩ ⟩
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟨⟩-congˡ (×₁∘⟨⟩ ○ ⟨⟩-cong₂ swap∘⟨⟩ identityˡ) ⟩
  assocʳ ∘ (id ×₁ assocˡ) ∘ ⟨ π₁ , ⟨ ⟨ π₂ , π₁ ⟩ , π₂ ⟩ ⟩
    ≈⟨ refl⟩∘⟨ ×₁∘⟨⟩ ⟩
  assocʳ ∘ ⟨ id ∘ π₁ , assocˡ ∘ ⟨ ⟨ π₂ , π₁ ⟩ , π₂ ⟩ ⟩
    ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ identityˡ assocˡ∘⟨⟩ ⟩
  assocʳ ∘ ⟨ π₁ , ⟨ π₂ , ⟨ π₁ , π₂ ⟩ ⟩ ⟩
    ≈⟨ assocʳ∘⟨⟩ ⟩
  ⟨ ⟨ π₁ , π₂ ⟩ , ⟨ π₁ , π₂ ⟩ ⟩
    ≈⟨ ⟨⟩-cong₂ η η ⟩
  Δ ∎

gsMonoidal : GSMonoidal (symmetric 𝒞 cartesian)
gsMonoidal = record
  { isComonoid    = λ _ → record
    { μ         = Δ
    ; η         = !
    ; assoc     = coassoc
    ; identityˡ = counitˡ
    ; identityʳ = counitʳ
    }
  ; inverse₁      = inverse₁
  ; inverse₂      = inverse₂
  ; cocommutative = cocomm
  ; preserves     = preserves
  }

-- Every morphism is total, the counit being the terminal map.  Half the
-- distance from gs-monoidal back to cartesian; the other half is that every
-- morphism is deterministic, which is Cartesian.CounitalCopy.

open GSMonoidal gsMonoidal using (Total)

total : (f : A ⇒ B) → Total f
total _ = !-unique₂
