{-# OPTIONS --without-K --safe #-}

-- Mentioned in passing https://ncatlab.org/nlab/show/slice+2-category

open import Categories.Bicategory using (Bicategory)

module Categories.Bicategory.Construction.LaxSlice
       {o ℓ e t}
       (𝒞 : Bicategory o ℓ e t)
       where

open import Categories.Category using () renaming (Category to 1Category)
import Categories.Morphism.Reasoning as MR
open import Categories.Bicategory.Extras 𝒞
open Shorthands

open import Categories.Functor.Construction.Constant using (const)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; niHelper)
open import Function using (_$_)
open import Data.Product using (_,_)
open import Categories.Functor using (Functor)
open Functor using (F₀)

open import Level using (_⊔_)

record SliceObj (X : Obj) : Set (t ⊔ o) where
  constructor sliceobj
  field
    {Y} : Obj
    arr : Y ⇒₁ X

module SliceHom (A : Obj) where

  record Slice⇒₁ (X Y : SliceObj A) : Set (o ⊔ ℓ) where
    constructor slicearr₁
    private
      module X = SliceObj X
      module Y = SliceObj Y

    field
      {h} : X.Y ⇒₁ Y.Y
      Δ   : X.arr ⇒₂ (Y.arr ∘ₕ h)

  record Slice⇒₂ {X Y : SliceObj A} (J K : Slice⇒₁ X Y) : Set (ℓ ⊔ e) where
    constructor slicearr₂
    private
      module Y = SliceObj Y
      module J = Slice⇒₁ J
      module K = Slice⇒₁ K

    field
      {ϕ} : J.h ⇒₂ K.h
      E   : K.Δ ≈ (Y.arr ▷ ϕ ∘ᵥ J.Δ)

  _∘ᵥ/_ : ∀ {X Y : SliceObj A}{J K L : Slice⇒₁ X Y} → Slice⇒₂ K L → Slice⇒₂ J K → Slice⇒₂ J L
  _∘ᵥ/_ {X}{Y}{J}{K}{L} (slicearr₂ {ϕ = ϕ} E) (slicearr₂ {ϕ = ψ} F) = slicearr₂ {ϕ = ϕ ∘ᵥ ψ} $ begin
      L.Δ                             ≈⟨ E ⟩
      (Y.arr ▷ ϕ ∘ᵥ K.Δ)              ≈⟨ refl⟩∘⟨ F ⟩
      Y.arr ▷ ϕ ∘ᵥ (Y.arr ▷ ψ ∘ᵥ J.Δ) ≈⟨ pullˡ ∘ᵥ-distr-▷ ⟩
      Y.arr ▷ (ϕ ∘ᵥ ψ) ∘ᵥ J.Δ         ∎
    where module X = SliceObj X
          module Y = SliceObj Y
          module J = Slice⇒₁ J
          module K = Slice⇒₁ K
          module L = Slice⇒₁ L
          open 1Category (hom X.Y A)
          open HomReasoning
          open Equiv
          open MR (hom X.Y A)
          
  SliceHomCat : SliceObj A → SliceObj A → 1Category (o ⊔ ℓ) (ℓ ⊔ e) e
  SliceHomCat X Y = record
    { Obj = Slice⇒₁ X Y
    ; _⇒_ = Slice⇒₂
    ; _≈_ = λ (slicearr₂ {ϕ} _) (slicearr₂ {ψ} _) → ϕ ≈ ψ 
    ; id = slice-id _
    ; _∘_ = _∘ᵥ/_
    ; assoc = hom.assoc
    ; sym-assoc = hom.sym-assoc
    ; identityˡ = hom.identityˡ
    ; identityʳ = hom.identityʳ
    ; identity² = hom.identity²
    ; equiv = record
      { refl = refl
      ; sym = sym
      ; trans = trans }
    ; ∘-resp-≈ = hom.∘-resp-≈
    }
    where
      open hom.Equiv
      module X = SliceObj X
      module Y = SliceObj Y

      slice-id : ∀ (J : Slice⇒₁ X Y) → Slice⇒₂ J J
      slice-id J = slicearr₂ $ begin
        J.Δ                 ≈˘⟨ identity₂ˡ ⟩
        id₂ ∘ᵥ J.Δ          ≈˘⟨ ▷id₂ ⟩∘⟨refl ⟩
        (Y.arr ▷ id₂) ∘ J.Δ ∎
        where module J = Slice⇒₁ J
              open 1Category (hom X.Y A)
              open HomReasoning

  _⊚₀/_ : ∀ {X Y Z : SliceObj A} → Slice⇒₁ Y Z → Slice⇒₁ X Y → Slice⇒₁ X Z
  _⊚₀/_ {X}{Y}{Z} J K = slicearr₁ ((α⇒ ∘ᵥ J.Δ ◁ K.h) ∘ᵥ K.Δ)
    where module K = Slice⇒₁ K
          module J = Slice⇒₁ J
  
  _⊚₁/_ : ∀ {X Y Z : SliceObj A} → {J J' : Slice⇒₁ Y Z} → {K K' : Slice⇒₁ X Y} → Slice⇒₂ J J' → Slice⇒₂ K K' → Slice⇒₂ (J ⊚₀/ K) (J' ⊚₀/ K')
  _⊚₁/_ {X}{Y}{Z}{J'}{J}{K'}{K} δ γ = slicearr₂ $ begin
    (α⇒ ∘ᵥ J.Δ ◁ K.h) ∘ᵥ K.Δ                                                  ≈⟨ (refl⟩∘⟨ γ.E) ⟩
    (α⇒ ∘ᵥ J.Δ ◁ K.h) ∘ᵥ (Y.arr ▷ γ.ϕ ∘ᵥ K'.Δ)                                ≈⟨ ((refl⟩∘⟨ δ.E ⟩⊚⟨refl) ⟩∘⟨refl) ⟩
    (α⇒ ∘ᵥ (Z.arr ▷ δ.ϕ ∘ᵥ J'.Δ) ◁ K.h) ∘ᵥ (Y.arr ▷ γ.ϕ ∘ᵥ K'.Δ)              ≈˘⟨ (((refl⟩∘⟨ ∘ᵥ-distr-◁ ) ⟩∘⟨refl)) ⟩
    (α⇒ ∘ᵥ ((Z.arr ▷ δ.ϕ) ◁ K.h ∘ᵥ J'.Δ ◁ K.h)) ∘ᵥ (Y.arr ▷ γ.ϕ ∘ᵥ K'.Δ)      ≈⟨ pullʳ (center (sym ◁-▷-exchg)) ⟩
    α⇒ ∘ᵥ (Z.arr ▷ δ.ϕ) ◁ K.h ∘ᵥ (Z.arr ⊚₀ J'.h ▷ γ.ϕ ∘ᵥ J'.Δ ◁ K'.h) ∘ᵥ K'.Δ ≈⟨ pushʳ ( pullˡ (pullˡ (sym ⊚.homomorphism)) ) ⟩
    (α⇒ ∘ᵥ (Z.arr ▷ δ.ϕ ∘ᵥ id₂) ⊚₁ (id₂ ∘ᵥ γ.ϕ) ∘ᵥ J'.Δ ◁ K'.h) ∘ᵥ K'.Δ       ≈⟨ ((refl⟩∘⟨ (identity₂ʳ ⟩⊚⟨ identity₂ˡ ⟩∘⟨refl)) ⟩∘⟨refl) ⟩
    (α⇒ ∘ᵥ ((Z.arr ▷ δ.ϕ) ⊚₁ γ.ϕ) ∘ᵥ J'.Δ ◁ K'.h) ∘ᵥ K'.Δ                     ≈⟨ pushˡ (pullˡ (⊚-assoc.⇒.commute ((id₂ , δ.ϕ) , γ.ϕ))) ⟩
    (Z.arr ▷ δ.ϕ ⊚₁ γ.ϕ ∘ᵥ α⇒) ∘ᵥ J'.Δ ◁ K'.h ∘ᵥ K'.Δ                         ≈⟨ pullʳ (sym assoc) ⟩
    (Z.arr ▷ δ.ϕ ⊚₁ γ.ϕ) ∘ᵥ ((α⇒ ∘ᵥ J'.Δ ◁ K'.h) ∘ᵥ K'.Δ)                     ∎
    where module X = SliceObj X
          module Y = SliceObj Y
          module Z = SliceObj Z
          module J = Slice⇒₁ J
          module J' = Slice⇒₁ J'
          module K = Slice⇒₁ K
          module K' = Slice⇒₁ K'
          module γ = Slice⇒₂ γ
          module δ = Slice⇒₂ δ          
          open 1Category (hom X.Y A)
          open HomReasoning
          open MR (hom X.Y A)
          open Equiv

  id/ : ∀ {X : SliceObj A} → Slice⇒₁ X X
  id/ = slicearr₁ ρ⇐

  _⊚/_ : ∀ {X Y Z : SliceObj A} → Bifunctor (SliceHomCat Y Z) (SliceHomCat X Y) (SliceHomCat X Z)
  _⊚/_ {X}{Y}{Z} = record
    { F₀ = λ (J , K) → J ⊚₀/ K
    ; F₁ = λ (δ , γ) → δ ⊚₁/ γ
      ; identity = ⊚.identity
      ; homomorphism = ⊚.homomorphism
      ; F-resp-≈ = ⊚.F-resp-≈
      }
      where module X = SliceObj X
            module Y = SliceObj Y
            module Z = SliceObj Z
  
  α⇒/ : ∀ {W X Y Z}(H : Slice⇒₁ Y Z) (J : Slice⇒₁ X Y) (K : Slice⇒₁ W X) → Slice⇒₂ ((H ⊚₀/ J) ⊚₀/ K) (H ⊚₀/ (J ⊚₀/ K))
  α⇒/ {W}{X}{Y}{Z} H J K = slicearr₂ $ begin
    (α⇒ ∘ᵥ H.Δ ◁ J.h ⊚₀ K.h) ∘ᵥ ((α⇒ ∘ᵥ J.Δ ◁ K.h) ∘ᵥ K.Δ  )                  ≈⟨ pullʳ (center⁻¹ (sym α⇒-◁-∘ₕ) refl) ⟩
    α⇒ ∘ᵥ (α⇒ ∘ᵥ H.Δ ◁ J.h ◁ K.h) ∘ᵥ J.Δ ◁ K.h ∘ᵥ K.Δ                         ≈⟨ pullˡ (pullˡ (sym pentagon)) ⟩
    ((Z.arr ▷ α⇒ ∘ᵥ α⇒ ∘ᵥ α⇒ ◁ K.h) ∘ᵥ H.Δ ◁ J.h ◁ K.h) ∘ᵥ (J.Δ ◁ K.h ∘ᵥ K.Δ) ≈⟨ pullˡ (pushˡ (pull-last ∘ᵥ-distr-◁ )) ⟩
    (Z.arr ▷ α⇒ ∘ᵥ (α⇒ ∘ᵥ ((α⇒ ∘ᵥ H.Δ ◁ J.h) ◁ K.h)) ∘ᵥ J.Δ ◁ K.h) ∘ᵥ K.Δ     ≈⟨ pushˡ (pushʳ (pullʳ ∘ᵥ-distr-◁)) ⟩
    ((Z.arr ▷ α⇒ ∘ᵥ α⇒)) ∘ᵥ (((α⇒ ∘ᵥ H.Δ ◁ J.h) ∘ᵥ J.Δ) ◁ K.h) ∘ᵥ K.Δ         ≈⟨ pullʳ (pushʳ refl) ⟩
    Z.arr ▷ α⇒ ∘ᵥ ((α⇒ ∘ᵥ (((α⇒ ∘ᵥ H.Δ ◁ J.h)) ∘ᵥ J.Δ) ◁ K.h) ∘ᵥ K.Δ)         ∎
    where module W = SliceObj W
          module X = SliceObj X
          module Y = SliceObj Y
          module Z = SliceObj Z
          module H = Slice⇒₁ H
          module J = Slice⇒₁ J
          module K = Slice⇒₁ K
          open 1Category (hom W.Y A)
          open HomReasoning
          open MR (hom W.Y A)
          open hom.Equiv

  λ⇒/ : ∀ {X Y} (H : Slice⇒₁ X Y) → Slice⇒₂ (id/ ⊚₀/ H) H
  λ⇒/ {X}{Y} H = slicearr₂ $ begin
    H.Δ                                   ≈⟨ introˡ id₂◁ ⟩
    (id₂ ◁ H.h) ∘ᵥ H.Δ                    ≈˘⟨ (unitʳ.iso.isoʳ (Y.arr , _) ⟩⊚⟨refl ⟩∘⟨refl) ⟩
    ((ρ⇒ ∘ᵥ ρ⇐) ◁ H.h) ∘ᵥ H.Δ             ≈˘⟨ (∘ᵥ-distr-◁ ⟩∘⟨refl) ⟩
    (ρ⇒ ◁ H.h ∘ᵥ ρ⇐ ◁ H.h) ∘ᵥ H.Δ         ≈⟨ pushˡ (sym triangle ⟩∘⟨ refl) ⟩
    (Y.arr ▷ λ⇒ ∘ᵥ α⇒) ∘ᵥ ρ⇐ ◁ H.h ∘ᵥ H.Δ ≈⟨ pullʳ (sym assoc) ⟩
    Y.arr ▷ λ⇒ ∘ᵥ (α⇒ ∘ᵥ ρ⇐ ◁ H.h) ∘ᵥ H.Δ ∎
    where module X = SliceObj X
          module Y = SliceObj Y
          module H = Slice⇒₁ H
          open 1Category (hom X.Y A)
          open HomReasoning
          open MR (hom X.Y A)
          open hom.Equiv

  ρ⇒/ : ∀{X}{Y} (H : Slice⇒₁ X Y) → Slice⇒₂ (H ⊚₀/ id/) H
  ρ⇒/ {X}{Y} H = slicearr₂ $ begin
    H.Δ                                     ≈⟨ introʳ (unitʳ.iso.isoʳ _) ⟩
    H.Δ ∘ᵥ ρ⇒ ∘ᵥ ρ⇐                         ≈⟨ pullˡ (sym ρ⇒-∘ᵥ-◁) ⟩
    (ρ⇒ ∘ᵥ H.Δ ◁ id₁) ∘ᵥ ρ⇐                 ≈⟨ unitorʳ-coherence  ⟩∘⟨refl ⟩∘⟨refl ⟩
    ((Y.arr ▷ ρ⇒ ∘ᵥ α⇒) ∘ᵥ H.Δ ◁ id₁) ∘ᵥ ρ⇐ ≈⟨ pushˡ assoc ⟩
    Y.arr ▷ ρ⇒ ∘ᵥ (α⇒ ∘ᵥ H.Δ ◁ id₁) ∘ᵥ ρ⇐   ∎
    where module X = SliceObj X
          module Y = SliceObj Y
          module H = Slice⇒₁ H
          open 1Category (hom X.Y A)
          open HomReasoning
          open MR (hom X.Y A)
          open hom.Equiv

  slice-inv : ∀ {X}{Y}{H : Slice⇒₁ X Y}{K} (α : Slice⇒₂ H K) → (f : Slice⇒₁.h K ⇒₂ Slice⇒₁.h H) → (f ∘ᵥ (Slice⇒₂.ϕ α) ≈ id₂) → Slice⇒₂ K H
  slice-inv {X}{Y}{H}{K} α f p = slicearr₂ $ begin
    H.Δ                               ≈⟨ introˡ ▷id₂ ⟩
    (Y.arr ▷ id₂) ∘ᵥ H.Δ              ≈˘⟨ (refl⟩⊚⟨ p ⟩∘⟨refl) ⟩
    (Y.arr ▷ (f ∘ᵥ α.ϕ)) ∘ᵥ H.Δ       ≈˘⟨ (∘ᵥ-distr-▷ ⟩∘⟨refl) ⟩
    (Y.arr ▷ f ∘ᵥ Y.arr ▷ α.ϕ) ∘ᵥ H.Δ ≈⟨ pullʳ (sym α.E) ⟩
    Y.arr ▷ f ∘ᵥ K.Δ                  ∎
    where module X = SliceObj X
          module Y = SliceObj Y
          module H = Slice⇒₁ H
          module K = Slice⇒₁ K
          module α = Slice⇒₂ α          
          open 1Category (hom X.Y A)
          open HomReasoning
          open MR (hom X.Y A)
          open hom.Equiv

LaxSlice : Obj → Bicategory (o ⊔ ℓ) (ℓ ⊔ e) e (o ⊔ t)
LaxSlice A   = record
  { enriched = record
    { Obj = SliceObj A
    ; hom = SliceHomCat
    ; id = const id/
    ; ⊚ = _⊚/_
    ; ⊚-assoc = niHelper (record
      { η       = λ ((H , J) , K) → α⇒/ H J K
      ; η⁻¹     = λ ((H , J) , K) → slice-inv (α⇒/ H J K) α⇐ (⊚-assoc.iso.isoˡ _)
      ; commute = λ f → ⊚-assoc.⇒.commute _
      ; iso = λ HJK → record { isoˡ = ⊚-assoc.iso.isoˡ _ ; isoʳ = ⊚-assoc.iso.isoʳ _ }
      })
    ; unitˡ = niHelper (record
      { η       = λ (i , H) → λ⇒/ H
      ; η⁻¹     = λ (i , H) → slice-inv (λ⇒/ H) λ⇐ (unitˡ.iso.isoˡ _)
      ; commute = λ f → λ⇒-∘ᵥ-▷
      ; iso     = λ iH → record { isoˡ = unitˡ.iso.isoˡ _ ; isoʳ = unitˡ.iso.isoʳ _ }
      })
    ; unitʳ = niHelper (record
         { η       = λ (H , i) → ρ⇒/ H
         ; η⁻¹     = λ (H , i) → slice-inv (ρ⇒/ H) ρ⇐ (unitʳ.iso.isoˡ _)
         ; commute = λ f → ρ⇒-∘ᵥ-◁
         ; iso     = λ Hi → record { isoˡ = unitʳ.iso.isoˡ _ ; isoʳ = unitʳ.iso.isoʳ _ } })
    }
  ; triangle = triangle
  ; pentagon = pentagon
  }
  where open SliceHom A
