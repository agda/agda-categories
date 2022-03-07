{-# OPTIONS --without-K --safe #-}

-- Mentioned in passing https://ncatlab.org/nlab/show/slice+2-category

open import Categories.Bicategory

module Categories.Bicategory.Construction.LaxSlice
       {o ℓ e t}
       (𝒞 : Bicategory o ℓ e t)
       where

open import Categories.Enriched.Category
open import Categories.Category renaming (Category to 1Category)
open import Categories.Morphism.Reasoning

open import Categories.Bicategory.Extras 𝒞

open import Level

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

  record Slice⇒₂ {X Y : SliceObj A} (H K : Slice⇒₁ X Y) : Set (ℓ ⊔ e) where
    constructor slicearr₂
    private
      module Y = SliceObj Y
      module H = Slice⇒₁ H
      module K = Slice⇒₁ K

    field
      {ϕ} : H.h ⇒₂ K.h
      E   : K.Δ ≈ (Y.arr ▷ ϕ ∘ᵥ H.Δ)

  open hom.Equiv
  open import Categories.Functor using (Functor)

  _∘'_ : ∀ {X Y : SliceObj A}{H K L : Slice⇒₁ X Y} → Slice⇒₂ K L → Slice⇒₂ H K → Slice⇒₂ H L
  _∘'_ {X}{Y}{H}{K}{L} (slicearr₂ {ϕ = ϕ} E) (slicearr₂ {ϕ = ψ} F) = slicearr₂ {ϕ = ϕ ∘ᵥ ψ} 
     (begin
      L.Δ ≈⟨ E ⟩
      (Y.arr ▷ ϕ ∘ᵥ K.Δ) ≈⟨ refl⟩∘⟨ F ⟩
      Y.arr ▷ ϕ ∘ᵥ (Y.arr ▷ ψ ∘ᵥ H.Δ) ≈˘⟨ hom.assoc ⟩
      (Y.arr ▷ ϕ ∘ᵥ Y.arr ▷ ψ) ∘ᵥ H.Δ ≈⟨ (∘ᵥ-distr-▷ ⟩∘⟨refl) ⟩
      Y.arr ▷ (ϕ ∘ᵥ ψ) ∘ᵥ H.Δ ∎
        )
    where module X = SliceObj X
          module Y = SliceObj Y
          module H = Slice⇒₁ H
          module K = Slice⇒₁ K
          module L = Slice⇒₁ L
          open 1Category (hom X.Y A)
          open HomReasoning
          open Equiv
          open import Categories.Morphism.Reasoning (hom X.Y A)
          open import Relation.Binary.Core using (Rel)
          open import Function.Base using (_$_)
          
  open SliceObj
  SliceHomCat : SliceObj A → SliceObj A → 1Category (o ⊔ ℓ) (ℓ ⊔ e) e
  SliceHomCat X Y = record
    { Obj = Slice⇒₁ X Y
    ; _⇒_ = Slice⇒₂
    ; _≈_ = λ where
      (slicearr₂ {ϕ} _) (slicearr₂ {ψ} _) → ϕ ≈ ψ 
    ; id = slice-id _
    ; _∘_ = _∘'_
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
      slice-id : ∀ (H : Slice⇒₁ X Y) → Slice⇒₂ H H
      slice-id H = slicearr₂ (begin
        (H.Δ        ≈˘⟨ identity₂ˡ ⟩
         id₂ ∘ᵥ H.Δ ≈⟨ (sym ▷id₂ ⟩∘⟨refl) ⟩
         (arr Y ▷ id₂) ∘ H.Δ
         ∎))
        where module X = SliceObj X
              module H = Slice⇒₁ H
              open 1Category (hom X.Y A)
              open HomReasoning

LaxSlice : Obj → Bicategory (o ⊔ ℓ) (ℓ ⊔ e) e (o ⊔ t)
LaxSlice A   = record
  { enriched = record
    { Obj = SliceObj A
    ; hom = SliceHomCat
    ; id = const (SliceHom.slicearr₁ ρ⇐)
    ; ⊚ = _⊚'_
    ; ⊚-assoc = λ {W X Y Z} →
      let module W = SliceObj W
          module X = SliceObj X
          module Y = SliceObj Y
          module Z = SliceObj Z
          η' : ∀ (H : Slice⇒₁ Y Z) (J : Slice⇒₁ X Y) (K : Slice⇒₁ W X) → Slice⇒₂ ((F₀ _⊚'_ (F₀ _⊚'_ (H , J) , K))) (F₀ _⊚'_ (H  , F₀ _⊚'_ (J , K)))
          η' H J K =
            let module H = Slice⇒₁ H
                module J = Slice⇒₁ J
                module K = Slice⇒₁ K
                open 1Category (hom W.Y A)
                open HomReasoning
                module Help = Categories.Morphism.Reasoning (hom W.Y A)
            in SliceHom.slicearr₂ (begin (
              Slice⇒₁.Δ (F₀ _⊚'_ (H  , F₀ _⊚'_ (J , K))) ≈⟨ Equiv.refl ⟩
              (α⇒ ∘ᵥ H.Δ ◁ J.h ⊚₀ K.h) ∘ᵥ ((α⇒ ∘ᵥ J.Δ ◁ K.h) ∘ᵥ K.Δ) ≈⟨ (refl⟩∘⟨ assoc) ⟩
              (α⇒ ∘ᵥ H.Δ ◁ J.h ⊚₀ K.h) ∘ᵥ α⇒ ∘ᵥ (J.Δ ◁ K.h ∘ᵥ K.Δ)   ≈˘⟨ assoc ⟩
              ((α⇒ ∘ᵥ H.Δ ◁ J.h ⊚₀ K.h) ∘ᵥ α⇒) ∘ᵥ (J.Δ ◁ K.h ∘ᵥ K.Δ) ≈⟨ (assoc ⟩∘⟨refl) ⟩
              (α⇒ ∘ᵥ (H.Δ ◁ J.h ⊚₀ K.h ∘ᵥ α⇒)) ∘ᵥ (J.Δ ◁ K.h ∘ᵥ K.Δ) ≈⟨ assoc ⟩

              α⇒ ∘ᵥ (H.Δ ◁ J.h ⊚₀ K.h ∘ᵥ α⇒) ∘ᵥ (J.Δ ◁ K.h ∘ᵥ K.Δ)                    ≈˘⟨ (refl⟩∘⟨ (α⇒-◁-∘ₕ  ⟩∘⟨refl)) ⟩
  
              α⇒ ∘ᵥ (α⇒ ∘ᵥ H.Δ ◁ J.h ◁ K.h) ∘ᵥ (J.Δ ◁ K.h ∘ᵥ K.Δ)                     ≈⟨ Equiv.sym assoc ⟩
              (α⇒ ∘ᵥ (α⇒ ∘ᵥ H.Δ ◁ J.h ◁ K.h)) ∘ᵥ (J.Δ ◁ K.h ∘ᵥ K.Δ)                   ≈˘⟨ ( assoc ⟩∘⟨refl) ⟩
              ((α⇒ ∘ᵥ α⇒) ∘ᵥ H.Δ ◁ J.h ◁ K.h) ∘ᵥ (J.Δ ◁ K.h ∘ᵥ K.Δ)                   ≈⟨ assoc ⟩

              (α⇒ ∘ᵥ α⇒) ∘ᵥ H.Δ ◁ J.h ◁ K.h ∘ᵥ (J.Δ ◁ K.h ∘ᵥ K.Δ)                     ≈˘⟨ (pentagon ⟩∘⟨refl) ⟩
  
              (Z.arr ▷ α⇒ ∘ᵥ α⇒ ∘ᵥ α⇒ ◁ K.h) ∘ᵥ H.Δ ◁ J.h ◁ K.h ∘ᵥ (J.Δ ◁ K.h ∘ᵥ K.Δ) ≈⟨ Help.assoc²' ⟩
              Z.arr ▷ α⇒ ∘ᵥ α⇒ ∘ᵥ α⇒ ◁ K.h ∘ᵥ H.Δ ◁ J.h ◁ K.h ∘ᵥ (J.Δ ◁ K.h ∘ᵥ K.Δ)   ≈⟨ (refl⟩∘⟨ (refl⟩∘⟨ Equiv.sym assoc)) ⟩

              Z.arr ▷ α⇒ ∘ᵥ α⇒ ∘ᵥ (α⇒ ◁ K.h ∘ᵥ H.Δ ◁ J.h ◁ K.h) ∘ᵥ (J.Δ ◁ K.h ∘ᵥ K.Δ) ≈⟨ (refl⟩∘⟨ (refl⟩∘⟨ (∘ᵥ-distr-◁ ⟩∘⟨refl))) ⟩
              Z.arr ▷ α⇒ ∘ᵥ α⇒ ∘ᵥ ((α⇒ ∘ᵥ H.Δ ◁ J.h) ◁ K.h) ∘ᵥ (J.Δ ◁ K.h ∘ᵥ K.Δ)     ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ Equiv.sym assoc) ⟩
              Z.arr ▷ α⇒ ∘ᵥ α⇒ ∘ᵥ ((α⇒ ∘ᵥ H.Δ ◁ J.h) ◁ K.h ∘ᵥ J.Δ ◁ K.h) ∘ᵥ K.Δ       ≈⟨ (refl⟩∘⟨ (refl⟩∘⟨ (∘ᵥ-distr-◁  ⟩∘⟨refl))) ⟩
              -- assoc/lifted assoc
              Z.arr ▷ α⇒ ∘ᵥ α⇒ ∘ᵥ (((α⇒ ∘ᵥ H.Δ ◁ J.h) ∘ᵥ J.Δ) ◁ K.h) ∘ᵥ K.Δ           ≈⟨ (refl⟩∘⟨ Equiv.sym assoc) ⟩

              Z.arr ▷ α⇒ ∘ᵥ ((α⇒ ∘ᵥ (((α⇒ ∘ᵥ H.Δ ◁ J.h)) ∘ᵥ J.Δ) ◁ K.h) ∘ᵥ K.Δ)       ≈⟨ Equiv.refl ⟩
              Z.arr ▷ α⇒ ∘ᵥ Slice⇒₁.Δ (F₀ _⊚'_ (F₀ _⊚'_ (H , J) , K))
              ∎))
      in 
      niHelper (record
      { η       = λ ((H , J) , K) → η' H J K
      ; η⁻¹     = λ where
        ((H , J) , K) →
          let module H = Slice⇒₁ H
              module J = Slice⇒₁ J
              module K = Slice⇒₁ K
              open 1Category (hom W.Y A)
              open HomReasoning
          in
          SliceHom.slicearr₂ 
            (begin (
            Slice⇒₁.Δ (F₀ _⊚'_ (F₀ _⊚'_ (H , J) , K))         ≈˘⟨ identity₂ˡ ⟩
            id₂ ∘ᵥ (Slice⇒₁.Δ (F₀ _⊚'_ (F₀ _⊚'_ (H , J) , K))) ≈⟨ (Equiv.sym ▷id₂ ⟩∘⟨refl) ⟩
            (Z.arr ▷ id₂) ∘ᵥ (Slice⇒₁.Δ (F₀ _⊚'_ (F₀ _⊚'_ (H , J) , K))) ≈˘⟨ (refl⟩⊚⟨ ⊚-assoc.iso.isoˡ ((H.h , J.h) , K.h) ⟩∘⟨refl) ⟩
            (Z.arr ▷ (α⇐ ∘ᵥ α⇒)) ∘ᵥ (Slice⇒₁.Δ (F₀ _⊚'_ (F₀ _⊚'_ (H , J) , K))) ≈˘⟨ (∘ᵥ-distr-▷ ⟩∘⟨refl) ⟩
            (Z.arr ▷ α⇐ ∘ᵥ Z.arr ▷ α⇒) ∘ᵥ (Slice⇒₁.Δ (F₀ _⊚'_ (F₀ _⊚'_ (H , J) , K))) ≈⟨ assoc ⟩
            Z.arr ▷ α⇐ ∘ᵥ Z.arr ▷ α⇒ ∘ᵥ (Slice⇒₁.Δ (F₀ _⊚'_ (F₀ _⊚'_ (H , J) , K))) ≈˘⟨ (refl⟩∘⟨ Slice⇒₂.E (η' H J K)) ⟩
            Z.arr ▷ α⇐ ∘ᵥ Slice⇒₁.Δ (F₀ _⊚'_ (H  , F₀ _⊚'_ (J , K)))
            ∎))

      ; commute = λ where
        {(H , J) , K} {(H' , J') , K'} (( β , γ ) , δ) →
          let module β = Slice⇒₂ β
              module γ = Slice⇒₂ γ
              module δ = Slice⇒₂ δ
          in ⊚-assoc.⇒.commute (((β.ϕ , γ.ϕ) , δ.ϕ))
      ; iso = λ where
         ((H , J) , K) →
          let module H = Slice⇒₁ H
              module J = Slice⇒₁ J
              module K = Slice⇒₁ K
          in record { isoˡ = ⊚-assoc.iso.isoˡ ((H.h , J.h) , K.h) ; isoʳ = ⊚-assoc.iso.isoʳ ( (H.h , J.h) , K.h) }
      })
    ; unitˡ = λ {X}{Y} →
      let module X = SliceObj X
          module Y = SliceObj Y
          λ⇒/ : ∀ (H : Slice⇒₁ X Y) → Slice⇒₂ (F₀ _⊚'_ (SliceHom.slicearr₁ ρ⇐ , H)) H
          λ⇒/ H =
            let module H = Slice⇒₁ H
                open 1Category (hom X.Y A)
                open HomReasoning
                open Equiv
            in SliceHom.slicearr₂ (begin (
              H.Δ                                   ≈˘⟨ identity₂ˡ ⟩
              id₂ ∘ᵥ H.Δ                            ≈˘⟨ (id₂◁ ⟩∘⟨refl) ⟩
              (id₂ ◁ H.h) ∘ᵥ H.Δ                    ≈˘⟨ (unitʳ.iso.isoʳ (Y.arr , (lift _)) ⟩⊚⟨refl ⟩∘⟨refl) ⟩
              ((ρ⇒ ∘ᵥ ρ⇐) ◁ H.h) ∘ᵥ H.Δ             ≈˘⟨ (∘ᵥ-distr-◁ ⟩∘⟨refl) ⟩
              (ρ⇒ ◁ H.h ∘ᵥ ρ⇐ ◁ H.h) ∘ᵥ H.Δ         ≈⟨ assoc ⟩
              ρ⇒ ◁ H.h ∘ᵥ ρ⇐ ◁ H.h ∘ᵥ H.Δ           ≈˘⟨ (triangle ⟩∘⟨refl) ⟩
              (Y.arr ▷ λ⇒ ∘ᵥ α⇒) ∘ᵥ ρ⇐ ◁ H.h ∘ᵥ H.Δ ≈⟨ assoc ⟩
              Y.arr ▷ λ⇒ ∘ᵥ α⇒ ∘ᵥ ρ⇐ ◁ H.h ∘ᵥ H.Δ   ≈˘⟨ (refl⟩∘⟨ assoc) ⟩
              Y.arr ▷ λ⇒ ∘ᵥ (α⇒ ∘ᵥ ρ⇐ ◁ H.h) ∘ᵥ H.Δ ≈⟨ refl ⟩
              Y.arr ▷ λ⇒ ∘ᵥ Slice⇒₁.Δ (F₀ _⊚'_ (SliceHom.slicearr₁ ρ⇐ , H))
              ∎))
      in niHelper (record
      { η = λ where
          (i , H) → λ⇒/ H
      ; η⁻¹ = λ where
          (i , H) →
            let module H = Slice⇒₁ H
                open 1Category (hom X.Y A)
                open HomReasoning
                open Equiv
            in SliceHom.slicearr₂ (begin (
               Slice⇒₁.Δ (F₀ _⊚'_ (SliceHom.slicearr₁ ρ⇐ , H))                                   ≈˘⟨ identity₂ˡ ⟩
               (id₂ ∘ᵥ Slice⇒₁.Δ (F₀ _⊚'_ (SliceHom.slicearr₁ ρ⇐ , H)))                          ≈˘⟨ (▷id₂ ⟩∘⟨refl ) ⟩
               (Y.arr ▷ id₂) ∘ᵥ Slice⇒₁.Δ (F₀ _⊚'_ (SliceHom.slicearr₁ ρ⇐ , H))                  ≈˘⟨ (refl⟩⊚⟨ unitˡ.iso.isoˡ _ ⟩∘⟨refl) ⟩
               (Y.arr ▷ (λ⇐ ∘ᵥ λ⇒)) ∘ᵥ Slice⇒₁.Δ (F₀ _⊚'_ (SliceHom.slicearr₁ ρ⇐ , H))           ≈˘⟨ (∘ᵥ-distr-▷ ⟩∘⟨refl) ⟩
               ((Y.arr ▷ λ⇐) ∘ᵥ (Y.arr ▷ λ⇒)) ∘ᵥ Slice⇒₁.Δ (F₀ _⊚'_ (SliceHom.slicearr₁ ρ⇐ , H)) ≈⟨ assoc ⟩
               (Y.arr ▷ λ⇐) ∘ᵥ (Y.arr ▷ λ⇒) ∘ᵥ Slice⇒₁.Δ (F₀ _⊚'_ (SliceHom.slicearr₁ ρ⇐ , H))   ≈˘⟨ (refl⟩∘⟨ Slice⇒₂.E (λ⇒/ H)) ⟩
               Y.arr ▷ λ⇐ ∘ᵥ H.Δ
               ∎))
      ; commute = λ where
          {lift _ , SliceHom.slicearr₁ {Hh} HΔ} {lift _ , SliceHom.slicearr₁ {Jh} JΔ} (lift _ , SliceHom.slicearr₂ {ϕ} E) → λ⇒-∘ᵥ-▷
      ; iso = λ where
          (i , SliceHom.slicearr₁ {h} Δ) →
            record { isoˡ = unitˡ.iso.isoˡ (_ , h)
                   ; isoʳ = unitˡ.iso.isoʳ (_ , h) }
      })
    ; unitʳ = λ {X}{Y} →
      let module X = SliceObj X
          module Y = SliceObj Y
          ρ⇒/ : ∀ (H : Slice⇒₁ X Y) → Slice⇒₂ (F₀ _⊚'_ (H , SliceHom.slicearr₁ ρ⇐)) H
          ρ⇒/ H =
            let module H = Slice⇒₁ H
                open 1Category (hom X.Y A)
                open HomReasoning
                open Equiv
            in SliceHom.slicearr₂ (begin (
               H.Δ ≈˘⟨ identity₂ʳ ⟩
               H.Δ ∘ᵥ id₂ ≈˘⟨ refl⟩∘⟨ unitʳ.iso.isoʳ (X.arr , _) ⟩
               H.Δ ∘ᵥ ρ⇒ ∘ᵥ ρ⇐ ≈˘⟨ assoc ⟩
               (H.Δ ∘ᵥ ρ⇒) ∘ᵥ ρ⇐ ≈˘⟨ ρ⇒-∘ᵥ-◁ ⟩∘⟨refl ⟩
               (ρ⇒ ∘ᵥ H.Δ ◁ id₁) ∘ᵥ ρ⇐ ≈⟨ unitorʳ-coherence  ⟩∘⟨refl ⟩∘⟨refl ⟩
               ((Y.arr ▷ ρ⇒ ∘ᵥ α⇒) ∘ᵥ H.Δ ◁ id₁) ∘ᵥ ρ⇐ ≈⟨ assoc ⟩∘⟨refl ⟩
               (Y.arr ▷ ρ⇒ ∘ᵥ (α⇒ ∘ᵥ H.Δ ◁ id₁)) ∘ᵥ ρ⇐ ≈⟨ assoc ⟩
               Y.arr ▷ ρ⇒ ∘ᵥ (α⇒ ∘ᵥ H.Δ ◁ id₁) ∘ᵥ ρ⇐ ≈⟨ refl ⟩
               Y.arr ▷ ρ⇒ ∘ᵥ Slice⇒₁.Δ (F₀ _⊚'_ (H , SliceHom.slicearr₁ ρ⇐ ))
               ∎))
      in niHelper (record
         { η = λ (H , i) → ρ⇒/ H
         ; η⁻¹ = λ (H , i) →
            let module H = Slice⇒₁ H
                open 1Category (hom X.Y A)
                open HomReasoning
                open Equiv
            in SliceHom.slicearr₂ (begin (
               Slice⇒₁.Δ (F₀ _⊚'_ (H , SliceHom.slicearr₁ ρ⇐ )) ≈˘⟨ identity₂ˡ ⟩
               (id₂ ∘ᵥ Slice⇒₁.Δ (F₀ _⊚'_ (H , SliceHom.slicearr₁ ρ⇐ )))                          ≈˘⟨ (▷id₂ ⟩∘⟨refl ) ⟩
               (Y.arr ▷ id₂) ∘ᵥ Slice⇒₁.Δ (F₀ _⊚'_ (H , SliceHom.slicearr₁ ρ⇐))                   ≈˘⟨ (refl⟩⊚⟨ unitʳ.iso.isoˡ _ ⟩∘⟨refl) ⟩
               (Y.arr ▷ (ρ⇐ ∘ᵥ ρ⇒)) ∘ᵥ Slice⇒₁.Δ (F₀ _⊚'_ (H , SliceHom.slicearr₁ ρ⇐))            ≈˘⟨ (∘ᵥ-distr-▷ ⟩∘⟨refl) ⟩
               ((Y.arr ▷ ρ⇐) ∘ᵥ (Y.arr ▷ ρ⇒)) ∘ᵥ Slice⇒₁.Δ (F₀ _⊚'_ (H , SliceHom.slicearr₁ ρ⇐ )) ≈⟨ assoc ⟩
               (Y.arr ▷ ρ⇐) ∘ᵥ (Y.arr ▷ ρ⇒) ∘ᵥ Slice⇒₁.Δ (F₀ _⊚'_ (H , SliceHom.slicearr₁ ρ⇐))    ≈˘⟨ (refl⟩∘⟨ Slice⇒₂.E (ρ⇒/ H)) ⟩
               Y.arr ▷ ρ⇐ ∘ᵥ H.Δ
               ∎))
         ; commute = λ f → ρ⇒-∘ᵥ-◁
         ; iso = λ where
          ((SliceHom.slicearr₁ {h} Δ) , i) →
            record { isoˡ = unitʳ.iso.isoˡ (h , _)
                   ; isoʳ = unitʳ.iso.isoʳ (h , _) } })
    }
  ; triangle = λ {X}{Y}{Z}{H}{K} → triangle
  ; pentagon = λ {V} {W} {X} {Y} {Z} {H} {J} {K} {L} → pentagon
  }
  where
    open import Categories.NaturalTransformation.NaturalIsomorphism
      using (NaturalIsomorphism; niHelper)
    open SliceHom A
    open Shorthands
    open import Categories.Functor
    open Functor
    open import Categories.Functor.Construction.Constant
    
    open import Categories.Functor.Bifunctor

    open import Data.Product
    _⊚'_ : ∀ {X Y Z : SliceObj A} → Bifunctor (SliceHomCat Y Z) (SliceHomCat X Y) (SliceHomCat X Z)
    _⊚'_ {X}{Y}{Z} = record
             { F₀ = λ where
               (H' , H) →
                 let module H' = Slice⇒₁ H'
                     module H = Slice⇒₁ H
                 in SliceHom.slicearr₁ ((α⇒ ∘ᵥ H'.Δ ◁ H.h) ∘ᵥ H.Δ)
             ; F₁ = λ where
               {H' , H} {J' , J} (γ , δ) →
                 let module H' = Slice⇒₁ H'
                     module H = Slice⇒₁ H
                     module J' = Slice⇒₁ J'
                     module J = Slice⇒₁ J
                     module γ = Slice⇒₂ γ
                     module δ = Slice⇒₂ δ
                     open 1Category (hom X.Y A)
                     open HomReasoning
                 in SliceHom.slicearr₂ (begin
                   (α⇒ ∘ᵥ J'.Δ ◁ J.h) ∘ᵥ J.Δ ≈⟨ (refl⟩∘⟨ δ.E) ⟩
                   (α⇒ ∘ᵥ J'.Δ ◁ J.h) ∘ᵥ (Y.arr ▷ δ.ϕ ∘ᵥ H.Δ) ≈⟨ ((refl⟩∘⟨ γ.E ⟩⊚⟨refl) ⟩∘⟨refl) ⟩
                   (α⇒ ∘ᵥ (Z.arr ▷ γ.ϕ ∘ᵥ H'.Δ) ◁ J.h) ∘ᵥ (Y.arr ▷ δ.ϕ ∘ᵥ H.Δ) ≈˘⟨ (((refl⟩∘⟨ ∘ᵥ-distr-◁ ) ⟩∘⟨refl)) ⟩

                    -- generalized assoc
                   (α⇒ ∘ᵥ ((Z.arr ▷ γ.ϕ) ◁ J.h ∘ᵥ H'.Δ ◁ J.h)) ∘ᵥ (Y.arr ▷ δ.ϕ ∘ᵥ H.Δ) ≈˘⟨ assoc ⟩
                   ((α⇒ ∘ᵥ ((Z.arr ▷ γ.ϕ) ◁ J.h ∘ᵥ H'.Δ ◁ J.h)) ∘ᵥ Y.arr ▷ δ.ϕ) ∘ᵥ H.Δ ≈⟨ (assoc ⟩∘⟨refl) ⟩
                   (α⇒ ∘ᵥ ((Z.arr ▷ γ.ϕ) ◁ J.h ∘ᵥ H'.Δ ◁ J.h) ∘ᵥ Y.arr ▷ δ.ϕ) ∘ᵥ H.Δ ≈⟨ ((refl⟩∘⟨ assoc) ⟩∘⟨refl) ⟩
                   
                   (α⇒ ∘ᵥ (Z.arr ▷ γ.ϕ) ◁ J.h ∘ᵥ (H'.Δ ◁ J.h ∘ᵥ Y.arr ▷ δ.ϕ)) ∘ᵥ H.Δ ≈˘⟨ ((refl⟩∘⟨ (refl⟩∘⟨ ◁-▷-exchg)) ⟩∘⟨refl) ⟩

                    -- generalized assoc
                   (α⇒ ∘ᵥ (Z.arr ▷ γ.ϕ) ◁ J.h ∘ᵥ (Z.arr ⊚₀ H'.h ▷ δ.ϕ ∘ᵥ H'.Δ ◁ H.h)) ∘ᵥ H.Δ ≈˘⟨ ((refl⟩∘⟨ assoc) ⟩∘⟨refl) ⟩
                   (α⇒ ∘ᵥ ((Z.arr ▷ γ.ϕ) ◁ J.h ∘ᵥ Z.arr ⊚₀ H'.h ▷ δ.ϕ) ∘ᵥ H'.Δ ◁ H.h) ∘ᵥ H.Δ ≈˘⟨ (assoc ⟩∘⟨refl) ⟩
                   (((α⇒ ∘ᵥ (Z.arr ▷ γ.ϕ) ◁ J.h ∘ᵥ Z.arr ⊚₀ H'.h ▷ δ.ϕ)) ∘ᵥ H'.Δ ◁ H.h) ∘ᵥ H.Δ ≈⟨ assoc ⟩

                   (α⇒ ∘ᵥ (Z.arr ▷ γ.ϕ) ◁ J.h ∘ᵥ Z.arr ⊚₀ H'.h ▷ δ.ϕ) ∘ᵥ H'.Δ ◁ H.h ∘ᵥ H.Δ ≈˘⟨ ((refl⟩∘⟨ ⊚.homomorphism) ⟩∘⟨refl) ⟩
                   (α⇒ ∘ᵥ (Z.arr ▷ γ.ϕ ∘ᵥ id₂) ⊚₁ (id₂ ∘ᵥ δ.ϕ)) ∘ᵥ H'.Δ ◁ H.h ∘ᵥ H.Δ ≈⟨ ((refl⟩∘⟨ identity₂ʳ ⟩⊚⟨ identity₂ˡ) ⟩∘⟨refl) ⟩
                   (α⇒ ∘ᵥ (Z.arr ▷ γ.ϕ) ⊚₁ δ.ϕ) ∘ᵥ H'.Δ ◁ H.h ∘ᵥ H.Δ ≈⟨ (⊚-assoc.⇒.commute ((id₂ , γ.ϕ) , δ.ϕ) ⟩∘⟨refl) ⟩
                   ((Z.arr ▷ γ.ϕ ⊚₁ δ.ϕ) ∘ᵥ α⇒) ∘ᵥ H'.Δ ◁ H.h ∘ᵥ H.Δ ≈⟨ assoc ⟩
                   (Z.arr ▷ γ.ϕ ⊚₁ δ.ϕ) ∘ᵥ α⇒ ∘ᵥ H'.Δ ◁ H.h ∘ᵥ H.Δ ≈˘⟨ refl⟩∘⟨ assoc ⟩
                   (Z.arr ▷ γ.ϕ ⊚₁ δ.ϕ) ∘ᵥ ((α⇒ ∘ᵥ H'.Δ ◁ H.h) ∘ᵥ H.Δ)
                   ∎)
             ; identity = ⊚.identity
             ; homomorphism = ⊚.homomorphism
             ; F-resp-≈ = ⊚.F-resp-≈
             }
         where module X = SliceObj X
               module Y = SliceObj Y
               module Z = SliceObj Z
