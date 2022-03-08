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

  _∘'_ : ∀ {X Y : SliceObj A}{H K L : Slice⇒₁ X Y} → Slice⇒₂ K L → Slice⇒₂ H K → Slice⇒₂ H L
  _∘'_ {X}{Y}{H}{K}{L} (slicearr₂ {ϕ = ϕ} E) (slicearr₂ {ϕ = ψ} F) = slicearr₂ {ϕ = ϕ ∘ᵥ ψ} $ begin
      L.Δ                             ≈⟨ E ⟩
      (Y.arr ▷ ϕ ∘ᵥ K.Δ)              ≈⟨ refl⟩∘⟨ F ⟩
      Y.arr ▷ ϕ ∘ᵥ (Y.arr ▷ ψ ∘ᵥ H.Δ) ≈˘⟨ hom.assoc ⟩
      (Y.arr ▷ ϕ ∘ᵥ Y.arr ▷ ψ) ∘ᵥ H.Δ ≈⟨ (∘ᵥ-distr-▷ ⟩∘⟨refl) ⟩
      Y.arr ▷ (ϕ ∘ᵥ ψ) ∘ᵥ H.Δ         ∎
    where module X = SliceObj X
          module Y = SliceObj Y
          module H = Slice⇒₁ H
          module K = Slice⇒₁ K
          module L = Slice⇒₁ L
          open 1Category (hom X.Y A)
          open HomReasoning
          open Equiv
          open MR (hom X.Y A)
          
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
      slice-id H = slicearr₂ $ begin
        H.Δ                 ≈˘⟨ identity₂ˡ ⟩
        id₂ ∘ᵥ H.Δ          ≈⟨ (sym ▷id₂ ⟩∘⟨refl) ⟩
        (arr Y ▷ id₂) ∘ H.Δ ∎
        where module X = SliceObj X
              module H = Slice⇒₁ H
              open 1Category (hom X.Y A)
              open HomReasoning

  open Shorthands
  open Functor
  _⊚/_ : ∀ {X Y Z : SliceObj A} → Bifunctor (SliceHomCat Y Z) (SliceHomCat X Y) (SliceHomCat X Z)
  _⊚/_ {X}{Y}{Z} = record
    { F₀ = λ (H' , H) →
           let module H' = Slice⇒₁ H'
               module H = Slice⇒₁ H
           in slicearr₁ ((α⇒ ∘ᵥ H'.Δ ◁ H.h) ∘ᵥ H.Δ)
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
            in slicearr₂ $ begin
               (α⇒ ∘ᵥ J'.Δ ◁ J.h) ∘ᵥ J.Δ                                                   ≈⟨ (refl⟩∘⟨ δ.E) ⟩
               (α⇒ ∘ᵥ J'.Δ ◁ J.h) ∘ᵥ (Y.arr ▷ δ.ϕ ∘ᵥ H.Δ)                                  ≈⟨ ((refl⟩∘⟨ γ.E ⟩⊚⟨refl) ⟩∘⟨refl) ⟩
               (α⇒ ∘ᵥ (Z.arr ▷ γ.ϕ ∘ᵥ H'.Δ) ◁ J.h) ∘ᵥ (Y.arr ▷ δ.ϕ ∘ᵥ H.Δ)                 ≈˘⟨ (((refl⟩∘⟨ ∘ᵥ-distr-◁ ) ⟩∘⟨refl)) ⟩

                -- generalized assoc
               (α⇒ ∘ᵥ ((Z.arr ▷ γ.ϕ) ◁ J.h ∘ᵥ H'.Δ ◁ J.h)) ∘ᵥ (Y.arr ▷ δ.ϕ ∘ᵥ H.Δ)         ≈˘⟨ assoc ⟩
               ((α⇒ ∘ᵥ ((Z.arr ▷ γ.ϕ) ◁ J.h ∘ᵥ H'.Δ ◁ J.h)) ∘ᵥ Y.arr ▷ δ.ϕ) ∘ᵥ H.Δ         ≈⟨ (assoc ⟩∘⟨refl) ⟩
               (α⇒ ∘ᵥ ((Z.arr ▷ γ.ϕ) ◁ J.h ∘ᵥ H'.Δ ◁ J.h) ∘ᵥ Y.arr ▷ δ.ϕ) ∘ᵥ H.Δ           ≈⟨ ((refl⟩∘⟨ assoc) ⟩∘⟨refl) ⟩
                   
               (α⇒ ∘ᵥ (Z.arr ▷ γ.ϕ) ◁ J.h ∘ᵥ (H'.Δ ◁ J.h ∘ᵥ Y.arr ▷ δ.ϕ)) ∘ᵥ H.Δ           ≈˘⟨ ((refl⟩∘⟨ (refl⟩∘⟨ ◁-▷-exchg)) ⟩∘⟨refl) ⟩

               -- generalized assoc
               (α⇒ ∘ᵥ (Z.arr ▷ γ.ϕ) ◁ J.h ∘ᵥ (Z.arr ⊚₀ H'.h ▷ δ.ϕ ∘ᵥ H'.Δ ◁ H.h)) ∘ᵥ H.Δ   ≈˘⟨ ((refl⟩∘⟨ assoc) ⟩∘⟨refl) ⟩
               (α⇒ ∘ᵥ ((Z.arr ▷ γ.ϕ) ◁ J.h ∘ᵥ Z.arr ⊚₀ H'.h ▷ δ.ϕ) ∘ᵥ H'.Δ ◁ H.h) ∘ᵥ H.Δ   ≈˘⟨ (assoc ⟩∘⟨refl) ⟩
               (((α⇒ ∘ᵥ (Z.arr ▷ γ.ϕ) ◁ J.h ∘ᵥ Z.arr ⊚₀ H'.h ▷ δ.ϕ)) ∘ᵥ H'.Δ ◁ H.h) ∘ᵥ H.Δ ≈⟨ assoc ⟩

               (α⇒ ∘ᵥ (Z.arr ▷ γ.ϕ) ◁ J.h ∘ᵥ Z.arr ⊚₀ H'.h ▷ δ.ϕ) ∘ᵥ H'.Δ ◁ H.h ∘ᵥ H.Δ     ≈˘⟨ ((refl⟩∘⟨ ⊚.homomorphism) ⟩∘⟨refl) ⟩
               (α⇒ ∘ᵥ (Z.arr ▷ γ.ϕ ∘ᵥ id₂) ⊚₁ (id₂ ∘ᵥ δ.ϕ)) ∘ᵥ H'.Δ ◁ H.h ∘ᵥ H.Δ           ≈⟨ ((refl⟩∘⟨ identity₂ʳ ⟩⊚⟨ identity₂ˡ) ⟩∘⟨refl) ⟩
               (α⇒ ∘ᵥ (Z.arr ▷ γ.ϕ) ⊚₁ δ.ϕ) ∘ᵥ H'.Δ ◁ H.h ∘ᵥ H.Δ                           ≈⟨ (⊚-assoc.⇒.commute ((id₂ , γ.ϕ) , δ.ϕ) ⟩∘⟨refl) ⟩
               ((Z.arr ▷ γ.ϕ ⊚₁ δ.ϕ) ∘ᵥ α⇒) ∘ᵥ H'.Δ ◁ H.h ∘ᵥ H.Δ                           ≈⟨ assoc ⟩
               (Z.arr ▷ γ.ϕ ⊚₁ δ.ϕ) ∘ᵥ α⇒ ∘ᵥ H'.Δ ◁ H.h ∘ᵥ H.Δ                             ≈˘⟨ refl⟩∘⟨ assoc ⟩
               (Z.arr ▷ γ.ϕ ⊚₁ δ.ϕ) ∘ᵥ ((α⇒ ∘ᵥ H'.Δ ◁ H.h) ∘ᵥ H.Δ)
               ∎
      ; identity = ⊚.identity
      ; homomorphism = ⊚.homomorphism
      ; F-resp-≈ = ⊚.F-resp-≈
      }
      where module X = SliceObj X
            module Y = SliceObj Y
            module Z = SliceObj Z

  
  α⇒/ : ∀ {W X Y Z}(H : Slice⇒₁ Y Z) (J : Slice⇒₁ X Y) (K : Slice⇒₁ W X) → Slice⇒₂ ((F₀ _⊚/_ (F₀ _⊚/_ (H , J) , K))) (F₀ _⊚/_ (H  , F₀ _⊚/_ (J , K)))
  α⇒/ {W}{X}{Y}{Z} H J K = slicearr₂ $ begin
              Slice⇒₁.Δ (F₀ _⊚/_ (H  , F₀ _⊚/_ (J , K))) ≈⟨ Equiv.refl ⟩
              (α⇒ ∘ᵥ H.Δ ◁ J.h ⊚₀ K.h) ∘ᵥ ((α⇒ ∘ᵥ J.Δ ◁ K.h) ∘ᵥ K.Δ)                  ≈⟨ (refl⟩∘⟨ assoc) ⟩
              (α⇒ ∘ᵥ H.Δ ◁ J.h ⊚₀ K.h) ∘ᵥ α⇒ ∘ᵥ (J.Δ ◁ K.h ∘ᵥ K.Δ)                    ≈˘⟨ assoc ⟩
              ((α⇒ ∘ᵥ H.Δ ◁ J.h ⊚₀ K.h) ∘ᵥ α⇒) ∘ᵥ (J.Δ ◁ K.h ∘ᵥ K.Δ)                  ≈⟨ (assoc ⟩∘⟨refl) ⟩
              (α⇒ ∘ᵥ (H.Δ ◁ J.h ⊚₀ K.h ∘ᵥ α⇒)) ∘ᵥ (J.Δ ◁ K.h ∘ᵥ K.Δ)                  ≈⟨ assoc ⟩

              α⇒ ∘ᵥ (H.Δ ◁ J.h ⊚₀ K.h ∘ᵥ α⇒) ∘ᵥ (J.Δ ◁ K.h ∘ᵥ K.Δ)                    ≈˘⟨ (refl⟩∘⟨ (α⇒-◁-∘ₕ  ⟩∘⟨refl)) ⟩
  
              α⇒ ∘ᵥ (α⇒ ∘ᵥ H.Δ ◁ J.h ◁ K.h) ∘ᵥ (J.Δ ◁ K.h ∘ᵥ K.Δ)                     ≈⟨ Equiv.sym assoc ⟩
              (α⇒ ∘ᵥ (α⇒ ∘ᵥ H.Δ ◁ J.h ◁ K.h)) ∘ᵥ (J.Δ ◁ K.h ∘ᵥ K.Δ)                   ≈˘⟨ ( assoc ⟩∘⟨refl) ⟩
              ((α⇒ ∘ᵥ α⇒) ∘ᵥ H.Δ ◁ J.h ◁ K.h) ∘ᵥ (J.Δ ◁ K.h ∘ᵥ K.Δ)                   ≈⟨ assoc ⟩

              (α⇒ ∘ᵥ α⇒) ∘ᵥ H.Δ ◁ J.h ◁ K.h ∘ᵥ (J.Δ ◁ K.h ∘ᵥ K.Δ)                     ≈˘⟨ (pentagon ⟩∘⟨refl) ⟩
  
              (Z.arr ▷ α⇒ ∘ᵥ α⇒ ∘ᵥ α⇒ ◁ K.h) ∘ᵥ H.Δ ◁ J.h ◁ K.h ∘ᵥ (J.Δ ◁ K.h ∘ᵥ K.Δ) ≈⟨ assoc²' ⟩
              Z.arr ▷ α⇒ ∘ᵥ α⇒ ∘ᵥ α⇒ ◁ K.h ∘ᵥ H.Δ ◁ J.h ◁ K.h ∘ᵥ (J.Δ ◁ K.h ∘ᵥ K.Δ)   ≈⟨ (refl⟩∘⟨ (refl⟩∘⟨ Equiv.sym assoc)) ⟩

              Z.arr ▷ α⇒ ∘ᵥ α⇒ ∘ᵥ (α⇒ ◁ K.h ∘ᵥ H.Δ ◁ J.h ◁ K.h) ∘ᵥ (J.Δ ◁ K.h ∘ᵥ K.Δ) ≈⟨ (refl⟩∘⟨ (refl⟩∘⟨ (∘ᵥ-distr-◁ ⟩∘⟨refl))) ⟩
              Z.arr ▷ α⇒ ∘ᵥ α⇒ ∘ᵥ ((α⇒ ∘ᵥ H.Δ ◁ J.h) ◁ K.h) ∘ᵥ (J.Δ ◁ K.h ∘ᵥ K.Δ)     ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ Equiv.sym assoc) ⟩
              Z.arr ▷ α⇒ ∘ᵥ α⇒ ∘ᵥ ((α⇒ ∘ᵥ H.Δ ◁ J.h) ◁ K.h ∘ᵥ J.Δ ◁ K.h) ∘ᵥ K.Δ       ≈⟨ (refl⟩∘⟨ (refl⟩∘⟨ (∘ᵥ-distr-◁  ⟩∘⟨refl))) ⟩
              -- assoc/lifted assoc
              Z.arr ▷ α⇒ ∘ᵥ α⇒ ∘ᵥ (((α⇒ ∘ᵥ H.Δ ◁ J.h) ∘ᵥ J.Δ) ◁ K.h) ∘ᵥ K.Δ           ≈⟨ (refl⟩∘⟨ Equiv.sym assoc) ⟩

              Z.arr ▷ α⇒ ∘ᵥ ((α⇒ ∘ᵥ (((α⇒ ∘ᵥ H.Δ ◁ J.h)) ∘ᵥ J.Δ) ◁ K.h) ∘ᵥ K.Δ)       ≈⟨ Equiv.refl ⟩
              Z.arr ▷ α⇒ ∘ᵥ Slice⇒₁.Δ (F₀ _⊚/_ (F₀ _⊚/_ (H , J) , K))                 ∎
    where module W = SliceObj W
          module X = SliceObj X
          module Y = SliceObj Y
          module Z = SliceObj Z
          module H = Slice⇒₁ H
          module J = Slice⇒₁ J
          module K = Slice⇒₁ K
          open 1Category (hom W.Y A)
          open HomReasoning
          open MR (hom W.Y A) using (assoc²')

  λ⇒/ : ∀ {X Y} (H : Slice⇒₁ X Y) → Slice⇒₂ (F₀ _⊚/_ (slicearr₁ ρ⇐ , H)) H
  λ⇒/ {X}{Y} H = slicearr₂ $ begin
              H.Δ                                                  ≈˘⟨ identity₂ˡ ⟩
              id₂ ∘ᵥ H.Δ                                           ≈˘⟨ (id₂◁ ⟩∘⟨refl) ⟩
              (id₂ ◁ H.h) ∘ᵥ H.Δ                                   ≈˘⟨ (unitʳ.iso.isoʳ (Y.arr , (lift _)) ⟩⊚⟨refl ⟩∘⟨refl) ⟩
              ((ρ⇒ ∘ᵥ ρ⇐) ◁ H.h) ∘ᵥ H.Δ                            ≈˘⟨ (∘ᵥ-distr-◁ ⟩∘⟨refl) ⟩
              (ρ⇒ ◁ H.h ∘ᵥ ρ⇐ ◁ H.h) ∘ᵥ H.Δ                        ≈⟨ assoc ⟩
              ρ⇒ ◁ H.h ∘ᵥ ρ⇐ ◁ H.h ∘ᵥ H.Δ                          ≈˘⟨ (triangle ⟩∘⟨refl) ⟩
              (Y.arr ▷ λ⇒ ∘ᵥ α⇒) ∘ᵥ ρ⇐ ◁ H.h ∘ᵥ H.Δ                ≈⟨ assoc ⟩
              Y.arr ▷ λ⇒ ∘ᵥ α⇒ ∘ᵥ ρ⇐ ◁ H.h ∘ᵥ H.Δ                  ≈˘⟨ (refl⟩∘⟨ assoc) ⟩
              Y.arr ▷ λ⇒ ∘ᵥ (α⇒ ∘ᵥ ρ⇐ ◁ H.h) ∘ᵥ H.Δ                ≈⟨ refl ⟩
              Y.arr ▷ λ⇒ ∘ᵥ Slice⇒₁.Δ (F₀ _⊚/_ (slicearr₁ ρ⇐ , H)) ∎
    where module X = SliceObj X
          module Y = SliceObj Y
          module H = Slice⇒₁ H
          open 1Category (hom X.Y A)
          open HomReasoning

  ρ⇒/ : ∀{X}{Y} (H : Slice⇒₁ X Y) → Slice⇒₂ (F₀ _⊚/_ (H , slicearr₁ ρ⇐)) H
  ρ⇒/ {X}{Y} H = slicearr₂ $ begin
               H.Δ                                                   ≈˘⟨ identity₂ʳ ⟩
               H.Δ ∘ᵥ id₂                                            ≈˘⟨ refl⟩∘⟨ unitʳ.iso.isoʳ (X.arr , _) ⟩
               H.Δ ∘ᵥ ρ⇒ ∘ᵥ ρ⇐                                       ≈˘⟨ assoc ⟩
               (H.Δ ∘ᵥ ρ⇒) ∘ᵥ ρ⇐                                     ≈˘⟨ ρ⇒-∘ᵥ-◁ ⟩∘⟨refl ⟩
               (ρ⇒ ∘ᵥ H.Δ ◁ id₁) ∘ᵥ ρ⇐                               ≈⟨ unitorʳ-coherence  ⟩∘⟨refl ⟩∘⟨refl ⟩
               ((Y.arr ▷ ρ⇒ ∘ᵥ α⇒) ∘ᵥ H.Δ ◁ id₁) ∘ᵥ ρ⇐               ≈⟨ assoc ⟩∘⟨refl ⟩
               (Y.arr ▷ ρ⇒ ∘ᵥ (α⇒ ∘ᵥ H.Δ ◁ id₁)) ∘ᵥ ρ⇐               ≈⟨ assoc ⟩
               Y.arr ▷ ρ⇒ ∘ᵥ (α⇒ ∘ᵥ H.Δ ◁ id₁) ∘ᵥ ρ⇐                 ≈⟨ refl ⟩
               Y.arr ▷ ρ⇒ ∘ᵥ Slice⇒₁.Δ (F₀ _⊚/_ (H , slicearr₁ ρ⇐ )) ∎
    where module X = SliceObj X
          module Y = SliceObj Y
          module H = Slice⇒₁ H
          open 1Category (hom X.Y A)
          open HomReasoning

  slice-inv : ∀ {X}{Y}{H : Slice⇒₁ X Y}{K} (α : Slice⇒₂ H K) → (f : Slice⇒₁.h K ⇒₂ Slice⇒₁.h H) → (f ∘ᵥ (Slice⇒₂.ϕ α) ≈ id₂) → Slice⇒₂ K H
  slice-inv {X}{Y}{H}{K} α f p = slicearr₂ $ begin
                  H.Δ                               ≈˘⟨ identity₂ˡ ⟩
                  id₂ ∘ᵥ H.Δ                        ≈⟨ (Equiv.sym ▷id₂ ⟩∘⟨refl) ⟩
                  (Y.arr ▷ id₂) ∘ᵥ H.Δ              ≈˘⟨ (refl⟩⊚⟨ p ⟩∘⟨refl) ⟩
                  (Y.arr ▷ (f ∘ᵥ α.ϕ)) ∘ᵥ H.Δ       ≈˘⟨ (∘ᵥ-distr-▷ ⟩∘⟨refl) ⟩
                  (Y.arr ▷ f ∘ᵥ Y.arr ▷ α.ϕ) ∘ᵥ H.Δ ≈⟨ assoc ⟩
                  Y.arr ▷ f ∘ᵥ Y.arr ▷ α.ϕ ∘ᵥ H.Δ   ≈˘⟨ (refl⟩∘⟨ α.E ) ⟩
                  Y.arr ▷ f ∘ᵥ K.Δ                  ∎
    where module X = SliceObj X
          module Y = SliceObj Y
          module H = Slice⇒₁ H
          module K = Slice⇒₁ K
          module α = Slice⇒₂ α          
          open 1Category (hom X.Y A)
          open HomReasoning

LaxSlice : Obj → Bicategory (o ⊔ ℓ) (ℓ ⊔ e) e (o ⊔ t)
LaxSlice A   = record
  { enriched = record
    { Obj = SliceObj A
    ; hom = SliceHomCat
    ; id = const (SliceHom.slicearr₁ ρ⇐)
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
