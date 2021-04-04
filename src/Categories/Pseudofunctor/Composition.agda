{-# OPTIONS --without-K --safe #-}

-- Composition of pseudofunctors

module Categories.Pseudofunctor.Composition where

open import Data.Product using (_,_)

open import Categories.Bicategory using (Bicategory)
import Categories.Bicategory.Extras as BicategoryExt
open import Categories.Category using (Category)
open import Categories.Category.Instance.One using (shift)
open import Categories.Category.Product using (_⁂_)
open import Categories.Functor using (Functor; _∘F_)
import Categories.Morphism.Reasoning as MorphismReasoning
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (NaturalIsomorphism; _≃_; niHelper; _ⓘˡ_; _ⓘʳ_)
open import Categories.Pseudofunctor using (Pseudofunctor)

open Category using (module HomReasoning)
open NaturalIsomorphism using (F⇒G; F⇐G)

infixr 9 _∘P_

-- Composition of pseudofunctors

_∘P_ : ∀ {o ℓ e t o′ ℓ′ e′ t′ o″ ℓ″ e″ t″}
         {C : Bicategory o ℓ e t} {D : Bicategory o′ ℓ′ e′ t′}
         {E : Bicategory o″ ℓ″ e″ t″} →
       Pseudofunctor D E → Pseudofunctor C D → Pseudofunctor C E
_∘P_ {o″ = o″} {ℓ″ = ℓ″} {e″ = e″} {C = C} {D = D} {E = E} F G = record
  { P₀             = λ x → F₀ (G₀ x)
  ; P₁             = F₁ ∘F G₁
  ; P-identity     = P-identity
  ; P-homomorphism = P-homomorphism
  ; unitaryˡ       = unitaryˡ
  ; unitaryʳ       = unitaryʳ
  ; assoc          = assoc
  }
  where
    module C  = BicategoryExt C
    module D  = BicategoryExt D
    module E  = BicategoryExt E
    module F  = Pseudofunctor F
    module G  = Pseudofunctor G
    open E
    open F using () renaming (P₀ to F₀; P₁ to F₁)
    open G using () renaming (P₀ to G₀; P₁ to G₁)
    module F₁G₁ {x} {y} = Functor (F₁ {G₀ x} {G₀ y} ∘F G₁ {x} {y})
    open NaturalIsomorphism

    F∘G-id = λ {x} → F₁ ⓘˡ G.P-identity {x}
    F-id   = λ {x} → F.P-identity {G₀ x}

    P-identity : ∀ {x} → E.id ∘F shift o″ ℓ″ e″ ≃ (F₁ ∘F G₁) ∘F (C.id {x})
    P-identity {x} = niHelper (record
      { η       = λ _ → ⇒.η F∘G-id _ ∘ᵥ ⇒.η F-id _
      ; η⁻¹     = λ _ → ⇐.η F-id _ ∘ᵥ ⇐.η F∘G-id _
      ; commute = λ _ → glue (⇒.commute F∘G-id _) (⇒.commute F-id _)
      ; iso     = λ _ → record
        { isoˡ = begin
            (⇐.η F-id _ ∘ᵥ ⇐.η F∘G-id _) ∘ᵥ ⇒.η F∘G-id _ ∘ᵥ ⇒.η F-id _
          ≈⟨ cancelInner (iso.isoˡ F∘G-id _) ⟩
            ⇐.η F-id _ ∘ᵥ ⇒.η F-id _
          ≈⟨ iso.isoˡ F-id _ ⟩
            id₂
          ∎
        ; isoʳ = begin
            (⇒.η F∘G-id _ ∘ᵥ ⇒.η F-id _) ∘ᵥ ⇐.η F-id _ ∘ᵥ ⇐.η F∘G-id _
          ≈⟨ cancelInner (iso.isoʳ F-id _) ⟩
            ⇒.η F∘G-id _ ∘ᵥ ⇐.η F∘G-id _
          ≈⟨ iso.isoʳ F∘G-id _ ⟩
            id₂
          ∎
        }
      })
      where
        FGx = F₀ (G₀ x)
        open HomReasoning (hom FGx FGx)
        open MorphismReasoning (hom FGx FGx)

    F∘G-h = λ {x y z} → F₁ ⓘˡ G.P-homomorphism {x} {y} {z}
    F-h∘G = λ {x y z} → F.P-homomorphism {G₀ x} {G₀ y} {G₀ z} ⓘʳ (G₁ ⁂ G₁)

    P-homomorphism : ∀ {x y z} →
                     E.⊚ ∘F (F₁ ∘F G₁ ⁂ F₁ ∘F G₁) ≃
                       (F₁ ∘F G₁) ∘F C.⊚ {x} {y} {z}
    P-homomorphism {x} {y} {z} = niHelper (record
      { η       = λ f,g → ⇒.η F∘G-h f,g ∘ᵥ ⇒.η F-h∘G f,g
      ; η⁻¹     = λ f,g → ⇐.η F-h∘G f,g ∘ᵥ ⇐.η F∘G-h f,g
      ; commute = λ α,β → glue (⇒.commute F∘G-h α,β) (⇒.commute F-h∘G α,β)
      ; iso     = λ f,g → record
        { isoˡ = cancelInner (iso.isoˡ F∘G-h f,g) ○ iso.isoˡ F-h∘G f,g
        ; isoʳ = cancelInner (iso.isoʳ F-h∘G f,g) ○ iso.isoʳ F∘G-h f,g
        }
      })
      where
        FGx = F₀ (G₀ x)
        FGz = F₀ (G₀ z)
        open HomReasoning (hom FGx FGz)
        open MorphismReasoning (hom FGx FGz)

    Pid  = λ {A} → NaturalTransformation.η (F⇒G (P-identity {A})) _
    Phom = λ {x} {y} {z} f,g →
           NaturalTransformation.η (F⇒G (P-homomorphism {x} {y} {z})) f,g
    λ⇒   = unitorˡ.from
    ρ⇒   = unitorʳ.from
    α⇒   = associator.from

    unitaryˡ : ∀ {x y} {f : x C.⇒₁ y} →
               let open ComHom in
               [ id₁ ⊚₀ F₁G₁.₀ f ⇒ F₁G₁.₀ f ]⟨
                 Pid ⊚₁ id₂             ⇒⟨ F₁G₁.₀ C.id₁ ⊚₀ F₁G₁.₀ f ⟩
                 Phom (C.id₁ , f)       ⇒⟨ F₁G₁.₀ (C.id₁ C.⊚₀ f) ⟩
                 F₁G₁.₁ C.unitorˡ.from
               ≈ E.unitorˡ.from
               ⟩
    unitaryˡ {x} {y} {f} = begin
        F₁G₁.₁ C.unitorˡ.from ∘ᵥ Phom (C.id₁ , f) ∘ᵥ Pid ⊚₁ id₂
      ≡⟨⟩
        F₁.₁ (G₁.₁ C.unitorˡ.from) ∘ᵥ
        (⇒.η F∘G-h (C.id₁ , f) ∘ᵥ ⇒.η F-h∘G (C.id₁ , f)) ∘ᵥ
        (⇒.η F∘G-id _ ∘ᵥ ⇒.η F-id _) ⊚₁ id₂
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ E.∘ᵥ-distr-◁ ⟩
        F₁.₁ (G₁.₁ C.unitorˡ.from) ∘ᵥ
        (⇒.η F∘G-h (C.id₁ , f) ∘ᵥ ⇒.η F-h∘G (C.id₁ , f)) ∘ᵥ
        ⇒.η F∘G-id _ ⊚₁ id₂ ∘ᵥ ⇒.η F-id _ ⊚₁ id₂
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ E.⊚.F-resp-≈ (hom.Equiv.refl , F₁.identity) ⟩∘⟨refl ⟩
        F₁.₁ (G₁.₁ C.unitorˡ.from) ∘ᵥ
        (⇒.η F∘G-h (C.id₁ , f) ∘ᵥ ⇒.η F-h∘G (C.id₁ , f)) ∘ᵥ
        ⇒.η F∘G-id _ ⊚₁ F₁.₁ D.id₂ ∘ᵥ ⇒.η F-id _ ⊚₁ id₂
      ≈⟨ refl⟩∘⟨ extend² (F.Hom.commute (G.unitˡ.η _ , D.id₂)) ⟩
        F₁.₁ (G₁.₁ C.unitorˡ.from) ∘ᵥ
        (⇒.η F∘G-h (C.id₁ , f) ∘ᵥ F₁.₁ (G.unitˡ.η _ D.⊚₁ D.id₂)) ∘ᵥ
        F.Hom.η (D.id₁ , G₁.₀ f) ∘ᵥ ⇒.η F-id _ ⊚₁ id₂
      ≈˘⟨ pushˡ (F₁.homomorphism ○ hom.∘-resp-≈ʳ F₁.homomorphism) ⟩
        F₁.₁ (G₁.₁ C.unitorˡ.from D.∘ᵥ
              G.Hom.η (C.id₁ , f) D.∘ᵥ G.unitˡ.η _ D.⊚₁ D.id₂) ∘ᵥ
        F.Hom.η (D.id₁ , G₁.₀ f) ∘ᵥ ⇒.η F-id _ ⊚₁ id₂
      ≈⟨ F₁.F-resp-≈ G.unitaryˡ ⟩∘⟨refl ⟩
        F₁.₁ (D.unitorˡ.from) ∘ᵥ
        F.Hom.η (D.id₁ , G₁.₀ f) ∘ᵥ ⇒.η F-id _ ⊚₁ id₂
      ≈⟨ F.unitaryˡ ⟩
        E.unitorˡ.from
      ∎
      where
        FGx = F₀ (G₀ x)
        FGy = F₀ (G₀ y)
        open HomReasoning (hom FGx FGy)
        open MorphismReasoning (hom FGx FGy)

    unitaryʳ : ∀ {x y} {f : x C.⇒₁ y} →
               let open ComHom in
               [ F₁G₁.₀ f ⊚₀ id₁ ⇒ F₁G₁.₀ f ]⟨
                 id₂ ⊚₁ Pid             ⇒⟨ F₁G₁.₀ f ⊚₀ F₁G₁.₀ C.id₁ ⟩
                 Phom (f , C.id₁)       ⇒⟨ F₁G₁.₀ (f C.⊚₀ C.id₁) ⟩
                 F₁G₁.₁ C.unitorʳ.from
               ≈ E.unitorʳ.from
               ⟩
    unitaryʳ {x} {y} {f} = begin
        F₁G₁.₁ C.unitorʳ.from ∘ᵥ Phom (f , C.id₁) ∘ᵥ id₂ ⊚₁ Pid
      ≡⟨⟩
        F₁.₁ (G₁.₁ C.unitorʳ.from) ∘ᵥ
        (⇒.η F∘G-h (f , C.id₁) ∘ᵥ ⇒.η F-h∘G (f , C.id₁)) ∘ᵥ
        id₂ ⊚₁ (⇒.η F∘G-id _ ∘ᵥ ⇒.η F-id _)
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ E.∘ᵥ-distr-▷ ⟩
        F₁.₁ (G₁.₁ C.unitorʳ.from) ∘ᵥ
        (⇒.η F∘G-h (f , C.id₁) ∘ᵥ ⇒.η F-h∘G (f , C.id₁)) ∘ᵥ
        id₂ ⊚₁ ⇒.η F∘G-id _ ∘ᵥ id₂ ⊚₁ ⇒.η F-id _
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ E.⊚.F-resp-≈ (F₁.identity , hom.Equiv.refl) ⟩∘⟨refl ⟩
        F₁.₁ (G₁.₁ C.unitorʳ.from) ∘ᵥ
        (⇒.η F∘G-h (f , C.id₁) ∘ᵥ ⇒.η F-h∘G (f , C.id₁)) ∘ᵥ
        F₁.₁ D.id₂ ⊚₁ ⇒.η F∘G-id _ ∘ᵥ id₂ ⊚₁ ⇒.η F-id _
      ≈⟨ refl⟩∘⟨ extend² (F.Hom.commute (D.id₂ , G.unitˡ.η _)) ⟩
        F₁.₁ (G₁.₁ C.unitorʳ.from) ∘ᵥ
        (⇒.η F∘G-h (f , C.id₁) ∘ᵥ F₁.₁ (D.id₂ D.⊚₁ G.unitˡ.η _)) ∘ᵥ
        F.Hom.η (G₁.₀ f , D.id₁) ∘ᵥ id₂ ⊚₁ ⇒.η F-id _
      ≈˘⟨ pushˡ (F₁.homomorphism ○ hom.∘-resp-≈ʳ F₁.homomorphism) ⟩
        F₁.₁ (G₁.₁ C.unitorʳ.from D.∘ᵥ
              G.Hom.η (f , C.id₁) D.∘ᵥ D.id₂ D.⊚₁ G.unitˡ.η _) ∘ᵥ
        F.Hom.η (G₁.₀ f , D.id₁) ∘ᵥ id₂ ⊚₁ ⇒.η F-id _
      ≈⟨ F₁.F-resp-≈ G.unitaryʳ ⟩∘⟨refl ⟩
        F₁.₁ (D.unitorʳ.from) ∘ᵥ
        F.Hom.η (G₁.₀ f , D.id₁) ∘ᵥ id₂ ⊚₁ ⇒.η F-id _
      ≈⟨ F.unitaryʳ ⟩
        E.unitorʳ.from
      ∎
      where
        FGx = F₀ (G₀ x)
        FGy = F₀ (G₀ y)
        open HomReasoning (hom FGx FGy)
        open MorphismReasoning (hom FGx FGy)

    assoc : ∀ {x y z w} {f : x C.⇒₁ y} {g : y C.⇒₁ z} {h : z C.⇒₁ w} →
            let open ComHom in
            [ (F₁G₁.₀ h ⊚₀ F₁G₁.₀ g) ⊚₀ F₁G₁.₀ f ⇒ F₁G₁.₀ (h C.⊚₀ (g C.⊚₀ f)) ]⟨
              Phom (h , g) ⊚₁ id₂     ⇒⟨ F₁G₁.₀ (h C.⊚₀ g) ⊚₀ F₁G₁.₀ f ⟩
              Phom (_ , f)            ⇒⟨ F₁G₁.₀ ((h C.⊚₀ g) C.⊚₀ f) ⟩
              F₁G₁.₁ C.associator.from
            ≈ E.associator.from       ⇒⟨ F₁G₁.₀ h ⊚₀ (F₁G₁.₀ g ⊚₀ F₁G₁.₀ f) ⟩
              id₂ ⊚₁ Phom (g , f)     ⇒⟨ F₁G₁.₀ h ⊚₀ F₁G₁.₀ (g C.⊚₀ f) ⟩
              Phom (h , _)
            ⟩
    assoc {x} {_} {_} {w} {f} {g} {h} = begin
        F₁G₁.₁ C.associator.from ∘ᵥ Phom (_ , f) ∘ᵥ Phom (h , g) ⊚₁ id₂
      ≡⟨⟩
        F₁.₁ (G₁.₁ C.associator.from) ∘ᵥ
        (⇒.η F∘G-h (_ , f) ∘ᵥ ⇒.η F-h∘G (_ , f)) ∘ᵥ
        (⇒.η F∘G-h (h , g) ∘ᵥ ⇒.η F-h∘G (h , g)) ⊚₁ id₂
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ E.∘ᵥ-distr-◁ ⟩
        F₁.₁ (G₁.₁ C.associator.from) ∘ᵥ
        (⇒.η F∘G-h (_ , f) ∘ᵥ ⇒.η F-h∘G (_ , f)) ∘ᵥ
        ⇒.η F∘G-h (h , g) ⊚₁ id₂ ∘ᵥ ⇒.η F-h∘G (h , g) ⊚₁ id₂
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ E.⊚.F-resp-≈ (hom.Equiv.refl , F₁.identity) ⟩∘⟨refl ⟩
        F₁.₁ (G₁.₁ C.associator.from) ∘ᵥ
        (⇒.η F∘G-h (_ , f) ∘ᵥ ⇒.η F-h∘G (_ , f)) ∘ᵥ
        ⇒.η F∘G-h (h , g) ⊚₁ F₁.₁ D.id₂ ∘ᵥ ⇒.η F-h∘G (h , g) ⊚₁ id₂
      ≈⟨ refl⟩∘⟨ extend² (F.Hom.commute (G.Hom.η (h , g) , D.id₂)) ⟩
        F₁.₁ (G₁.₁ C.associator.from) ∘ᵥ
        (⇒.η F∘G-h (_ , f) ∘ᵥ F₁.₁ (G.Hom.η (h , g) D.⊚₁ D.id₂)) ∘ᵥ
        F.Hom.η (_ , G₁.₀ f) ∘ᵥ ⇒.η F-h∘G (h , g) ⊚₁ id₂
      ≈˘⟨ pushˡ (F₁.homomorphism ○ hom.∘-resp-≈ʳ F₁.homomorphism) ⟩
        F₁.₁ (G₁.₁ C.associator.from D.∘ᵥ
              G.Hom.η (_ , f) D.∘ᵥ G.Hom.η (h , g) D.⊚₁ D.id₂) ∘ᵥ
        F.Hom.η (_ , G₁.₀ f) ∘ᵥ ⇒.η F-h∘G (h , g) ⊚₁ id₂
      ≈⟨ F₁.F-resp-≈ G.assoc ⟩∘⟨refl ⟩
        F₁.₁ (G.Hom.η (h , _) D.∘ᵥ D.id₂ D.⊚₁ G.Hom.η (g , f) D.∘ᵥ
              D.associator.from) ∘ᵥ
        F.Hom.η (_ , G₁.₀ f) ∘ᵥ ⇒.η F-h∘G (h , g) ⊚₁ id₂
      ≈⟨ (F₁.homomorphism ○ pushʳ F₁.homomorphism) ⟩∘⟨refl ⟩
        ((⇒.η F∘G-h (h , _) ∘ᵥ F₁.₁ (D.id₂ D.⊚₁ G.Hom.η (g , f))) ∘ᵥ
         F₁.₁ D.associator.from) ∘ᵥ
        F.Hom.η (_ , G₁.₀ f) ∘ᵥ ⇒.η F-h∘G (h , g) ⊚₁ id₂
      ≈⟨ pullʳ F.assoc ⟩
        (⇒.η F∘G-h (h , _) ∘ᵥ F₁.₁ (D.id₂ D.⊚₁ G.Hom.η (g , f))) ∘ᵥ
        F.Hom.η (G₁.₀ h , _) ∘ᵥ id₂ ⊚₁ ⇒.η F-h∘G (g , f) ∘ᵥ
        E.associator.from
      ≈˘⟨ extend² (F.Hom.commute (D.id₂ , G.Hom.η (g , f))) ⟩
        (⇒.η F∘G-h (h , _) ∘ᵥ ⇒.η F-h∘G (h , _)) ∘ᵥ
        F₁.₁ D.id₂ ⊚₁ ⇒.η F∘G-h (g , f) ∘ᵥ id₂ ⊚₁ ⇒.η F-h∘G (g , f) ∘ᵥ
        E.associator.from
      ≈⟨ refl⟩∘⟨ pullˡ (E.⊚.F-resp-≈ (F₁.identity , hom.Equiv.refl) ⟩∘⟨refl) ⟩
        (⇒.η F∘G-h (h , _) ∘ᵥ ⇒.η F-h∘G (h , _)) ∘ᵥ
        (id₂ ⊚₁ ⇒.η F∘G-h (g , f) ∘ᵥ id₂ ⊚₁ ⇒.η F-h∘G (g , f)) ∘ᵥ
        E.associator.from
      ≈⟨ refl⟩∘⟨ E.∘ᵥ-distr-▷ ⟩∘⟨refl ⟩
        (⇒.η F∘G-h (h , _) ∘ᵥ ⇒.η F-h∘G (h , _)) ∘ᵥ
        id₂ ⊚₁ (⇒.η F∘G-h (g , f) ∘ᵥ ⇒.η F-h∘G (g , f)) ∘ᵥ
        E.associator.from
      ≡⟨⟩
        Phom (h , _) ∘ᵥ id₂ ⊚₁ Phom (g , f) ∘ᵥ E.associator.from
      ∎
      where
        FGx = F₀ (G₀ x)
        FGw = F₀ (G₀ w)
        open HomReasoning (hom FGx FGw)
        open MorphismReasoning (hom FGx FGw)
