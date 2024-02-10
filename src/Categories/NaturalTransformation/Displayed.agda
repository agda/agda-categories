{-# OPTIONS --safe --without-K #-}

module Categories.NaturalTransformation.Displayed where

open import Level

open import Categories.Category.Core
open import Categories.Category.Displayed
open import Categories.Functor hiding (id)
open import Categories.Functor.Displayed renaming (id′ to idF′)
open import Categories.Functor.Displayed.Properties
import Categories.Morphism.Displayed.Reasoning as DMR
open import Categories.NaturalTransformation

private
  variable
    o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ o‴ ℓ‴ e‴ : Level
    C D E : Category o ℓ e
    F G H : Functor C D
    C′ D′ : Displayed C o ℓ e

record DisplayedNaturalTransformation
  {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {F G : Functor C D}
  {C′ : Displayed C o″ ℓ″ e″} {D′ : Displayed D o‴ ℓ‴ e‴} (F′ : DisplayedFunctor C′ D′ F) (G′ : DisplayedFunctor C′ D′ G)
  (T : NaturalTransformation F G)
  : Set (o ⊔ ℓ ⊔ o″ ⊔ ℓ″ ⊔ ℓ‴ ⊔ e‴) where
  private
    module C′ = Displayed C′
    module D′ = Displayed D′
    module F′ = DisplayedFunctor F′
    module G′ = DisplayedFunctor G′
  open NaturalTransformation T
  field
    η′ : ∀ {X} (X′ : C′.Obj[ X ]) → F′.₀′ X′ D′.⇒[ η X ] G′.₀′ X′
    commute′ : ∀ {X Y} {X′ : C′.Obj[ X ]} {Y′ : C′.Obj[ Y ]} {f} (f′ : X′ C′.⇒[ f ] Y′)
               → η′ Y′ D′.∘′ F′.₁′ f′ D′.≈[ commute f ] G′.₁′ f′ D′.∘′ η′ X′
    sym-commute′ : ∀ {X Y} {X′ : C′.Obj[ X ]} {Y′ : C′.Obj[ Y ]} {f} (f′ : X′ C′.⇒[ f ] Y′)
                 → G′.₁′ f′ D′.∘′ η′ X′ D′.≈[ sym-commute f ] η′ Y′ D′.∘′ F′.₁′ f′

  op′ : DisplayedNaturalTransformation G′.op′ F′.op′ op
  op′ = record
    { η′ = η′
    ; commute′ = sym-commute′
    ; sym-commute′ = commute′
    }

id′ : ∀ {C′ : Displayed C o″ ℓ″ e″} {D′ : Displayed D o‴ ℓ‴ e‴} {F′ : DisplayedFunctor C′ D′ F}
      → DisplayedNaturalTransformation F′ F′ id
id′ {D′ = D′} = record
  { η′ = λ _ → D′.id′
  ; commute′ = λ f → id′-comm-sym
  ; sym-commute′ = λ _ → id′-comm
  }
  where
    module D′ = Displayed D′
    open DMR D′

_∘′ᵥ_ : ∀ {S : NaturalTransformation G H} {T : NaturalTransformation F G}
          {C′ : Displayed C o″ ℓ″ e″} {D′ : Displayed D o‴ ℓ‴ e‴}
          {F′ : DisplayedFunctor C′ D′ F} {G′ : DisplayedFunctor C′ D′ G} {H′ : DisplayedFunctor C′ D′ H}
        → DisplayedNaturalTransformation G′ H′ S → DisplayedNaturalTransformation F′ G′ T
        → DisplayedNaturalTransformation F′ H′ (S ∘ᵥ T)
_∘′ᵥ_ {D′ = D′} S′ T′ = record
  { η′ = λ X → S′.η′ X D′.∘′ T′.η′ X
  ; commute′ = λ f → glue′ (S′.commute′ f) (T′.commute′ f)
  ; sym-commute′ = λ f → sym-glue′ (S′.sym-commute′ f) (T′.sym-commute′ f)
  }
  where
    module D′ = Displayed D′
    module S′ = DisplayedNaturalTransformation S′
    module T′ = DisplayedNaturalTransformation T′
    open DMR D′

_∘′ₕ_ : ∀ {F G : Functor C D} {H I : Functor D E}
          {S : NaturalTransformation H I} {T : NaturalTransformation F G}
          {C′ : Displayed C o ℓ e} {D′ : Displayed D o′ ℓ′ e′} {E′ : Displayed E o″ ℓ″ e″}
          {F′ : DisplayedFunctor C′ D′ F} {G′ : DisplayedFunctor C′ D′ G}
          {H′ : DisplayedFunctor D′ E′ H} {I′ : DisplayedFunctor D′ E′ I}
        → DisplayedNaturalTransformation H′ I′ S
        → DisplayedNaturalTransformation F′ G′ T
        → DisplayedNaturalTransformation (H′ ∘F′ F′) (I′ ∘F′ G′) (S ∘ₕ T)
_∘′ₕ_ {E′ = E′} {F′ = F′} {I′ = I′} S′ T′ = record
  { η′ = λ X → I′.₁′ (T′.η′ X) E′.∘′ S′.η′ (F′.₀′ X)
  ; commute′ = λ f → glue′ ([ I′ ]-resp-square′ (T′.commute′ f)) (S′.commute′ (F′.₁′ f))
  ; sym-commute′ = λ f → sym-glue′ ([ I′ ]-resp-square′ (T′.sym-commute′ f)) (S′.sym-commute′ (F′.₁′ f)) 
  } 
  where
    module S′ = DisplayedNaturalTransformation S′
    module T′ = DisplayedNaturalTransformation T′
    module E′ = Displayed E′
    module F′ = DisplayedFunctor F′
    module I′ = DisplayedFunctor I′
    open DMR E′

id′∘id′⇒id′ : ∀ {C′ : Displayed C o ℓ e} → DisplayedNaturalTransformation {C′ = C′} {D′ = C′} (idF′ ∘F′ idF′) idF′ id∘id⇒id
id′∘id′⇒id′ {C′ = C′} = record
  { η′ = λ _ → Displayed.id′ C′
  ; commute′ = λ _ → DMR.id′-comm-sym C′
  ; sym-commute′ = λ _ → DMR.id′-comm C′
  }

id′⇒id′∘id′ : ∀ {C′ : Displayed C o ℓ e} → DisplayedNaturalTransformation {C′ = C′} {D′ = C′} idF′ (idF′ ∘F′ idF′) id⇒id∘id
id′⇒id′∘id′ {C′ = C′} = record
  { η′ = λ _ → Displayed.id′ C′
  ; commute′ = λ _ → DMR.id′-comm-sym C′
  ; sym-commute′ = λ _ → DMR.id′-comm C′
  }

module _ {F′ : DisplayedFunctor C′ D′ F} where
  open DMR D′
  private module D′ = Displayed D′

  F′⇒F′∘id′ : DisplayedNaturalTransformation F′ (F′ ∘F′ idF′) F⇒F∘id
  F′⇒F′∘id′ = record { η′ = λ _ → D′.id′; commute′ = λ _ → id′-comm-sym ; sym-commute′ = λ _ → id′-comm }

  F′⇒id′∘F′ : DisplayedNaturalTransformation F′ (idF′ ∘F′ F′) F⇒id∘F
  F′⇒id′∘F′ = record { η′ = λ _ → D′.id′ ; commute′ = λ _ → id′-comm-sym ; sym-commute′ = λ _ → id′-comm }

  F′∘id′⇒F′ : DisplayedNaturalTransformation (F′ ∘F′ idF′) F′ F∘id⇒F
  F′∘id′⇒F′ = record { η′ = λ _ → D′.id′ ; commute′ = λ _ → id′-comm-sym ; sym-commute′ = λ _ → id′-comm }

  id′∘F′⇒F′ : DisplayedNaturalTransformation (idF′ ∘F′ F′) F′ id∘F⇒F
  id′∘F′⇒F′ = record { η′ = λ _ → D′.id′ ; commute′ = λ _ → id′-comm-sym ; sym-commute′ = λ _ → id′-comm }
