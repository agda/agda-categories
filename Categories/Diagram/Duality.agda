{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Diagram.Duality {o ℓ e} (C : Category o ℓ e) where

open Category C

open import Level

open import Categories.Functor
open import Categories.Functor.Bifunctor
open import Categories.NaturalTransformation.Dinatural

open import Categories.Diagram.Equalizer op
open import Categories.Diagram.Coequalizer C
open import Categories.Diagram.Pullback op
open import Categories.Diagram.Pushout C
open import Categories.Diagram.Cone as Cone
open import Categories.Diagram.Cocone as Cocone
open import Categories.Diagram.End as End
open import Categories.Diagram.Coend as Coend

private
  variable
    o′ ℓ′ e′ : Level
    D J : Category o′ ℓ′ e′
    A B : Obj
    f g : A ⇒ B

Coequalizer⇒coEqualizer : Coequalizer f g → Equalizer f g
Coequalizer⇒coEqualizer coe = record
  { arr       = arr
  ; equality  = equality
  ; equalize  = coequalize
  ; universal = universal
  ; unique    = unique
  }
  where open Coequalizer coe

coEqualizer⇒Coequalizer : Equalizer f g → Coequalizer f g
coEqualizer⇒Coequalizer e = record
  { arr        = arr
  ; equality   = equality
  ; coequalize = equalize
  ; universal  = universal
  ; unique     = unique
  }
  where open Equalizer e

coPullback⇒Pushout : Pullback f g → Pushout f g
coPullback⇒Pushout p = record
  { i₁              = p₁
  ; i₂              = p₂
  ; commute         = commute
  ; universal       = universal
  ; unique          = unique
  ; universal∘i₁≈h₁ = p₁∘universal≈h₁
  ; universal∘i₂≈h₂ = p₂∘universal≈h₂
  }
  where open Pullback p

Pushout⇒coPullback : Pushout f g → Pullback f g
Pushout⇒coPullback p = record
  { p₁              = i₁
  ; p₂              = i₂
  ; commute         = commute
  ; universal       = universal
  ; unique          = unique
  ; p₁∘universal≈h₁ = universal∘i₁≈h₁
  ; p₂∘universal≈h₂ = universal∘i₂≈h₂
  }
  where open Pushout p

module _ {F : Functor J C} where
  open Functor F renaming (op to Fop)

  coCone⇒Cocone : Cone Fop → Cocone F
  coCone⇒Cocone c = record
    { coapex = record
      { ψ       = ψ
    ; commute = commute
      }
    }
    where open Cone.Cone c

  Cocone⇒coCone : Cocone F → Cone Fop
  Cocone⇒coCone c = record
    { apex = record
      { ψ       = ψ
      ; commute = commute
      }
    }
    where open Cocone.Cocone c

module _ {F : Bifunctor (Category.op D) D C} where
  open HomReasoning
  open Functor F renaming (op to Fop)

  coWedge⇒Cowedge : Wedge Fop → Cowedge F
  coWedge⇒Cowedge W = record
    { E         = E
    ; dinatural = record
      { α       = α
      ; commute = λ f → ⟺ assoc ○ ⟺ (commute f) ○ assoc
      }
    }
    where open Wedge W
          open DinaturalTransformation dinatural

  Cowedge⇒coWedge : Cowedge F → Wedge Fop
  Cowedge⇒coWedge W = record
    { E         = E
    ; dinatural = record
      { α       = α
      ; commute = λ f → assoc ○ ⟺ (commute f) ○ ⟺ assoc
      }
    }
    where open Cowedge W
          open DinaturalTransformation dinatural

  coEnd⇒Coend : End Fop → Coend F
  coEnd⇒Coend e = record
    { cowedge   = coWedge⇒Cowedge wedge
    ; factor    = λ W → factor (Cowedge⇒coWedge W)
    ; universal = universal
    ; unique    = unique
    }
    where open End.End e

  Coend⇒coEnd : Coend F → End Fop
  Coend⇒coEnd e = record
    { wedge     = Cowedge⇒coWedge cowedge
    ; factor    = λ W → factor (coWedge⇒Cowedge W)
    ; universal = universal
    ; unique    = unique
    }
    where open Coend.Coend e
