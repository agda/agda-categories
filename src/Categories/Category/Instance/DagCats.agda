{-# OPTIONS --safe --without-K #-}

module Categories.Category.Instance.DagCats where

open import Categories.Category.Core
open import Categories.Category.Dagger
open import Categories.Functor.Dagger
open import Categories.NaturalTransformation.NaturalIsomorphism

open import Function.Base using (_on_)
open import Level

DagCats : ∀ o ℓ e → Category (suc (o ⊔ ℓ ⊔ e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
DagCats o ℓ e = record
  { Obj = DaggerCategory o ℓ e
  ; _⇒_ = DaggerFunctor
  ; _≈_ = NaturalIsomorphism on DaggerFunctor.functor
  ; id = id
  ; _∘_ = _∘F†_
  ; assoc = λ {_ _ _ _ F G H} → associator (DaggerFunctor.functor F) (DaggerFunctor.functor G) (DaggerFunctor.functor H)
  ; sym-assoc = λ {_ _ _ _ F G H} → sym (associator (DaggerFunctor.functor F) (DaggerFunctor.functor G) (DaggerFunctor.functor H))
  ; identityˡ = unitorˡ
  ; identityʳ = unitorʳ
  ; identity² = unitor²
  ; equiv = record
    { refl = refl
    ; sym = sym
    ; trans = trans
    }
  ; ∘-resp-≈ = _ⓘₕ_
  }
