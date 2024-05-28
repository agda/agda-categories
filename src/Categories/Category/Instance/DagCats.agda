{-# OPTIONS --safe --without-K #-}

module Categories.Category.Instance.DagCats where

open import Categories.Category.Core using (Category)
open import Categories.Category.Dagger using (DaggerCategory)
open import Categories.Functor.Dagger using (DaggerFunctor; id; _∘F†_)
open import Categories.NaturalTransformation.NaturalIsomorphism

open import Function.Base using (_on_)
open import Level using (suc; _⊔_)

DagCats : ∀ o ℓ e → Category (suc (o ⊔ ℓ ⊔ e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
DagCats o ℓ e = record
  { Obj = DaggerCategory o ℓ e
  ; _⇒_ = DaggerFunctor
  ; _≈_ = NaturalIsomorphism on functor
  ; id = id
  ; _∘_ = _∘F†_
  ; assoc = λ {_ _ _ _ F G H} → associator (functor F) (functor G) (functor H)
  ; sym-assoc = λ {_ _ _ _ F G H} → sym (associator (functor F) (functor G) (functor H))
  ; identityˡ = unitorˡ
  ; identityʳ = unitorʳ
  ; identity² = unitor²
  ; equiv = record
    { refl = refl
    ; sym = sym
    ; trans = trans
    }
  ; ∘-resp-≈ = _ⓘₕ_
  } where open DaggerFunctor
