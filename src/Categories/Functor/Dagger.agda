{-# OPTIONS --safe --without-K #-}

module Categories.Functor.Dagger where

open import Categories.Category.Dagger
open import Categories.Functor renaming (id to idF)

open import Level

private
  variable
    o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ : Level

record DaggerFunctor (C : DaggerCategory o ℓ e) (D : DaggerCategory o′ ℓ′ e′) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private
    module C = DaggerCategory C
    module D = DaggerCategory D
  field
    functor : Functor C.C D.C

  open Functor functor public

  field
    F-resp-† : ∀ {X Y} {f : X C.⇒ Y} → F₁ f D.† D.≈ F₁ (f C.†)
  
id : ∀ {C : DaggerCategory o ℓ e} → DaggerFunctor C C
id {C = C} = record
  { functor = idF
  ; F-resp-† = DaggerCategory.Equiv.refl C
  }

_∘F†_ : ∀ {C : DaggerCategory o ℓ e} {D : DaggerCategory o′ ℓ′ e′} {E : DaggerCategory o″ ℓ″ e″}
      → DaggerFunctor D E → DaggerFunctor C D → DaggerFunctor C E
_∘F†_ {E = E} F G = record
  { functor = F.functor ∘F G.functor
  ; F-resp-† = DaggerCategory.Equiv.trans E F.F-resp-† (F.F-resp-≈ G.F-resp-†)
  }
  where
    module F = DaggerFunctor F
    module G = DaggerFunctor G
