{-# OPTIONS --without-K --safe #-}

module Categories.Adjoint.Instance.QuiverCategory where

-- "Free Category on a Quiver" is adjoint to Underlying Quiver

open import Level
open import Function using (_$_; flip) renaming (id to idFun; _∘_ to _⊚_)
open import Relation.Binary.PropositionalEquality as ≡
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Data.Quiver
open import Data.Quiver.Paths
import Data.Quiver.Morphism as QM
open QM using (Morphism; _≃_)

open import Categories.Adjoint
open import Categories.Category
import Categories.Category.Construction.FreeQuiver as FQ
open import Categories.Category.Construction.Quivers
open import Categories.Functor using (Functor)
open import Categories.Functor.Construction.FreeCategory
open import Categories.NaturalTransformation hiding (id)
import Categories.Morphism.Reasoning as MR

module _ (o ℓ e : Level) where

  GM : (X : Quiver o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)) → Morphism X (Underlying₀ (FQ.PathCategory X))
  GM X = let open Paths X in record { F₀ = idFun ; F₁ = return ; F-resp-≈ = λ f≈g → f≈g ◅ ε }

  module _ (X : Category o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)) where
    open Category X
    open HomReasoning
    open Paths (Underlying₀ X)

    -- "unwind" a path by using repeated composition
    unwind : {A B : Obj} → Star _⇒_ A B → A ⇒ B
    unwind = fold _⇒_ (flip _∘_) id

    unwind-◅◅ : {A B C : Obj} {f : Star _⇒_ A B} {g : Star _⇒_ B C} →
                unwind (f ◅◅ g) ≈ (unwind g) ∘ (unwind f)
    unwind-◅◅ {f = ε} {g} = Equiv.sym identityʳ
    unwind-◅◅ {f = x ◅ f} {g} = ∘-resp-≈ˡ (unwind-◅◅ {f = f} {g}) ○ assoc

    unwind-resp-≈ : {A B : Obj} {f g : Star _⇒_ A B} → FQ.[ Underlying₀ X ] f ≈* g → unwind f ≈ unwind g
    unwind-resp-≈ ε = Equiv.refl
    unwind-resp-≈ (x ◅ eq) = ∘-resp-≈ (unwind-resp-≈ eq) x

  module _ (X : Quiver o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)) where
    open Paths X

    zig′ : {A B : Quiver.Obj X} → (f : Star (Quiver._⇒_ X) A B) →
      FQ.[ X ] (unwind (FQ.PathCategory X)) (qmap (GM X) f) ≈* f
    zig′ ε        = ε
    zig′ (fs ◅ f) = Quiver.Equiv.refl X ◅ zig′ f

  module _ {X Y : Category o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)} (F : Functor X Y) where
    module X = Category X
    module Y = Category Y
    open Category.HomReasoning Y
    open Functor F
    comm : {A B : X.Obj} (f : Star X._⇒_ A B) → unwind Y (qmap (Underlying₁ F) f) Y.≈ F₁ (unwind X f)
    comm ε = Y.Equiv.sym identity
    comm (x ◅ f) = Y.Equiv.sym (homomorphism ○ Category.∘-resp-≈ˡ Y (Y.Equiv.sym (comm f)))

  Free⊣Underlying : Adjoint (FreeCategory {o} {o ⊔ ℓ} {o ⊔ ℓ ⊔ e}) Underlying
  Free⊣Underlying = record
    { unit = ntHelper record
      { η = GM
      ; commute = λ {X} {Y} f → let open Paths Y in record { F₀≡ = ≡.refl ; F₁≡ = Quiver.Equiv.refl Y ◅ ε }
      }
    ; counit = ntHelper record
      { η = λ X → record
        { F₀ = idFun
        ; F₁ = unwind X
        ; identity = Category.Equiv.refl X
        ; homomorphism = λ { {f = f} {g} → unwind-◅◅ X {f = f} {g} }
        ; F-resp-≈ = unwind-resp-≈ X
        }
      ; commute = λ {_} {Y} F → record
        { eq₀ = λ _ → refl
        ; eq₁ = λ f → toSquare Y (comm F f)
        }
      }
    ; zig = λ {G} → record
      { eq₀ = λ _ → refl
      ; eq₁ = λ f → toSquare (FQ.PathCategory G) (zig′ G f)
      }
    ; zag = λ {B} → record { F₀≡ = refl ; F₁≡ = Category.identityˡ B  }
    }
    where
    open MR
