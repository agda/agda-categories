{-# OPTIONS --without-K --safe #-}
module Categories.Category.Construction.Comma where

open import Data.Product using (_×_; ∃; _,_; proj₁; proj₂; zip; map)
open import Level
open import Relation.Binary using (Rel)

open import Categories.Category.Instance.One
open import Categories.Category using (Category; _[_,_]; _[_∘_]; module Definitions)
open import Categories.Functor using (Functor)
open import Categories.Functor.Construction.Constant using (const!)
import Categories.Morphism.Reasoning as MR

private
  variable
    o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ o₃ ℓ₃ e₃ : Level

-- things go odd with generalized variables for A B C, use anonymous module instead
module _ {A : Category o₁ ℓ₁ e₁}  {B : Category o₂ ℓ₂ e₂} {C : Category o₃ ℓ₃ e₃} where
  private
    module C = Category C
    module A = Category A
    module B = Category B

  record CommaObj (T : Functor A C) (S : Functor B C) : Set (o₁ ⊔ o₂ ⊔ ℓ₃) where
    open Category
    open Functor T renaming (F₀ to T₀)
    open Functor S renaming (F₀ to S₀)
    field
      {α} : Obj A
      {β} : Obj B
      f   : C [ T₀ α , S₀ β ]

  record Comma⇒ {T : Functor A C} {S : Functor B C} (X₁ X₂ : CommaObj T S) : Set (ℓ₁ ⊔ ℓ₂ ⊔ e₃) where
    open CommaObj X₁ renaming (α to α₁; β to β₁; f to f₁)
    open CommaObj X₂ renaming (α to α₂; β to β₂; f to f₂)
    open Functor T renaming (F₁ to T₁)
    open Functor S renaming (F₁ to S₁)
    open Definitions C

    field
      g       : A [ α₁ , α₂ ]
      h       : B [ β₁ , β₂ ]
      commute : CommutativeSquare f₁ (T₁ g) (S₁ h) f₂

  Comma : Functor A C → Functor B C → Category _ _ _
  Comma T S = record
    { Obj         = CommaObj T S
    ; _⇒_         = Comma⇒
    ; _≈_         = λ a₁ a₂ → g a₁ A.≈ g a₂ × h a₁ B.≈ h a₂
    ; _∘_         = _∘′_
    ; id          = record { g = A.id ; h = B.id ; commute = id-comm }
    ; assoc       = A.assoc , B.assoc
    ; sym-assoc   = A.sym-assoc , B.sym-assoc
    ; identityˡ   = A.identityˡ , B.identityˡ
    ; identityʳ   = A.identityʳ , B.identityʳ
    ; identity²   = A.identity² , B.identity²
    ; equiv = record
      { refl  = A.Equiv.refl , B.Equiv.refl
      ; sym   = map A.Equiv.sym B.Equiv.sym
      ; trans = zip A.Equiv.trans B.Equiv.trans
      }
    ; ∘-resp-≈    = zip A.∘-resp-≈ B.∘-resp-≈
    } module Comma
    where
      module T = Functor T
      module S = Functor S

      open T using () renaming (F₀ to T₀; F₁ to T₁)
      open S using () renaming (F₀ to S₀; F₁ to S₁)
      open Comma⇒
      id-comm : {E : CommaObj T S} → let open CommaObj E in
         (S₁ B.id C.∘ f) C.≈ f C.∘ T₁ A.id
      id-comm {E} = begin
        (S₁ B.id C.∘ f) ≈⟨ S.identity ⟩∘⟨refl ⟩
        C.id C.∘ f      ≈⟨ id-comm-sym ⟩
        f C.∘ C.id      ≈˘⟨ refl⟩∘⟨ T.identity ⟩
        f C.∘ T₁ A.id ∎
        where
          open C.HomReasoning
          open CommaObj E
          open MR C

      _∘′_ : ∀ {X₁ X₂ X₃} → Comma⇒ X₂ X₃ → Comma⇒ X₁ X₂ → Comma⇒ X₁ X₃
      _∘′_ {X₁} {X₂} {X₃} a₁ a₂ = record
        { g = A [ g₁ ∘ g₂ ]
        ; h = B [ h₁ ∘ h₂ ]
        ; commute = begin
          S₁ (h₁ B.∘ h₂) C.∘ f₁      ≈⟨ S.homomorphism ⟩∘⟨refl ○ C.assoc ⟩
          S₁ h₁ C.∘  (S₁ h₂ C.∘ f₁)  ≈⟨  refl⟩∘⟨ commutes₂ ⟩
          S₁ h₁ C.∘  (f₂ C.∘ T₁ g₂)  ≈⟨ C.sym-assoc ⟩
          (S₁ h₁ C.∘  f₂) C.∘ T₁ g₂  ≈⟨ commutes₁ ⟩∘⟨refl ⟩
          (f₃ C.∘ T₁ g₁) C.∘ T₁ g₂   ≈⟨ C.assoc ○ refl⟩∘⟨ ⟺ T.homomorphism ⟩
          f₃ C.∘ T₁ (g₁ A.∘ g₂) ∎
        }
        where
        open C.HomReasoning
        open Comma⇒ a₁ renaming (g to g₁; h to h₁; commute to commutes₁)
        open Comma⇒ a₂ renaming (g to g₂; h to h₂; commute to commutes₂)
        open CommaObj X₁ renaming (α to α₁; β to β₁; f to f₁)
        open CommaObj X₂ renaming (α to α₂; β to β₂; f to f₂)
        open CommaObj X₃ renaming (α to α₃; β to β₃; f to f₃)

  infix 4 _↓_
  _↓_ : (S : Functor A C) (T : Functor B C) → Category _ _ _
  S ↓ T = Comma S T

  Dom : (T : Functor A C) → (S : Functor B C) → Functor (Comma T S) A
  Dom T S = record
    { F₀ = CommaObj.α
    ; F₁ = Comma⇒.g
    ; identity = refl
    ; homomorphism = refl
    ; F-resp-≈ = proj₁
    }
   where
    open Comma T S
    open A.Equiv

  Cod : (T : Functor A C) → (S : Functor B C) → Functor (Comma T S) B
  Cod T S = record
    { F₀ = CommaObj.β
    ; F₁ = Comma⇒.h
    ; identity = refl
    ; homomorphism = refl
    ; F-resp-≈ = proj₂
    }
   where
    open Comma T S
    open B.Equiv

module _ {C : Category o₁ ℓ₁ e₁} {D : Category o₂ ℓ₂ e₂} where
  private
    module C = Category C

  infix 4 _↙_ _↘_
  _↙_ : (X : C.Obj) (T : Functor D C) → Category _ _ _
  X ↙ T = const! X ↓ T

  _↘_ : (S : Functor D C) (X : C.Obj) → Category _ _ _
  S ↘ X = S ↓ const! X
