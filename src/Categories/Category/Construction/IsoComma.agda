{-# OPTIONS --without-K --safe #-}
module Categories.Category.Construction.IsoComma where

open import Data.Product using (_×_; _,_; zip; map)
open import Level

open import Categories.Category using (Category; _[_,_]; _[_≈_]; _[_∘_]; module Definitions)
open import Categories.Functor using (Functor)
import Categories.Morphism.Reasoning as MR

private
  variable
    o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ o₃ ℓ₃ e₃ : Level

module _ {A : Category o₁ ℓ₁ e₁} {B : Category o₂ ℓ₂ e₂} {C : Category o₃ ℓ₃ e₃} where
  private
    module C = Category C
    module A = Category A
    module B = Category B

  open import Categories.Morphism C using (_≅_)

  record IsoCommaObj (F : Functor A C) (G : Functor B C) : Set (o₁ ⊔ o₂ ⊔ ℓ₃ ⊔ e₃) where
    open Functor F renaming (F₀ to F₀)
    open Functor G renaming (F₀ to G₀)
    field
      {a} : A.Obj
      {b} : B.Obj
      iso : (F₀ a) ≅ (G₀ b)

  record IsoComma⇒ {F : Functor A C} {G : Functor B C} (X Y : IsoCommaObj F G) : Set (ℓ₁ ⊔ ℓ₂ ⊔ e₃) where
    open IsoCommaObj X renaming (a to a₁; b to b₁; iso to iso₁)
    open IsoCommaObj Y renaming (a to a₂; b to b₂; iso to iso₂)
    open Functor F renaming (F₁ to F₁)
    open Functor G renaming (F₁ to G₁)
    open _≅_ using (from)
    field
      f       : A [ a₁ , a₂ ]
      g       : B [ b₁ , b₂ ]
      commute : (G₁ g C.∘ from iso₁) C.≈ (from iso₂ C.∘ F₁ f)

  IsoComma : Functor A C → Functor B C → Category _ _ _
  IsoComma F G = record
    { Obj         = IsoCommaObj F G
    ; _⇒_         = IsoComma⇒
    ; _≈_         = λ a b → f a A.≈ f b × g a B.≈ g b
    ; _∘_         = _∘′_
    ; id          = λ { {X} → record { f = A.id ; g = B.id ; commute = id-comm X } }
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
    } module IsoComma
    where
      module F = Functor F
      module G = Functor G

      open F using () renaming (F₀ to F₀; F₁ to F₁)
      open G using () renaming (F₀ to G₀; F₁ to G₁)
      open IsoComma⇒
      open _≅_ using (from)

      id-comm : (X : IsoCommaObj F G) → (G₁ B.id C.∘ from (IsoCommaObj.iso X)) C.≈ (from (IsoCommaObj.iso X) C.∘ F₁ A.id)
      id-comm X = begin
        G₁ B.id C.∘ from (IsoCommaObj.iso X)  ≈⟨ G.identity ⟩∘⟨refl ⟩
        C.id C.∘ from (IsoCommaObj.iso X)     ≈⟨ C.identityˡ ⟩
        from (IsoCommaObj.iso X)              ≈˘⟨ C.identityʳ ⟩
        from (IsoCommaObj.iso X) C.∘ C.id     ≈˘⟨ refl⟩∘⟨ F.identity ⟩
        from (IsoCommaObj.iso X) C.∘ F₁ A.id  ∎
        where
          open C.HomReasoning
          open MR C

      _∘′_ : ∀ {X Y Z : IsoCommaObj F G} → IsoComma⇒ Y Z → IsoComma⇒ X Y → IsoComma⇒ X Z
      _∘′_ {X} {Y} {Z} a₁ a₂ = record
        { f = A [ f₁ ∘ f₂ ]
        ; g = B [ g₁ ∘ g₂ ]
        ; commute = begin
          G₁ (g₁ B.∘ g₂) C.∘ from iso₁     ≈⟨ G.homomorphism ⟩∘⟨refl ○ C.assoc ⟩
          G₁ g₁ C.∘ (G₁ g₂ C.∘ from iso₁)  ≈⟨ refl⟩∘⟨ comm₂ ⟩
          G₁ g₁ C.∘ (from iso₂ C.∘ F₁ f₂)  ≈⟨ C.sym-assoc ⟩
          (G₁ g₁ C.∘ from iso₂) C.∘ F₁ f₂  ≈⟨ comm₁ ⟩∘⟨refl ⟩
          (from iso₃ C.∘ F₁ f₁) C.∘ F₁ f₂  ≈⟨ C.assoc ○ refl⟩∘⟨ ⟺ F.homomorphism ⟩
          from iso₃ C.∘ F₁ (f₁ A.∘ f₂)     ∎
        }
        where
          open C.HomReasoning
          open MR C
          open IsoCommaObj X renaming (iso to iso₁)
          open IsoCommaObj Y renaming (iso to iso₂)
          open IsoCommaObj Z renaming (iso to iso₃)
          open IsoComma⇒ a₁ renaming (f to f₁; g to g₁; commute to comm₁)
          open IsoComma⇒ a₂ renaming (f to f₂; g to g₂; commute to comm₂)

  infix 4 _↓≅_
  _↓≅_ : Functor A C → Functor B C → Category _ _ _
  _↓≅_ = IsoComma
