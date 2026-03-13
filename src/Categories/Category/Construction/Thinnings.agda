{-# OPTIONS --safe --without-K #-}

-- A generalised form of Thinnings, as described in Conor Mc Bride's Everybody's Got To Be Somewhere
-- The traditional definition can be recovered by setting C to a discrete category

open import Categories.Category

module Categories.Category.Construction.Thinnings {o ℓ e} (C : Category o ℓ e) where

open import Categories.Object.Initial
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Binary.Sublist.Heterogeneous
open import Data.List.Relation.Binary.Sublist.Heterogeneous.Properties
open import Function.Base using (flip)
open import Level

open Category C

data _≈ᵗ_ : ∀ {X Y : List Obj} → Sublist _⇒_ X Y → Sublist _⇒_ X Y → Set (o ⊔ ℓ ⊔ e) where
  [] : [] ≈ᵗ []
  _∷ʳ_ : ∀ {xs ys} {fs gs : Sublist _⇒_ xs ys} y → fs ≈ᵗ gs → (y ∷ʳ fs) ≈ᵗ (y ∷ʳ gs)
  _∷_ : ∀ {x xs y ys} {f g : x ⇒ y} {fs gs : Sublist _⇒_ xs ys} → f ≈ g → fs ≈ᵗ gs → (f ∷ fs) ≈ᵗ (g ∷ gs)

private
  ≈ᵗ-refl : ∀ {X Y} {fs : Sublist _⇒_ X Y} → fs ≈ᵗ fs
  ≈ᵗ-refl {fs = []} = []
  ≈ᵗ-refl {fs = y ∷ʳ fs} = y ∷ʳ ≈ᵗ-refl
  ≈ᵗ-refl {fs = _ ∷ fs} = Equiv.refl ∷ ≈ᵗ-refl

  ≈ᵗ-sym : ∀ {X Y} {fs gs : Sublist _⇒_ X Y} → fs ≈ᵗ gs → gs ≈ᵗ fs
  ≈ᵗ-sym [] = []
  ≈ᵗ-sym (y ∷ʳ fs≈gs) = y ∷ʳ ≈ᵗ-sym fs≈gs
  ≈ᵗ-sym (f≈g ∷ fs≈gs) = Equiv.sym f≈g ∷ ≈ᵗ-sym fs≈gs

  ≈ᵗ-trans : ∀ {X Y} {fs gs hs : Sublist _⇒_ X Y} → fs ≈ᵗ gs → gs ≈ᵗ hs → fs ≈ᵗ hs
  ≈ᵗ-trans [] [] = []
  ≈ᵗ-trans (y ∷ʳ fs≈gs) (.y ∷ʳ gs≈hs) = y ∷ʳ ≈ᵗ-trans fs≈gs gs≈hs
  ≈ᵗ-trans (f≈g ∷ fs≈gs) (g≈h ∷ gs≈hs) = Equiv.trans f≈g g≈h ∷ ≈ᵗ-trans fs≈gs gs≈hs

  assocᵗ : ∀ {W X Y Z : List Obj} {f : Sublist _⇒_ W X} {g : Sublist _⇒_ X Y} {h : Sublist _⇒_ Y Z}
         → trans (flip _∘_) f (trans (flip _∘_) g h) ≈ᵗ trans (flip _∘_) (trans (flip _∘_) f g) h
  assocᵗ {f = []} {g = []} {h = []} = []
  assocᵗ {f = []} {g = []} {h = y ∷ʳ _} = y ∷ʳ assocᵗ
  assocᵗ {f = []} {g = _ ∷ʳ _} {h = y ∷ʳ _} = y ∷ʳ assocᵗ
  assocᵗ {f = _ ∷ʳ _} {g = _ ∷ʳ _} {h = y ∷ʳ _} = _ ∷ʳ assocᵗ
  assocᵗ {f = _ ∷ _} {g = _ ∷ʳ _} {h = y ∷ʳ _} = _ ∷ʳ assocᵗ
  assocᵗ {f = _ ∷ʳ _} {g = _ ∷ _} {h = y ∷ʳ _} = _ ∷ʳ assocᵗ
  assocᵗ {f = _ ∷ _} {g = _ ∷ _} {h = y ∷ʳ _} = _ ∷ʳ assocᵗ
  assocᵗ {f = []} {g = _ ∷ʳ _} {h = _ ∷ _} = _ ∷ʳ assocᵗ
  assocᵗ {f = _ ∷ʳ _} {g = _ ∷ʳ _} {h = _ ∷ _} = _ ∷ʳ assocᵗ
  assocᵗ {f = _ ∷ _} {g = _ ∷ʳ _} {h = _ ∷ _} = _ ∷ʳ assocᵗ
  assocᵗ {f = _ ∷ʳ _} {g = _ ∷ _} {h = _ ∷ _} = _ ∷ʳ assocᵗ
  assocᵗ {f = _ ∷ _} {g = _ ∷ _} {h = _ ∷ _} = assoc ∷ assocᵗ

  sym-assocᵗ : ∀ {W X Y Z : List Obj} {f : Sublist _⇒_ W X} {g : Sublist _⇒_ X Y} {h : Sublist _⇒_ Y Z}
             → trans (flip _∘_) (trans (flip _∘_) f g) h ≈ᵗ trans (flip _∘_) f (trans (flip _∘_) g h)
  sym-assocᵗ {f = []} {g = []} {h = []} = []
  sym-assocᵗ {f = []} {g = []} {h = _ ∷ʳ _} = _ ∷ʳ sym-assocᵗ
  sym-assocᵗ {f = []} {g = _ ∷ʳ _} {h = _ ∷ʳ _} = _ ∷ʳ sym-assocᵗ
  sym-assocᵗ {f = _ ∷ʳ _} {g = _ ∷ʳ _} {h = _ ∷ʳ _} = _ ∷ʳ sym-assocᵗ
  sym-assocᵗ {f = _ ∷ _} {g = _ ∷ʳ _} {h = _ ∷ʳ _} = _ ∷ʳ sym-assocᵗ
  sym-assocᵗ {f = _ ∷ʳ _} {g = _ ∷ _} {h = _ ∷ʳ _} = _ ∷ʳ sym-assocᵗ
  sym-assocᵗ {f = _ ∷ _} {g = _ ∷ _} {h = _ ∷ʳ _} = _ ∷ʳ sym-assocᵗ
  sym-assocᵗ {f = []} {g = _ ∷ʳ _} {h = _ ∷ _} = _ ∷ʳ sym-assocᵗ
  sym-assocᵗ {f = _ ∷ʳ _} {g = _ ∷ʳ _} {h = _ ∷ _} = _ ∷ʳ sym-assocᵗ
  sym-assocᵗ {f = _ ∷ _} {g = _ ∷ʳ _} {h = _ ∷ _} = _ ∷ʳ sym-assocᵗ
  sym-assocᵗ {f = _ ∷ʳ _} {g = _ ∷ _} {h = _ ∷ _} = _ ∷ʳ sym-assocᵗ
  sym-assocᵗ {f = _ ∷ _} {g = _ ∷ _} {h = _ ∷ _} = sym-assoc ∷ sym-assocᵗ

  identityˡᵗ : ∀ {X Y} {f : Sublist _⇒_ X Y} → trans (flip _∘_) f (refl id) ≈ᵗ f
  identityˡᵗ {f = []} = []
  identityˡᵗ {f = _ ∷ʳ _} = _ ∷ʳ identityˡᵗ
  identityˡᵗ {f = _ ∷ _} = identityˡ ∷ identityˡᵗ

  identityʳᵗ : ∀ {X Y} {f : Sublist _⇒_ X Y} → trans (flip _∘_) (refl id) f ≈ᵗ f
  identityʳᵗ {f = []} = []
  identityʳᵗ {f = _ ∷ʳ _} = _ ∷ʳ identityʳᵗ
  identityʳᵗ {f = _ ∷ _} = identityʳ ∷ identityʳᵗ

  identity²ᵗ : ∀ {X} → trans (flip _∘_) (refl id) (refl id) ≈ᵗ refl id {x = X}
  identity²ᵗ {[]} = []
  identity²ᵗ {x ∷ xs} = identity² ∷ identity²ᵗ

  ∘-resp-≈ᵗ : ∀ {X Y Z} {f h : Sublist _⇒_ Y Z} {g i : Sublist _⇒_ X Y}
            → f ≈ᵗ h → g ≈ᵗ i → trans (flip _∘_) g f ≈ᵗ trans (flip _∘_) i h
  ∘-resp-≈ᵗ [] [] = []
  ∘-resp-≈ᵗ (_ ∷ʳ f≈h) [] = _ ∷ʳ ∘-resp-≈ᵗ f≈h []
  ∘-resp-≈ᵗ (_ ∷ʳ f≈h) (_ ∷ʳ g≈i) = _ ∷ʳ ∘-resp-≈ᵗ f≈h (_ ∷ʳ g≈i)
  ∘-resp-≈ᵗ (_ ∷ʳ f≈h) (eq ∷ g≈i) = _ ∷ʳ ∘-resp-≈ᵗ f≈h (eq ∷ g≈i)
  ∘-resp-≈ᵗ (_ ∷ f≈h) (_ ∷ʳ g≈i) = _ ∷ʳ ∘-resp-≈ᵗ f≈h g≈i
  ∘-resp-≈ᵗ (eq₁ ∷ f≈h) (eq₂ ∷ g≈i) = ∘-resp-≈ eq₁ eq₂ ∷ ∘-resp-≈ᵗ f≈h g≈i

Thinnings : Category o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e)
Thinnings = record
  { Obj = List Obj
  ; _⇒_ = Sublist _⇒_
  ; _≈_ = _≈ᵗ_
  ; id = refl id
  ; _∘_ = flip (trans (flip _∘_))
  ; assoc = assocᵗ
  ; sym-assoc = sym-assocᵗ
  ; identityˡ = identityˡᵗ
  ; identityʳ = identityʳᵗ
  ; identity² = identity²ᵗ
  ; equiv = record
    { refl = ≈ᵗ-refl
    ; sym = ≈ᵗ-sym
    ; trans = ≈ᵗ-trans
    }
  ; ∘-resp-≈ = ∘-resp-≈ᵗ
  }

[]-initial : IsInitial Thinnings []
[]-initial = record
  { ! = Sublist-[]-universal _
  ; !-unique = λ f → Category.Equiv.reflexive Thinnings (Sublist-[]-irrelevant _ f)
  }

initial : Initial Thinnings
initial = record { ⊥-is-initial = []-initial }
