{-# OPTIONS --without-K --safe #-}

open import Categories.Category

-- this module characterizes a category of all equalizer indexed by I.
-- this notion formalizes a category with all equalizer up to certain cardinal.
module Categories.Diagram.Equalizer.Indexed {o ℓ e} (C : Category o ℓ e) where

open import Level

open Category C

record IndexedEqualizerOf {i} {I : Set i} {A B : Obj} (M : I → A ⇒ B) : Set (i ⊔ o ⊔ e ⊔ ℓ) where
  field
    E   : Obj
    arr : E ⇒ A

    -- a reference morphism
    ref : E ⇒ B
    equality  : ∀ i → M i ∘ arr ≈ ref
    equalize  : ∀ {X} (h : X ⇒ A) (r : X ⇒ B) → (∀ i → M i ∘ h ≈ r) → X ⇒ E
    universal : ∀ {X} (h : X ⇒ A) (r : X ⇒ B) (eq : ∀ i → M i ∘ h ≈ r) → h ≈ arr ∘ equalize h r eq
    unique    : ∀ {X} {l : X ⇒ E} (h : X ⇒ A) (r : X ⇒ B) (eq : ∀ i → M i ∘ h ≈ r) → h ≈ arr ∘ l → l ≈ equalize h r eq

record IndexedEqualizer {i} (I : Set i) : Set (i ⊔ o ⊔ e ⊔ ℓ) where
  field
    A B         : Obj
    M           : I → A ⇒ B
    equalizerOf : IndexedEqualizerOf M

  open IndexedEqualizerOf equalizerOf public

AllEqualizers : ∀ i → Set (o ⊔ ℓ ⊔ e ⊔ suc i)
AllEqualizers i = (I : Set i) → IndexedEqualizer I

AllEqualizersOf : ∀ i → Set (o ⊔ ℓ ⊔ e ⊔ suc i)
AllEqualizersOf i = ∀ {I : Set i} {A B : Obj} (M : I → A ⇒ B) → IndexedEqualizerOf M
