{-# OPTIONS --without-K --safe #-}

open import Categories.Category

-- a zero object is both terminal and initial.
module Categories.Object.Zero {o ℓ e} (C : Category o ℓ e) where

open import Level using (_⊔_)

open import Categories.Object.Terminal C
open import Categories.Object.Initial C

open import Categories.Morphism C
open import Categories.Morphism.Reasoning C

open Category C
open HomReasoning

record Zero : Set (o ⊔ ℓ ⊔ e) where
 field
   zero : Obj
   !    : ∀ {A} → zero ⇒ A
   ¡    : ∀ {A} → A ⇒ zero

 zero⇒ : ∀ {A B : Obj} → A ⇒ B
 zero⇒ {A} = ! ∘ ¡

 field
   !-unique : ∀ {A} (f : zero ⇒ A) → ! ≈ f
   ¡-unique : ∀ {A} (f : A ⇒ zero) → ¡ ≈ f

 ¡-unique₂ : ∀ {A} (f g : A ⇒ zero) → f ≈ g
 ¡-unique₂ f g = ⟺ (¡-unique f) ○ ¡-unique g

 !-unique₂ : ∀ {A} (f g : zero ⇒ A) → f ≈ g
 !-unique₂ f g = ⟺ (!-unique f) ○ !-unique g

 zero-∘ˡ : ∀ {X Y Z} → (f : Y ⇒ Z) → f ∘ zero⇒ {X} ≈ zero⇒
 zero-∘ˡ f = pullˡ (⟺ (!-unique (f ∘ !)))

 zero-∘ʳ : ∀ {X Y Z} → (f : X ⇒ Y) → zero⇒ {Y} {Z} ∘ f ≈ zero⇒
 zero-∘ʳ f = pullʳ (⟺ (¡-unique (¡ ∘ f)))


 initial : Initial
 initial = record
   { ⊥        = zero
   ; ⊥-is-initial = record
     { !        = !
     ; !-unique = !-unique
     }
   }

 terminal : Terminal
 terminal = record
   { ⊤        = zero
   ; ⊤-is-terminal = record
     { !        = ¡
     ; !-unique = ¡-unique
     }
   }

 module initial  = Initial initial
 module terminal = Terminal terminal

 !-Mono : ∀ {A} → Mono (! {A})
 !-Mono = from-⊤-is-Mono {t = terminal} !

 ¡-Epi : ∀ {A} → Epi (¡ {A})
 ¡-Epi = to-⊥-is-Epi {i = initial} ¡
