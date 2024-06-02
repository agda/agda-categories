{-# OPTIONS --safe --without-K #-}

module Categories.Functor.Displayed where

open import Function.Base using () renaming (id to id→; _∘_ to _∙_)
open import Level

open import Categories.Category
open import Categories.Category.Displayed
open import Categories.Functor

private
  variable
    o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ o‴ ℓ‴ e‴  : Level
    B₁ B₂ B₃ : Category o ℓ e

record DisplayedFunctor {B₁ : Category o ℓ e} {B₂ : Category o′ ℓ′ e′} (C : Displayed B₁ o″ ℓ″ e″) (D : Displayed B₂ o‴ ℓ‴ e‴) (F : Functor B₁ B₂) : Set (o ⊔ ℓ ⊔ e ⊔ o″ ⊔ ℓ″ ⊔ e″ ⊔ o‴ ⊔ ℓ‴ ⊔ e‴) where
  private
    module C = Displayed C
    module D = Displayed D
    module F = Functor F
  field
    F₀′ : ∀ {X} → C.Obj[ X ] → D.Obj[ F.₀ X ]
    F₁′ : ∀ {X Y} {f : B₁ [ X , Y ]} {X′ Y′} → X′ C.⇒[ f ] Y′ → F₀′ X′ D.⇒[ F.₁ f ] F₀′ Y′
    identity′ : ∀ {X} {X′ : C.Obj[ X ]} → F₁′ (C.id′ {X = X′}) D.≈[ F.identity ] D.id′
    homomorphism′ : ∀ {X Y Z} {X′ : C.Obj[ X ]} {Y′ : C.Obj[ Y ]} {Z′ : C.Obj[ Z ]}
                      {f : B₁ [ X , Y ]} {g : B₁ [ Y , Z ]} {f′ : X′ C.⇒[ f ] Y′} {g′ : Y′ C.⇒[ g ] Z′}
                    → F₁′ (g′ C.∘′ f′) D.≈[ F.homomorphism ] F₁′ g′ D.∘′ F₁′ f′
    F′-resp-≈[] : ∀ {X Y} {X′ : C.Obj[ X ]} {Y′ : C.Obj[ Y ]}
                    {f g : B₁ [ X , Y ]} {f′ : X′ C.⇒[ f ] Y′} {g′ : X′ C.⇒[ g ] Y′}
                  → {p : B₁ [ f ≈ g ]} → f′ C.≈[ p ] g′
                  → F₁′ f′ D.≈[ F.F-resp-≈ p ] F₁′ g′

  ₀′ = F₀′
  ₁′ = F₁′

  op′ : DisplayedFunctor C.op′ D.op′ F.op
  op′ = record
    { F₀′ = F₀′
    ; F₁′ = F₁′
    ; identity′ = identity′
    ; homomorphism′ = homomorphism′
    ; F′-resp-≈[] = F′-resp-≈[]
    }

id′ : ∀ {B : Category o ℓ e} {C : Displayed B o′ ℓ′ e′} → DisplayedFunctor C C id
id′ {C = C} = record
  { F₀′ = id→
  ; F₁′ = id→
  ; identity′ = Displayed.Equiv′.refl′ C
  ; homomorphism′ = Displayed.Equiv′.refl′ C
  ; F′-resp-≈[] = id→
  }

_∘F′_ : ∀ {C : Displayed B₁ o ℓ e} {D : Displayed B₂ o′ ℓ′ e′} {E : Displayed B₃ o″ ℓ″ e″}
          {F : Functor B₂ B₃} {G : Functor B₁ B₂}
        → DisplayedFunctor D E F → DisplayedFunctor C D G → DisplayedFunctor C E (F ∘F G)
_∘F′_  {C = C} {D = D} {E = E} F′ G′ = record
   { F₀′ = F′.₀′ ∙ G′.₀′
   ; F₁′ = F′.₁′ ∙ G′.₁′
   ; identity′ = begin′
     F′.₁′ (G′.₁′ C.id′) ≈[]⟨ F′.F′-resp-≈[] G′.identity′ ⟩
     F′.₁′ D.id′         ≈[]⟨ F′.identity′ ⟩
     E.id′               ∎′
   ; homomorphism′ = λ {_} {_} {_} {_} {_} {_} {_} {_} {f′} {g′} → begin′
     F′.₁′ (G′.₁′ (g′ C.∘′ f′))               ≈[]⟨ F′.F′-resp-≈[] G′.homomorphism′ ⟩
     F′.₁′ (G′.₁′ g′ D.∘′ G′.₁′ f′)           ≈[]⟨ F′.homomorphism′ ⟩
     (F′.₁′ (G′.₁′ g′) E.∘′ F′.₁′ (G′.₁′ f′)) ∎′
   ; F′-resp-≈[] = F′.F′-resp-≈[] ∙ G′.F′-resp-≈[]
   }
   where
     module C = Displayed C
     module D = Displayed D
     module E = Displayed E
     open E.HomReasoning′
     module F′ = DisplayedFunctor F′
     module G′ = DisplayedFunctor G′
