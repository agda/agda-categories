{-# OPTIONS --without-K --safe #-}
open import Categories.Category hiding (_[_,_])

module Categories.Object.Coproduct {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level
open import Function using (flip; _$_)

open Category 𝒞

open import Categories.Morphism.Reasoning 𝒞
open import Categories.Morphism 𝒞

open HomReasoning

private
  variable
    A B C D X Y Z : Obj
    f g h : A ⇒ B

record Coproduct (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  infix 10 [_,_]
  
  field
    A+B   : Obj
    i₁    : A ⇒ A+B
    i₂    : B ⇒ A+B
    [_,_] : A ⇒ C → B ⇒ C → A+B ⇒ C

    inject₁ : [ f , g ] ∘ i₁ ≈ f
    inject₂ : [ f , g ] ∘ i₂ ≈ g
    unique   : h ∘ i₁ ≈ f → h ∘ i₂ ≈ g → [ f , g ] ≈ h

  g-η : [ f ∘ i₁ , f ∘ i₂ ] ≈ f
  g-η = unique Equiv.refl Equiv.refl

  η : [ i₁ , i₂ ] ≈ id
  η = unique identityˡ identityˡ

  []-cong₂ : ∀ {C} → {f f′ : A ⇒ C} {g g′ : B ⇒ C} → f ≈ f′ → g ≈ g′ → [ f , g ] ≈ [ f′ , g′ ]
  []-cong₂ f≈f′ g≈g′ = unique (inject₁ ○ ⟺ f≈f′) (inject₂ ○ ⟺ g≈g′)

  ∘-distribˡ-[] : ∀ {f : A ⇒ C} {g : B ⇒ C} {q : C ⇒ D} → q ∘ [ f , g ] ≈ [ q ∘ f , q ∘ g ]
  ∘-distribˡ-[] = ⟺ $ unique (pullʳ inject₁) (pullʳ inject₂)

  unique′ : f ∘ i₁ ≈ g ∘ i₁ → f ∘ i₂ ≈ g ∘ i₂ → f ≈ g
  unique′ eq₁ eq₂ = ⟺ (unique eq₁ eq₂) ○ g-η

record IsCoproduct {A B A+B : Obj} (i₁ : A ⇒ A+B) (i₂ : B ⇒ A+B) : Set (o ⊔ ℓ ⊔ e) where
  field
    [_,_] : A ⇒ C → B ⇒ C → A+B ⇒ C

    inject₁ : [ f , g ] ∘ i₁ ≈ f
    inject₂ : [ f , g ] ∘ i₂ ≈ g
    unique   : h ∘ i₁ ≈ f → h ∘ i₂ ≈ g → [ f , g ] ≈ h

Coproduct⇒IsCoproduct : (c : Coproduct A B) → IsCoproduct (Coproduct.i₁ c) (Coproduct.i₂ c)
Coproduct⇒IsCoproduct c = record
  { [_,_] = [_,_]
  ; inject₁ = inject₁
  ; inject₂ = inject₂
  ; unique = unique
  }
  where
    open Coproduct c

IsCoproduct⇒Coproduct : ∀ {C} {i₁ : A ⇒ C} {i₂ : B ⇒ C} → IsCoproduct i₁ i₂ → Coproduct A B
IsCoproduct⇒Coproduct c = record
  { [_,_] = [_,_]
  ; inject₁ = inject₁
  ; inject₂ = inject₂
  ; unique = unique
  }
  where
    open IsCoproduct c
  
module _ {A B : Obj} where
  open Coproduct {A} {B} renaming ([_,_] to _[_,_])

  repack : (p₁ p₂ : Coproduct A B) → A+B p₁ ⇒ A+B p₂
  repack p₁ p₂ = p₁ [ i₁ p₂ , i₂ p₂ ]

  repack∘ : (p₁ p₂ p₃ : Coproduct A B) → repack p₂ p₃ ∘ repack p₁ p₂ ≈ repack p₁ p₃
  repack∘ p₁ p₂ p₃ = ⟺ $ unique p₁ 
    (glueTrianglesˡ (inject₁ p₂) (inject₁ p₁)) 
    (glueTrianglesˡ (inject₂ p₂) (inject₂ p₁))

  repack≡id : (p : Coproduct A B) → repack p p ≈ id
  repack≡id = η

  repack-cancel : (p₁ p₂ : Coproduct A B) → repack p₁ p₂ ∘ repack p₂ p₁ ≈ id
  repack-cancel p₁ p₂ = repack∘ p₂ p₁ p₂ ○ repack≡id p₂

up-to-iso : ∀ (p₁ p₂ : Coproduct A B) → Coproduct.A+B p₁ ≅ Coproduct.A+B p₂
up-to-iso p₁ p₂ = record
  { from = repack p₁ p₂
  ; to   = repack p₂ p₁
  ; iso  = record
    { isoˡ = repack-cancel p₂ p₁
    ; isoʳ = repack-cancel p₁ p₂
    }
  }

transport-by-iso : ∀ (p : Coproduct A B) → ∀ {X} → Coproduct.A+B p ≅ X → Coproduct A B
transport-by-iso p {X} p≅X = record
  { A+B = X
  ; i₁ = from ∘ i₁
  ; i₂ = from ∘ i₂
  ; [_,_] = λ h₁ h₂ → [ h₁ , h₂ ] ∘ to
  ; inject₁ = cancelInner isoˡ ○ inject₁
  ; inject₂ = cancelInner isoˡ ○ inject₂
  ; unique = λ {_ i l r} pf₁ pf₂ → begin
    [ l , r ] ∘ to                             ≈˘⟨ []-cong₂ pf₁ pf₂ ⟩∘⟨refl ⟩
    [ i ∘ from ∘ i₁ , i ∘ from ∘ i₂ ] ∘ to     ≈⟨ unique assoc assoc ⟩∘⟨refl ⟩
    (i ∘ from) ∘ to                            ≈⟨ cancelʳ isoʳ ⟩
    i                                          ∎
  }
  where open Coproduct p
        open _≅_ p≅X

Reversible : (p : Coproduct A B) → Coproduct B A
Reversible p = record
  { A+B       = A+B
  ; i₁        = i₂
  ; i₂        = i₁
  ; [_,_]     = flip [_,_]
  ; inject₁  = inject₂
  ; inject₂  = inject₁
  ; unique = flip unique
  }
  where open Coproduct p

Commutative : (p₁ : Coproduct A B) (p₂ : Coproduct B A) → Coproduct.A+B p₁ ≅ Coproduct.A+B p₂
Commutative p₁ p₂ = up-to-iso p₁ (Reversible p₂)

Associable : ∀ (p₁ : Coproduct X Y) (p₂ : Coproduct Y Z) (p₃ : Coproduct X (Coproduct.A+B p₂)) → Coproduct (Coproduct.A+B p₁) Z
Associable p₁ p₂ p₃ = record
  { A+B       = A+B p₃
  ; i₁        = p₁ [ i₁ p₃ , i₂ p₃ ∘ i₁ p₂ ]
  ; i₂        = i₂ p₃ ∘ i₂ p₂
  ; [_,_]     = λ f g → p₃ [ f ∘ i₁ p₁ , p₂ [ f ∘ i₂ p₁ , g ] ]
  ; inject₁  = λ {_ f g} → begin
    p₃ [ f ∘ i₁ p₁ , p₂ [ f ∘ i₂ p₁ , g ] ] ∘ p₁ [ i₁ p₃ , i₂ p₃ ∘ i₁ p₂ ] ≈⟨ ∘-distribˡ-[] p₁ ⟩
    p₁ [ p₃ [ f ∘ i₁ p₁ , p₂ [ f ∘ i₂ p₁ , g ] ] ∘ i₁ p₃ 
       , p₃ [ f ∘ i₁ p₁ , p₂ [ f ∘ i₂ p₁ , g ] ] ∘ i₂ p₃ ∘ i₁ p₂ ]         ≈⟨ []-cong₂ p₁ (inject₁ p₃) (glueTrianglesʳ (inject₂ p₃) (inject₁  p₂)) ⟩
    p₁ [ f ∘ i₁ p₁ , f ∘ i₂ p₁ ]                                           ≈⟨ g-η p₁ ⟩
    f                                                                      ∎
  ; inject₂  = λ {_ f g} → glueTrianglesʳ (inject₂ p₃) (inject₂ p₂)
  ; unique = λ {_ i f g} pf₁ pf₂ → begin
    p₃ [ f ∘ i₁ p₁ , p₂ [ f ∘ i₂ p₁ , g ] ]                   ≈⟨ []-cong₂ p₃ (∘-resp-≈ˡ (sym pf₁)) 
                                                                ([]-cong₂ p₂ (∘-resp-≈ˡ (sym pf₁)) (sym pf₂)) ⟩
    (p₃ [ (i ∘ p₁ [ i₁ p₃ , i₂ p₃ ∘ i₁ p₂ ]) ∘ i₁ p₁ 
        , p₂ [ (i ∘ p₁ [ i₁ p₃ , i₂ p₃ ∘ i₁ p₂ ]) ∘ i₂ p₁ 
             , i ∘ i₂ p₃ ∘ i₂ p₂ ] ])                         ≈⟨ []-cong₂ p₃ (pullʳ (inject₁ p₁)) 
                                                                ([]-cong₂ p₂ (trans (pullʳ (inject₂ p₁)) sym-assoc) 
                                                                             sym-assoc) ⟩
    (p₃ [ i ∘ i₁ p₃ 
        , p₂ [ (i ∘ i₂ p₃) ∘ i₁ p₂ , (i ∘ i₂ p₃) ∘ i₂ p₂ ] ]) ≈⟨ []-cong₂ p₃ refl (g-η p₂) ⟩
    (p₃ [ i ∘ i₁ p₃ , i ∘ i₂ p₃ ])                            ≈⟨ g-η p₃ ⟩
    i                                                         ∎
  }
  where
  open Coproduct renaming ([_,_] to _[_,_])
  open Equiv

Associative : ∀ (p₁ : Coproduct X Y) (p₂ : Coproduct Y Z)
                (p₃ : Coproduct X (Coproduct.A+B p₂)) (p₄ : Coproduct (Coproduct.A+B p₁) Z) →
                (Coproduct.A+B p₃) ≅ (Coproduct.A+B p₄)
Associative p₁ p₂ p₃ p₄ = up-to-iso (Associable p₁ p₂ p₃) p₄

Mobile : ∀ {A₁ B₁ A₂ B₂} (p : Coproduct A₁ B₁) → A₁ ≅ A₂ → B₁ ≅ B₂ → Coproduct A₂ B₂
Mobile p A₁≅A₂ B₁≅B₂ = record
  { A+B              = A+B
  ; i₁               = i₁ ∘ to A₁≅A₂
  ; i₂               = i₂ ∘ to B₁≅B₂
  ; [_,_]            = λ h k → [ h ∘ from A₁≅A₂ , k ∘ from B₁≅B₂ ]
  ; inject₁         = begin
    [ _ ∘ from A₁≅A₂ , _ ∘ from B₁≅B₂ ] ∘ i₁ ∘ to A₁≅A₂ ≈⟨ pullˡ inject₁ ⟩
    (_ ∘ from A₁≅A₂) ∘ to A₁≅A₂                         ≈⟨ cancelʳ (isoʳ A₁≅A₂) ⟩
    _                                                   ∎
  ; inject₂         = begin
    [ _ ∘ from A₁≅A₂ , _ ∘ from B₁≅B₂ ] ∘ i₂ ∘ to B₁≅B₂ ≈⟨ pullˡ inject₂ ⟩
    (_ ∘ from B₁≅B₂) ∘ to B₁≅B₂                         ≈⟨ cancelʳ (isoʳ B₁≅B₂) ⟩
    _                                                   ∎
  ; unique        = λ pfˡ pfʳ → unique (switch-fromtoʳ (≅-sym A₁≅A₂) ((assoc ○ pfˡ))) (switch-fromtoʳ (≅-sym B₁≅B₂) ((assoc ○ pfʳ)))
  }
  where open Coproduct p
        open _≅_
        open ≅ using () renaming (sym to ≅-sym)
