{-# OPTIONS --safe --without-K #-}

module Categories.Functor.Displayed.Properties where

open import Categories.Category
open import Categories.Category.Displayed
open import Categories.Functor
open import Categories.Functor.Displayed
open import Categories.Functor.Properties
open import Categories.Morphism
open import Categories.Morphism.Displayed

module _
  {o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ o‴ ℓ‴ e‴}
  {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {F : Functor C D}
  {C′ : Displayed C o″ ℓ″ e″} {D′ : Displayed D o‴ ℓ‴ e‴} (F′ : DisplayedFunctor C′ D′ F)
  where

  private
    module C = Category C
--    module F = Functor F
    module C′ = Displayed C′
    module D′ = Displayed D′
    module F′ = DisplayedFunctor F′

  open Definitions
  open Definitions′

  [_]-resp-∘′ : ∀ {X Y Z} {f : Y C.⇒ Z} {g : X C.⇒ Y} {h : X C.⇒ Z} {f∘g≈h : f C.∘ g C.≈ h}
                  {X′  : C′.Obj[ X ]} {Y′ : C′.Obj[ Y ]} {Z′ : C′.Obj[ Z ]}
                  {f′ : Y′ C′.⇒[ f ] Z′} {g′ : X′ C′.⇒[ g ] Y′} {h′ : X′ C′.⇒[ h ] Z′}
                → f′ C′.∘′ g′ C′.≈[ f∘g≈h ] h′
                → F′.₁′ f′ D′.∘′ F′.₁′ g′ D′.≈[ [ F ]-resp-∘ f∘g≈h ] F′.₁′ h′
  [_]-resp-∘′ {f′ = f′} {g′ = g′} {h′ = h′} eq = begin′
    F′.₁′ f′ D′.∘′ F′.₁′ g′ ≈˘[]⟨ F′.homomorphism′ ⟩
    F′.₁′ (f′ C′.∘′ g′)     ≈[]⟨ F′.F′-resp-≈[] eq ⟩
    F′.₁′ h′                ∎′
    where open D′.HomReasoning′

  [_]-resp-square′ : ∀ {W X Y Z} {f : W C.⇒ X} {g : W C.⇒ Y} {h : X C.⇒ Z} {i : Y C.⇒ Z} {sq : CommutativeSquare C f g h i}
                       {W′ : C′.Obj[ W ]} {X′ : C′.Obj[ X ]} {Y′ : C′.Obj[ Y ]} {Z′ : C′.Obj[ Z ]}
                       {f′ : W′ C′.⇒[ f ] X′} {g′ : W′ C′.⇒[ g ] Y′} {h′ : X′ C′.⇒[ h ] Z′} {i′ : Y′ C′.⇒[ i ] Z′}
                    → CommutativeSquare′ C′ f′ g′ h′ i′ sq
                    → CommutativeSquare′ D′ (F′.₁′ f′) (F′.₁′ g′) (F′.₁′ h′) (F′.₁′ i′) ([ F ]-resp-square sq)
  [_]-resp-square′ {f′ = f′} {g′ = g′} {h′ = h′} {i′ = i′} sq′ = begin′
    F′.₁′ h′ D′.∘′ F′.₁′ f′ ≈˘[]⟨ F′.homomorphism′ ⟩
    F′.₁′ (h′ C′.∘′ f′)     ≈[]⟨ F′.F′-resp-≈[] sq′ ⟩
    F′.₁′ (i′ C′.∘′ g′)     ≈[]⟨ F′.homomorphism′ ⟩
    F′.₁′ i′ D′.∘′ F′.₁′ g′ ∎′
    where open D′.HomReasoning′

  [_]-resp-DisplayedIso : ∀ {X Y} {f : X C.⇒ Y} {g : Y C.⇒ X} {iso : Iso C f g}
                            {X′ : C′.Obj[ X ]} {Y′ : C′.Obj[ Y ]} {f′ : X′ C′.⇒[ f ] Y′} {g′ : Y′ C′.⇒[ g ] X′}
                          → DisplayedIso C′ f′ g′ iso → DisplayedIso D′ (F′.₁′ f′) (F′.₁′ g′) ([ F ]-resp-Iso iso)
  [_]-resp-DisplayedIso {f′ = f′} {g′ = g′} diso = record
    { isoˡ′ = begin′
      F′.₁′ g′ D′.∘′ F′.₁′ f′ ≈[]⟨ [ isoˡ′ ]-resp-∘′ ⟩
      F′.₁′ C′.id′            ≈[]⟨ F′.identity′ ⟩
      D′.id′                  ∎′
    ; isoʳ′ = begin′
      F′.₁′ f′ D′.∘′ F′.₁′ g′ ≈[]⟨ [ isoʳ′ ]-resp-∘′ ⟩
      F′.₁′ C′.id′            ≈[]⟨ F′.identity′ ⟩
      D′.id′                  ∎′
    }
    where
      open DisplayedIso diso
      open D′.HomReasoning′
