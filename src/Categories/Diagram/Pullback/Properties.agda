{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Diagram.Pullback.Properties {o ℓ e} (C : Category o ℓ e) where

open import Function using (_$_)

open import Categories.Category.BinaryProducts C
open import Categories.Category.Cartesian C
open import Categories.Diagram.Pullback C
open import Categories.Diagram.Equalizer C hiding (up-to-iso)
open import Categories.Object.Product C hiding (up-to-iso)
open import Categories.Object.Terminal C hiding (up-to-iso)
open import Categories.Morphism C
open import Categories.Morphism.Reasoning C
open import Categories.Category.Complete.Finitely using (FinitelyComplete)
open import Data.Product using (∃; _,_)

private
  open Category C
  variable
    X Y Z : Obj
    f g h i : X ⇒ Y
open HomReasoning
open Equiv

-- pullbacks of a monomorphism along itself give us the identity arrow.
pullback-self-mono : Mono f → IsPullback id id f f
pullback-self-mono mono = record
  { commute = refl
  ; universal = λ {X} {h₁} {h₂} eq → h₁
  ; unique = λ id∘i≈h₁ _ → ⟺ identityˡ ○ id∘i≈h₁
  ; p₁∘universal≈h₁ = identityˡ
  ; p₂∘universal≈h₂ = λ {X} {h₁} {h₂} {eq} → identityˡ ○ mono h₁ h₂ eq
  }

-- pullback from a terminal object is the same as a product
module _ (t : Terminal) where
  open Terminal t

  pullback-⊤⇒product : Pullback (! {X}) (! {Y}) → Product X Y
  pullback-⊤⇒product p = record
    { A×B      = P
    ; π₁       = p₁
    ; π₂       = p₂
    ; ⟨_,_⟩    = λ f g → universal (!-unique₂ {f = ! ∘ f} {g = ! ∘ g})
    ; project₁ = p₁∘universal≈h₁
    ; project₂ = p₂∘universal≈h₂
    ; unique   = λ eq eq′ → ⟺ (unique eq eq′)
    }
    where open Pullback p

  product⇒pullback-⊤ : Product X Y → Pullback (! {X}) (! {Y})
  product⇒pullback-⊤ p = record
    { p₁              = π₁
    ; p₂              = π₂
    ; isPullback = record
      { commute         = !-unique₂
      ; universal       = λ {_ f g} _ → ⟨ f , g ⟩
      ; unique          = λ eq eq′ → ⟺ (unique eq eq′)
      ; p₁∘universal≈h₁ = project₁
      ; p₂∘universal≈h₂ = project₂
      }
    }
    where open Product p

-- pullbacks respect _≈_
module _ (p : Pullback f g) where
  open Pullback p

  pullback-resp-≈ : f ≈ h → g ≈ i → Pullback h i
  pullback-resp-≈ eq eq′ = record
    { p₁              = p₁
    ; p₂              = p₂
    ; isPullback = record
      { commute         = ∘-resp-≈ˡ (⟺ eq) ○ commute ○ ∘-resp-≈ˡ eq′
      ; universal       = λ eq″ → universal (∘-resp-≈ˡ eq ○ eq″ ○ ∘-resp-≈ˡ (⟺ eq′))
      ; unique          = unique
      ; p₁∘universal≈h₁ = p₁∘universal≈h₁
      ; p₂∘universal≈h₂ = p₂∘universal≈h₂
      }
    }

-- Some facts about pulling back along identity
module _ (p : Pullback id f) where
  open Pullback p

  -- This is a more subtle way of saying that 'p₂ ≈ id', without involving heterogenous equality.
  pullback-identity : universal id-comm-sym ∘ p₂ ≈ id
  pullback-identity = begin
    universal Basic.id-comm-sym ∘ p₂ ≈⟨ unique ( pullˡ p₁∘universal≈h₁ ) (pullˡ p₂∘universal≈h₂)  ⟩
    universal eq                     ≈⟨ universal-resp-≈ (⟺ commute ○ identityˡ) identityˡ ⟩
    universal commute                ≈˘⟨ Pullback.id-unique p ⟩
    id ∎
    where
      eq : id ∘ f ∘ p₂ ≈ f ∘ id ∘ p₂
      eq = begin
        (id ∘ f ∘ p₂) ≈⟨ elimˡ Equiv.refl ⟩
        (f ∘ p₂)      ≈˘⟨ refl⟩∘⟨ identityˡ ⟩
        (f ∘ id ∘ p₂) ∎

-- pullbacks in Cartesian categories create equalizers
module _ (pullbacks : ∀ {X Y Z} (f : X ⇒ Z) (g : Y ⇒ Z) → Pullback f g)
         (cartesian : Cartesian) where
  open Cartesian cartesian
  open BinaryProducts products using (⟨_,_⟩; π₁; π₂; ⟨⟩-cong₂; ⟨⟩∘; project₁; project₂)

  pullback×cartesian⇒equalizer : Equalizer f g
  pullback×cartesian⇒equalizer {f = f} {g = g} = record
    { arr       = p.p₁
    ; isEqualizer = record
      { equality  = equality
      ; equalize  = λ {_ h} eq → p.universal $ begin
        ⟨ f , g ⟩ ∘ h               ≈⟨ ⟨⟩∘ ⟩
        ⟨ f ∘ h , g ∘ h ⟩           ≈˘⟨ ⟨⟩-cong₂ identityˡ (identityˡ ○ eq) ⟩
        ⟨ id ∘ f ∘ h , id ∘ f ∘ h ⟩ ≈˘⟨ ⟨⟩∘ ⟩
        ⟨ id , id ⟩ ∘ f ∘ h         ∎
      ; universal = ⟺ p.p₁∘universal≈h₁
      ; unique    = λ eq → p.unique (⟺ eq)
                                    (⟺ (pullˡ eq′) ○ ⟺ (∘-resp-≈ʳ eq))
      }
    }
    where p : Pullback ⟨ f , g ⟩ ⟨ id , id ⟩
          p = pullbacks _ _
          module p = Pullback p
          eq : ⟨ f ∘ p.p₁ , g ∘ p.p₁ ⟩ ≈ ⟨ p.p₂ , p.p₂ ⟩
          eq = begin
            ⟨ f ∘ p.p₁ , g ∘ p.p₁ ⟩      ≈˘⟨ ⟨⟩∘ ⟩
            ⟨ f , g ⟩ ∘ p.p₁             ≈⟨ p.commute ⟩
            ⟨ id , id ⟩ ∘ p.p₂           ≈⟨ ⟨⟩∘ ⟩
            ⟨ id ∘ p.p₂ , id ∘ p.p₂ ⟩    ≈⟨ ⟨⟩-cong₂ identityˡ identityˡ ⟩
            ⟨ p.p₂ , p.p₂ ⟩              ∎
          eq′ : f ∘ p.p₁ ≈  p.p₂
          eq′ = begin
            f ∘ p.p₁                     ≈˘⟨ project₁ ⟩
            π₁ ∘ ⟨ f ∘ p.p₁ , g ∘ p.p₁ ⟩ ≈⟨ refl⟩∘⟨ eq ⟩
            π₁ ∘ ⟨ p.p₂ , p.p₂ ⟩         ≈⟨ project₁ ⟩
            p.p₂                         ∎
          equality : f ∘ p.p₁ ≈ g ∘ p.p₁
          equality = begin
            f ∘ p.p₁                     ≈⟨ eq′ ⟩
            p.p₂                         ≈˘⟨ project₂ ⟩
            π₂ ∘ ⟨ p.p₂ , p.p₂ ⟩         ≈˘⟨ refl⟩∘⟨ eq ⟩
            π₂ ∘ ⟨ f ∘ p.p₁ , g ∘ p.p₁ ⟩ ≈⟨ project₂ ⟩
            g ∘ p.p₁                     ∎

-- all pullbacks and a terminal object make a category finitely complete
pullback-⊤⇒FinitelyComplete : (∀ {X Y Z} (f : X ⇒ Z) (g : Y ⇒ Z) → Pullback f g) → Terminal → FinitelyComplete C
pullback-⊤⇒FinitelyComplete pullbacks ⊤ = record
  { cartesian = cartesian
  ; equalizer = λ _ _ → pullback×cartesian⇒equalizer pullbacks cartesian
  }
    where
      open Category hiding (Obj)
      open Pullback
      open Terminal ⊤ hiding (⊤)

      _×_ : (A B : Obj) → Pullback (IsTerminal.! ⊤-is-terminal) (IsTerminal.! ⊤-is-terminal)
      A × B = pullbacks (IsTerminal.! ⊤-is-terminal) (IsTerminal.! ⊤-is-terminal)

      cartesian = record
        { terminal = ⊤
        ; products = record
            { product = λ {A B} → record
                { A×B = P {A}{_}{B} (A × B)
                ; π₁ = p₁ (A × B)
                ; π₂ = p₂ (A × B)
                ; ⟨_,_⟩ =  λ _ _ → universal (A × B) (!-unique₂)
                ; project₁ = p₁∘universal≈h₁ (A × B)
                ; project₂ = p₂∘universal≈h₂ (A × B)
                ; unique = λ eq₁ eq₂ → Equiv.sym C (unique (A × B) eq₁ eq₂)
                }
            }
        }

-- extra properties of "up-to-iso"
module IsoPb {X Y Z} {f : X ⇒ Z} {g : Y ⇒ Z} (pull₀ pull₁ : Pullback f g) where
  open Pullback using (P; p₁; p₂; p₁∘universal≈h₁; p₂∘universal≈h₂; commute; universal)

  P₀≅P₁ : P pull₀ ≅ P pull₁
  P₀≅P₁ = up-to-iso pull₀ pull₁

  P₀⇒P₁ : P pull₀ ⇒ P pull₁
  P₀⇒P₁ = _≅_.from P₀≅P₁

  p₁-≈ : p₁ pull₁ ∘ P₀⇒P₁ ≈ p₁ pull₀
  p₁-≈ = p₁∘universal≈h₁ pull₁ {eq = commute pull₀}

  p₂-≈ : p₂ pull₁ ∘ P₀⇒P₁ ≈ p₂ pull₀
  p₂-≈ = p₂∘universal≈h₂ pull₁ {eq = commute pull₀}
