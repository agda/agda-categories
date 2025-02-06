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
  ; p₁∘universal≈h₁ = identityˡ
  ; p₂∘universal≈h₂ = λ {X} {h₁} {h₂} {eq} → identityˡ ○ mono h₁ h₂ eq
  ; unique-diagram = λ id∘h≈id∘i _ → introˡ refl ○ id∘h≈id∘i ○ elimˡ refl
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
      ; p₁∘universal≈h₁ = project₁
      ; p₂∘universal≈h₂ = project₂
      ; unique-diagram  = unique′
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
      ; p₁∘universal≈h₁ = p₁∘universal≈h₁
      ; p₂∘universal≈h₂ = p₂∘universal≈h₂
      ; unique-diagram  = unique-diagram
      }
    }

-- Some facts about pulling back along identity
module _ (p : Pullback id f) where
  open Pullback p

  -- This is a more subtle way of saying that 'p₂ ≈ id', without involving heterogenous equality.
  pullback-identity : universal id-comm-sym ∘ p₂ ≈ id
  pullback-identity = begin
    universal id-comm-sym ∘ p₂ ≈⟨ unique ( pullˡ p₁∘universal≈h₁ ) (pullˡ p₂∘universal≈h₂)  ⟩
    universal eq               ≈⟨ universal-resp-≈ (⟺ commute ○ identityˡ) identityˡ ⟩
    universal commute          ≈˘⟨ Pullback.id-unique p ⟩
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


-- pasting law for pullbacks:
-- in a commutative diagram of the form
-- A -> B -> C
-- |    |    |
-- D -> E -> F
-- if the right square (BCEF) is a pullback,
-- then the left square (ABDE) is a pullback
-- iff the big square (ACDF) is a pullback.
module PullbackPastingLaw {A B C D E F : Obj}
  {f : A ⇒ B} {g : B ⇒ C} {h : A ⇒ D} {i : B ⇒ E} {j : C ⇒ F} {k : D ⇒ E} {l : E ⇒ F}
  (ABDE : i ∘ f ≈ k ∘ h) (BCEF : j ∘ g ≈ l ∘ i) (pbᵣ : IsPullback g i j l) where
  
  open IsPullback using (p₁∘universal≈h₁; p₂∘universal≈h₂; universal; unique-diagram)

  leftPullback⇒bigPullback : IsPullback f h i k → IsPullback (g ∘ f) h j (l ∘ k)
  leftPullback⇒bigPullback pbₗ = record
    { commute = ACDF
    ; universal = universalb
    ; p₁∘universal≈h₁ = [g∘f]∘universalb≈h₁
    ; p₂∘universal≈h₂ = p₂∘universal≈h₂ pbₗ
    ; unique-diagram = unique-diagramb
    } where
      ACDF : j ∘ (g ∘ f) ≈ (l ∘ k) ∘ h
      ACDF = begin
        j ∘ g ∘ f   ≈⟨ extendʳ BCEF ⟩
        l ∘ i ∘ f   ≈⟨ pushʳ ABDE ⟩ 
        (l ∘ k) ∘ h ∎

      -- first apply universal property of (BCEF) to get a morphism H -> B,
      -- then apply universal property of (ABDE) to get a morphism H -> A.
      universalb : {H : Obj} {h₁ : H ⇒ C} {h₂ : H ⇒ D} → j ∘ h₁ ≈ (l ∘ k) ∘ h₂ → H ⇒ A
      universalb {_} {h₁} {h₂} eq = universal pbₗ (p₂∘universal≈h₂ pbᵣ {eq = j∘h₁≈l∘k∘h₂}) where
        j∘h₁≈l∘k∘h₂ : j ∘ h₁ ≈ l ∘ k ∘ h₂
        j∘h₁≈l∘k∘h₂ = begin
          j ∘ h₁       ≈⟨ eq ⟩
          (l ∘ k) ∘ h₂ ≈⟨ assoc ⟩
          l ∘ k ∘ h₂   ∎
                
      [g∘f]∘universalb≈h₁ : {H : Obj} {h₁ : H ⇒ C} {h₂ : H ⇒ D} {eq : j ∘ h₁ ≈ (l ∘ k) ∘ h₂} → (g ∘ f) ∘ universalb eq ≈ h₁
      [g∘f]∘universalb≈h₁ {h₁ = h₁} = begin
        (g ∘ f) ∘ universalb _ ≈⟨ pullʳ (p₁∘universal≈h₁ pbₗ) ⟩
        g ∘ universal pbᵣ _    ≈⟨ p₁∘universal≈h₁ pbᵣ ⟩
        h₁                     ∎
                
      unique-diagramb : {H : Obj} {s t : H ⇒ A} → (g ∘ f) ∘ s ≈ (g ∘ f) ∘ t → h ∘ s ≈ h ∘ t → s ≈ t
      unique-diagramb {_} {s} {t} eq eq' = unique-diagram pbₗ (unique-diagram pbᵣ g∘f∘s≈g∘f∘t i∘f∘s≈i∘f∘t) eq' where
        g∘f∘s≈g∘f∘t : g ∘ f ∘ s ≈ g ∘ f ∘ t
        g∘f∘s≈g∘f∘t = begin
          g ∘ f ∘ s   ≈⟨ sym-assoc ⟩
          (g ∘ f) ∘ s ≈⟨ eq ⟩
          (g ∘ f) ∘ t ≈⟨ assoc ⟩
          g ∘ f ∘ t   ∎
        i∘f∘s≈i∘f∘t : i ∘ f ∘ s ≈ i ∘ f ∘ t
        i∘f∘s≈i∘f∘t = begin
          i ∘ f ∘ s   ≈⟨ pullˡ ABDE ⟩ 
          (k ∘ h) ∘ s ≈⟨ pullʳ eq' ⟩
          k ∘ h ∘ t   ≈⟨ extendʳ (sym ABDE) ⟩
          i ∘ f ∘ t   ∎

  bigPullback⇒leftPullback : IsPullback (g ∘ f) h j (l ∘ k) → IsPullback f h i k
  bigPullback⇒leftPullback pbb = record
    { commute = ABDE
    ; universal = universalₗ
    ; p₁∘universal≈h₁ = f∘universalₗ≈h₁
    ; p₂∘universal≈h₂ = p₂∘universal≈h₂ pbb
    ; unique-diagram = unique-diagramb
    } where   
      universalₗ : {H : Obj} {h₁ : H ⇒ B} {h₂ : H ⇒ D} → i ∘ h₁ ≈ k ∘ h₂ → H ⇒ A
      universalₗ {_} {h₁} {h₂} eq = universal pbb j∘g∘h₁≈[l∘k]∘h₂ where
        j∘g∘h₁≈[l∘k]∘h₂ : j ∘ g ∘ h₁ ≈ (l ∘ k) ∘ h₂
        j∘g∘h₁≈[l∘k]∘h₂ = begin
          j ∘ g ∘ h₁   ≈⟨ pullˡ BCEF ⟩
          (l ∘ i) ∘ h₁ ≈⟨ extendˡ eq ⟩
          (l ∘ k) ∘ h₂ ∎

      f∘universalₗ≈h₁ : {H : Obj} {h₁ : H ⇒ B} {h₂ : H ⇒ D} {eq : i ∘ h₁ ≈ k ∘ h₂} → f ∘ universalₗ eq ≈ h₁
      f∘universalₗ≈h₁ {_} {h₁} {h₂} {eq} = unique-diagram pbᵣ g∘f∘universalₗ≈g∘h₁ i∘f∘universalₗ≈i∘h₁ where
        g∘f∘universalₗ≈g∘h₁ : g ∘ f ∘ universalₗ _ ≈ g ∘ h₁
        g∘f∘universalₗ≈g∘h₁ = begin
          g ∘ f ∘ universalₗ _   ≈⟨ sym-assoc ⟩
          (g ∘ f) ∘ universalₗ _ ≈⟨ p₁∘universal≈h₁ pbb ⟩
          g ∘ h₁                 ∎               
        i∘f∘universalₗ≈i∘h₁ : i ∘ f ∘ universalₗ _ ≈ i ∘ h₁
        i∘f∘universalₗ≈i∘h₁ = begin
          i ∘ f ∘ universalₗ _   ≈⟨ pullˡ ABDE ⟩
          (k ∘ h) ∘ universalₗ _ ≈⟨ pullʳ (p₂∘universal≈h₂ pbb) ⟩
          k ∘ h₂                 ≈⟨ sym eq ⟩
          i ∘ h₁                 ∎
              
      unique-diagramb : {H : Obj} {s t : H ⇒ A} → f ∘ s ≈ f ∘ t → h ∘ s ≈ h ∘ t → s ≈ t
      unique-diagramb eq eq' = unique-diagram pbb (extendˡ eq) eq'
