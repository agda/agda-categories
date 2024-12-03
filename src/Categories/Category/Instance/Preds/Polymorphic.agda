module Categories.Category.Instance.Preds.Polymorphic {o} where

{-
A Category in which Predicates are the Objects

Note that this is different from the category defined in `Categories.Category.Instance.Preds`, because in that category the objects are always predicates on the same type.
Here we are making a category in which the objects are all predicates, but not necessarily of the same type.
So this category actually generalises the `Sets` category, since one possible predicate of any type is the universal predicate, allowing all elements of the type.

This idea is drawn from Conal Elliott's paper Timely Computation.
-}

open import Level using (0ℓ; Level; suc; _⊔_)
open import Function using (id; _∘_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; <_,_>)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; cong-app; module ≡-Reasoning)

open import Categories.Category using (Category)

record PRED : Set (suc o) where
  constructor pred
  field
    {U} : Set o
    P : U → Set o

infixr 5 _⇒_ -- Enter the ⇒ with \=>

record _⇒_ (A B : PRED) : Set o where
  constructor mk⇒
  open PRED
  field
    {f} : U A → U B
    imp : ∀ {u} → P A u → P B (f u)

liftPred : (A : Set o) → PRED
liftPred A = pred {A} (λ _ → ⊤)

private
  variable
    A B C : PRED
    f g h i : A ⇒ B

infix 6 _◎_ -- Enter the ◎ with \ci.

_◎_ : B ⇒ C → A ⇒ B → A ⇒ C
(mk⇒ f) ◎ (mk⇒ g) = mk⇒ (f ∘ g)

infix 4 _⇒≈_ -- Enter ⇒≈ with \=>\~~

data _⇒≈_ (x : A ⇒ B) : A ⇒ B → Set (suc o) where
  mk⇒≈ : {y : A ⇒ B}
       → ({u : PRED.U A} → (PRED.P A u) → _⇒_.f x u ≡ _⇒_.f y u)
       → ({u : PRED.U A} → (PRED.P A u) → PRED.P B (_⇒_.f x u) ≡ PRED.P B (_⇒_.f y u))
       → x ⇒≈ y

⇒refl : Reflexive (_⇒≈_ {A} {B})
⇒refl = mk⇒≈ (λ _ → refl) (λ _ → refl)

⇒sym : Symmetric (_⇒≈_ {A} {B})
⇒sym (mk⇒≈ ff≡fg Pf≡Pg) = mk⇒≈ (λ Pu → sym (ff≡fg Pu))
                               (λ Pu → sym (Pf≡Pg Pu))

⇒trans : Transitive (_⇒≈_ {A} {B})
⇒trans (mk⇒≈ fi≡fj Pi≡Pj) (mk⇒≈ fj≡fk Pj≡Pk) =
  mk⇒≈ (λ Pu → trans (fi≡fj Pu) (fj≡fk Pu))
       (λ Pu → trans (Pi≡Pj Pu) (Pj≡Pk Pu))

⇒equiv : IsEquivalence (_⇒≈_ {A} {B})
⇒equiv = record
  { refl = ⇒refl
  ; sym = ⇒sym
  ; trans = ⇒trans
  }

module Equiv {A B : PRED} = IsEquivalence (⇒equiv {A} {B})

module ⇒≈-Reasoning where
  infix  1 begin_
  infixr 2 _⇒≈⟨⟩_ step-⇒≈
  infix  3 _∎

  begin_ : ∀ {f g : A ⇒ B} → f ⇒≈ g → f ⇒≈ g
  begin f⇒≈g = f⇒≈g

  _⇒≈⟨⟩_ : ∀ (f : A ⇒ B) {g : A ⇒ B} → f ⇒≈ g → f ⇒≈ g
  f ⇒≈⟨⟩ f⇒≈g = f⇒≈g

  step-⇒≈ : ∀ (f {g h} : A ⇒ B) → g ⇒≈ h → f ⇒≈ g → f ⇒≈ h
  step-⇒≈ f g⇒≈h f⇒≈g = ⇒trans f⇒≈g g⇒≈h

  syntax step-⇒≈ f g⇒≈h f⇒≈g = f ⇒≈⟨ f⇒≈g ⟩ g⇒≈h

  _∎ : ∀ (f : A ⇒ B) → f ⇒≈ f
  f ∎ = ⇒refl

◎-resp-⇒≈ₗ : ∀ {A B C : PRED} {f g : B ⇒ C} → f ⇒≈ g → (h : A ⇒ B) → f ◎ h ⇒≈ g ◎ h
◎-resp-⇒≈ₗ (mk⇒≈ fu≡gu fPu≡gPu) (mk⇒ Ph) =
  mk⇒≈ (fu≡gu ∘ Ph)
       (fPu≡gPu ∘ Ph)
    {- The above looks simple, but here's what I had to painstakingly work through
       before simplifying to the above, and this is only for the first argument
       to `mk⇒≈`!
◎-resp-⇒≈ₗ {_} {_} {_} {f} {g} (mk⇒≈ fu≡gu fPu≡gPu) h@(mk⇒ Ph) = mk⇒≈
  (λ {u} Pu → begin
    _⇒_.f (f ◎ h) u
  ≡⟨⟩ -- Definition of ◎
    ((_⇒_.f f) ∘ (_⇒_.f h)) u
  ≡⟨⟩ -- Definition of ∘
    (_⇒_.f f) ((_⇒_.f h) u)
  ≡⟨ fu≡gu {_⇒_.f h u} (Ph Pu) ⟩ -- Apply `f ⇒≈ g`
    (_⇒_.f g) ((_⇒_.f h) u)
  ≡⟨⟩ -- Definition of ∘
    ((_⇒_.f g) ∘ (_⇒_.f h)) u
  ≡⟨⟩ -- Definition of ◎
    _⇒_.f (g ◎ h) u
  ∎
  ) where open ≡-Reasoning -}

◎-resp-⇒≈ᵣ : ∀ {A B C : PRED} {h i : A ⇒ B} → h ⇒≈ i → (f : B ⇒ C) → f ◎ h ⇒≈ f ◎ i
◎-resp-⇒≈ᵣ {_} {_} {C} (mk⇒≈ hu≡iu _) (mk⇒ {f} _) =
  mk⇒≈ (cong f ∘ hu≡iu)
       (λ Pu → cong (PRED.P C) (cong f (hu≡iu Pu)))
  {- Again the long-hand proof looks a lot uglier, though may be easier to follow:
    (λ {u} Pu → begin
      _⇒_.f (f ◎ h) u
    ≡⟨⟩
      ((_⇒_.f f) ∘ (_⇒_.f h)) u
    ≡⟨⟩
      (_⇒_.f f) (_⇒_.f h u)
       -- hu≡iu : {u : PRED.U A} → (PRED.P A u) → _⇒_.f h u ≡ _⇒_.f i u
    ≡⟨ cong (_⇒_.f f) (hu≡iu Pu⟩
      (_⇒_.f f) (_⇒_.f i u)
    ≡⟨⟩
      _⇒_.f (f ◎ i)
    ∎)
    (λ {u} Pu → begin
      PRED.P C (_⇒_.f (f ◎ h) u)
    ≡⟨ cong (PRED.P C) (cong (_⇒_.f f) (hu≡iu Pu)) ⟩
      PRED.P C (_⇒_.f (f ◎ i) u)
    ∎)
  -}

◎-resp-⇒≈ : ∀ {A B C} {f h : B ⇒ C} {g i : A ⇒ B} → f ⇒≈ h → g ⇒≈ i → f ◎ g ⇒≈ h ◎ i
◎-resp-⇒≈ {_} {_} {_} {f} {h} {g} {i} f⇒≈h g⇒≈i =
  begin
    f ◎ g
  ⇒≈⟨ ◎-resp-⇒≈ₗ f⇒≈h g ⟩
    h ◎ g
  ⇒≈⟨ ◎-resp-⇒≈ᵣ g⇒≈i h ⟩
    h ◎ i
  ∎ where open ⇒≈-Reasoning


Preds : Category (suc o) o (suc o)
Preds = record
  { Obj = PRED
  ; _⇒_ = _⇒_
  ; _≈_ = _⇒≈_
  ; id = mk⇒ id
  ; _∘_ = _◎_
  ; assoc = ⇒refl
  ; sym-assoc = ⇒refl
  ; identityˡ = ⇒refl
  ; identityʳ = ⇒refl
  ; identity² = ⇒refl
  ; equiv = ⇒equiv
  ; ∘-resp-≈ = ◎-resp-⇒≈
 }

open import Categories.Category.BinaryProducts Preds using (BinaryProducts; module BinaryProducts)
open import Categories.Category.Cartesian Preds using (Cartesian)
open import Categories.Object.Terminal {suc o} {o} {suc o} Preds using (IsTerminal; Terminal)
open import Categories.Object.Product Preds using (Product)

Pred-⊤ : PRED
Pred-⊤ = liftPred ⊤

PredsIsTerminal : IsTerminal Pred-⊤
PredsIsTerminal = record
  { ! = mk⇒ (λ _ → tt)
  ; !-unique = λ _ → ⇒refl
  }


PredsProduct : ∀ {A B : PRED} → Product A B
PredsProduct {pred {A} P} {pred {B} Q} = record
  { A×B = pred {A × B} (λ (u , v) → P u × Q v)
  ; π₁ = mk⇒ proj₁
  ; π₂ = mk⇒ proj₂
  ; ⟨_,_⟩ = λ (mk⇒ ca) (mk⇒ cb) → mk⇒ < ca , cb >
  ; project₁ = ⇒refl
  ; project₂ = ⇒refl
  ; unique = λ where
      {_} {mk⇒ {fh} Ph} {mk⇒ {fi} Pi} {mk⇒ {fj} Pj} (mk⇒≈ fπ₁◎hu≈fiu _) (mk⇒≈ fπ₂◎hu≈fju _) → mk⇒≈
          (λ {u} Pu → begin
              < fi , fj > u
            ≡⟨⟩
              fi u , fj u
            ≡⟨ cong₂ _,_ (sym (fπ₁◎hu≈fiu Pu)) (sym (fπ₂◎hu≈fju Pu)) ⟩
              (proj₁ ∘ fh) u , (proj₂ ∘ fh) u
            ≡⟨⟩
              < proj₁ ∘ fh , proj₂ ∘ fh > u
            ≡⟨⟩
              fh u
            ∎)
          (λ {u} Pu → begin
              (P (fi u) × Q (fj u))
            ≡⟨ cong₂ (λ x y → P x × Q y) (sym (fπ₁◎hu≈fiu Pu)) (sym (fπ₂◎hu≈fju Pu)) ⟩
              (P (proj₁ (fh u)) × Q (proj₂ (fh u)))
            ∎)
  } where open ≡-Reasoning

PredsBinaryProducts : BinaryProducts
PredsBinaryProducts = record { product = PredsProduct }

PredsCartesian : Cartesian
PredsCartesian = record
  { terminal = record
      { ⊤ = Pred-⊤
      ; ⊤-is-terminal = PredsIsTerminal
      }
  ; products = PredsBinaryProducts
  }
