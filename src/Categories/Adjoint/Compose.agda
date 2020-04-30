{-# OPTIONS --without-K --safe #-}
module Categories.Adjoint.Compose where

-- Composition of Adjoints

open import Level

open import Data.Product using (_,_; _×_)
open import Function using (_$_) renaming (_∘_ to _∙_)
open import Function.Equality using (Π; _⟶_)
import Function.Inverse as FI
open import Relation.Binary using (Rel; IsEquivalence; Setoid)

-- be explicit in imports to 'see' where the information comes from
open import Categories.Adjoint using (Adjoint; _⊣_)
open import Categories.Category.Core using (Category)
open import Categories.Category.Product using (Product; _⁂_)
open import Categories.Category.Instance.Setoids
open import Categories.Morphism
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Functor.Hom using (Hom[_][-,-])
open import Categories.Functor.Construction.LiftSetoids
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper; _∘ₕ_; _∘ᵥ_; _∘ˡ_; _∘ʳ_)
  renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (NaturalIsomorphism; unitorˡ; unitorʳ; associator; _≃_)
import Categories.Morphism.Reasoning as MR

private
  variable
    o o′ o″ ℓ ℓ′ ℓ″ e e′ e″ : Level
    C D E : Category o ℓ e

-- Adjoints compose; we can't be sloppy, so associators and unitors must be inserted.
-- Use single letters in pairs, so L & M on the left, and R & S on the right
_∘⊣_ : {L : Functor C D} {R : Functor D C} {M : Functor D E} {S : Functor E D} →
  L ⊣ R → M ⊣ S → (M ∘F L) ⊣ (R ∘F S)
_∘⊣_ {C = C} {D = D} {E = E} {L = L} {R} {M} {S} LR MS = record
  { unit =  ((F⇐G (associator _ S R) ∘ᵥ R ∘ˡ (F⇒G (associator L M S))) ∘ᵥ
            (R ∘ˡ (MSη′ ∘ʳ L)) ∘ᵥ (R ∘ˡ (F⇐G unitorˡ))) ∘ᵥ LRη′
  ; counit = MSε′ ∘ᵥ (((F⇒G (unitorʳ {F = M}) ∘ʳ S) ∘ᵥ ((M ∘ˡ LRε′) ∘ʳ S)) ∘ᵥ
             (F⇒G (associator R L M) ∘ʳ S) ) ∘ᵥ F⇐G (associator S R (M ∘F L) )
  ; zig = λ {A} → zig′ {A}
  ; zag = λ {B} → zag′ {B}
  }
  where
    open NaturalIsomorphism using (F⇒G; F⇐G)
    module LR = Adjoint LR using (zig; zag) renaming (unit to LRη′; counit to LRε′)
    module MS = Adjoint MS using (zig; zag) renaming (unit to MSη′; counit to MSε′)
    module LRη = NaturalTransformation (Adjoint.unit LR) using () renaming (η to ηLR)
    module MSη = NaturalTransformation (Adjoint.unit MS) using (commute) renaming (η to ηMS)
    module LRε = NaturalTransformation (Adjoint.counit LR) using (commute) renaming (η to εLR)
    module MSε = NaturalTransformation (Adjoint.counit MS) using () renaming (η to εMS)
    module C = Category C using (Obj; id; _∘_; _≈_; sym-assoc; ∘-resp-≈ˡ; ∘-resp-≈;
      ∘-resp-≈ʳ; identityˡ; identityʳ; module HomReasoning)
    module D = Category D using (id; _∘_; ∘-resp-≈ˡ; sym-assoc; ∘-resp-≈ʳ; identityˡ;
      module HomReasoning; assoc)
    module E = Category E using (Obj; id; _∘_; _≈_; identityˡ; ∘-resp-≈ʳ; module HomReasoning;
      assoc; sym-assoc; identityʳ)
    module L = Functor L using (homomorphism; F-resp-≈) renaming (F₀ to L₀; F₁ to L₁)
    module M = Functor M using (F-resp-≈; identity; homomorphism) renaming (F₀ to M₀; F₁ to M₁)
    module R = Functor R using (F-resp-≈; identity; homomorphism) renaming (F₀ to R₀; F₁ to R₁)
    module S = Functor S using (F-resp-≈; homomorphism) renaming (F₀ to S₀; F₁ to S₁)
    open LR; open MS; open LRη; open LRε; open MSε; open MSη; open L; open M; open R; open S

    zig′ : {A : C.Obj} → (εMS (M₀ (L₀ A)) E.∘
       ((E.id E.∘ M₁ (εLR (S₀ (M₀ (L₀ A))))) E.∘ E.id) E.∘ E.id)
      E.∘ M₁ (L₁ (((C.id C.∘ R₁ D.id) C.∘ R₁ (ηMS (L₀ A)) C.∘ R₁ D.id) C.∘ ηLR A))
      E.≈ E.id
    -- use "inverted" format here, where rules are out-dented
    zig′ {A} = begin
        (εMS (M₀ (L₀ A)) E.∘ ((E.id E.∘ M₁ (εLR (S₀ (M₀ (L₀ A))))) E.∘ E.id) E.∘ E.id)
        E.∘ M₁ (L₁ (((C.id C.∘ R₁ D.id) C.∘ R₁ (ηMS (L₀ A)) C.∘ R₁ D.id) C.∘ ηLR A))
      ≈⟨  ( refl⟩∘⟨ (E.identityʳ ○ E.identityʳ ○ E.identityˡ)) ⟩∘⟨refl ⟩  -- get rid of those pesky E.id
        (εMS (M₀ (L₀ A)) E.∘ M₁ (εLR (S₀ (M₀ (L₀ A)))))
        E.∘ M₁ (L₁ (((C.id C.∘ R₁ D.id) C.∘ R₁ (ηMS (L₀ A)) C.∘ R₁ D.id) C.∘ ηLR A))
      ≈⟨ E.assoc ○ E.∘-resp-≈ʳ (⟺ M.homomorphism) ⟩
        εMS (M₀ (L₀ A)) E.∘
        M₁ (εLR (S₀ (M₀ (L₀ A))) D.∘ L₁ (((C.id C.∘ R₁ D.id) C.∘ R₁ (ηMS (L₀ A)) C.∘ R₁ D.id) C.∘ ηLR A))
         -- below: get rid of lots of pesky id. Nasty bit of nested equational reasoning, but nothing deep
      ≈⟨  refl⟩∘⟨ M.F-resp-≈ (D.∘-resp-≈ʳ (L.F-resp-≈
             (C.∘-resp-≈ˡ (C.∘-resp-≈ C.identityˡ (C.∘-resp-≈ʳ R.identity) C.HomReasoning.○
                let _⊚_ = C.HomReasoning._○_ in C.∘-resp-≈ R.identity C.identityʳ ⊚ C.identityˡ)))) ⟩
        εMS (M₀ (L₀ A)) E.∘ M₁ (εLR (S₀ (M₀ (L₀ A))) D.∘ L₁ ((R₁ (ηMS (L₀ A))) C.∘ ηLR A))
      ≈⟨  refl⟩∘⟨ M.F-resp-≈ (D.∘-resp-≈ʳ L.homomorphism) ⟩
        εMS (M₀ (L₀ A)) E.∘ M₁ (εLR (S₀ (M₀ (L₀ A))) D.∘ L₁ (R₁ (ηMS (L₀ A))) D.∘ L₁ (ηLR A))
      ≈⟨ refl⟩∘⟨ M.F-resp-≈ D.sym-assoc ⟩
        εMS (M₀ (L₀ A)) E.∘ M₁ ((εLR (S₀ (M₀ (L₀ A))) D.∘ L₁ (R₁ (ηMS (L₀ A)))) D.∘ L₁ (ηLR A))
      ≈⟨  refl⟩∘⟨ M.F-resp-≈ (D.∘-resp-≈ˡ (LRε.commute _)) ⟩
        εMS (M₀ (L₀ A)) E.∘ M₁ ( (_ D.∘ εLR _) D.∘ L₁ (ηLR A))
      ≈⟨  refl⟩∘⟨ M.homomorphism ⟩
        εMS (M₀ (L₀ A)) E.∘ M₁ (_ D.∘ εLR _) E.∘ M₁ (L₁ (ηLR A))
      ≈⟨  refl⟩∘⟨ ( M.homomorphism ⟩∘⟨refl ) ⟩
        εMS (M₀ (L₀ A)) E.∘ (M₁ (ηMS (L₀ A)) E.∘ M₁ (εLR _)) E.∘ M₁ (L₁ (ηLR A))
      ≈⟨ E.∘-resp-≈ʳ E.assoc ○ E.sym-assoc ⟩
        (εMS (M₀ (L₀ A)) E.∘ M₁ (ηMS (L₀ A))) E.∘ (M₁ (εLR _) E.∘ M₁ (L₁ (ηLR A)))
      ≈⟨ MS.zig ⟩∘⟨refl ⟩
        E.id E.∘ (M₁ (εLR _) E.∘ M₁ (L₁ (ηLR A)))
      ≈⟨ E.identityˡ ⟩
        M₁ (εLR _) E.∘ M₁ (L₁ (ηLR A))
      ≈˘⟨ M.homomorphism ⟩
        M₁ (εLR _ D.∘ L₁ (ηLR A))
      ≈⟨ M.F-resp-≈ LR.zig ○ M.identity ⟩
        E.id ∎
      where open E.HomReasoning

    zag′ : {B : E.Obj} → R₁ (S₁ (εMS B E.∘ ((E.id E.∘ M₁ (εLR (S₀ B))) E.∘ E.id) E.∘ E.id))
      C.∘ ((C.id C.∘ R₁ D.id) C.∘ R₁ (ηMS (L₀ (R₀ (S₀ B)))) C.∘ R₁ D.id) C.∘
      ηLR (R₀ (S₀ B)) C.≈ C.id
    zag′ {B} =
      let _⊚_ = E.HomReasoning._○_ in
      begin
         R₁ (S₁ (εMS B E.∘ ((E.id E.∘ M₁ (εLR (S₀ B))) E.∘ E.id) E.∘ E.id))
          C.∘ ((C.id C.∘ R₁ D.id) C.∘ R₁ (ηMS (L₀ (R₀ (S₀ B)))) C.∘ R₁ D.id) C.∘
          ηLR (R₀ (S₀ B)) -- get rid of all those id
      ≈⟨ R.F-resp-≈ (S.F-resp-≈ (E.∘-resp-≈ʳ (E.identityʳ ⊚ (E.identityʳ ⊚ E.identityˡ)))) ⟩∘⟨
         C.∘-resp-≈ˡ (C.∘-resp-≈ C.identityˡ (C.∘-resp-≈ʳ R.identity) ○
          C.∘-resp-≈ R.identity C.identityʳ ○ C.identityˡ) ⟩
         R₁ (S₁ (εMS B E.∘ M₁ (εLR (S₀ B)))) C.∘ R₁ (ηMS (L₀ (R₀ (S₀ B)))) C.∘ ηLR (R₀ (S₀ B))
      ≈⟨ C.sym-assoc ⟩
         (R₁ (S₁ (εMS B E.∘ M₁ (εLR (S₀ B)))) C.∘ R₁ (ηMS (L₀ (R₀ (S₀ B))))) C.∘ ηLR (R₀ (S₀ B))
      ≈˘⟨  R.homomorphism ⟩∘⟨refl ⟩
         R₁ (S₁ (εMS B E.∘ M₁ (εLR (S₀ B))) D.∘ ηMS (L₀ (R₀ (S₀ B)))) C.∘ ηLR (R₀ (S₀ B))
      ≈⟨ R.F-resp-≈ (D.∘-resp-≈ˡ S.homomorphism) ⟩∘⟨refl ⟩
        R₁ ((S₁ (εMS B) D.∘ (S₁ (M₁ (εLR (S₀ B))))) D.∘ ηMS (L₀ (R₀ (S₀ B)))) C.∘ ηLR (R₀ (S₀ B))
      ≈⟨ R.F-resp-≈ D.assoc ⟩∘⟨refl ⟩
        R₁ (S₁ (εMS B) D.∘ S₁ (M₁ (εLR (S₀ B))) D.∘ ηMS (L₀ (R₀ (S₀ B)))) C.∘ ηLR (R₀ (S₀ B))
      ≈⟨ R.F-resp-≈ (D.∘-resp-≈ʳ (D.HomReasoning.⟺ (MSη.commute (εLR (S₀ B))))) ⟩∘⟨refl ⟩
         R₁ (S₁ (εMS B) D.∘ ηMS (S₀ B) D.∘ εLR (S₀ B)) C.∘ ηLR (R₀ (S₀ B))
      ≈⟨ R.F-resp-≈ D.sym-assoc ⟩∘⟨refl ⟩
         R₁ ((S₁ (εMS B) D.∘ ηMS (S₀ B)) D.∘ εLR (S₀ B)) C.∘ ηLR (R₀ (S₀ B))
      ≈⟨ R.F-resp-≈ (D.∘-resp-≈ˡ MS.zag) ⟩∘⟨refl ⟩
         R₁ (D.id D.∘ εLR (S₀ B)) C.∘ ηLR (R₀ (S₀ B))
      ≈⟨ C.∘-resp-≈ˡ (R.F-resp-≈ D.identityˡ) ⟩
         R₁ (εLR (S₀ B)) C.∘ ηLR (R₀ (S₀ B))
      ≈⟨ LR.zag ⟩
         C.id ∎
      where open C.HomReasoning
