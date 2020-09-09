open import Algebra.Bundles using (Group)

module Categories.Category.Construction.GroupAsCategory o {c ℓ} (G : Group c ℓ) where

open import Level

open import Categories.Category.Groupoid

open Group G

-- A group is a groupoid with a single object
open import Categories.Category.Construction.MonoidAsCategory o monoid
  renaming (MonoidAsCategory to GroupAsCategory) public

GroupIsGroupoid : IsGroupoid GroupAsCategory
GroupIsGroupoid = record
  { iso = record
    { isoˡ = inverseˡ _
    ; isoʳ = inverseʳ _
    }
  }

GroupAsGroupoid : Groupoid o c ℓ
GroupAsGroupoid = record { isGroupoid = GroupIsGroupoid }
