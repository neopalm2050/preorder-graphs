import UniqueList

inductive equivalence_of {n : Nat} (unionList : List (Fin n × Fin n)) : Fin n → Fin n → Prop where
| refl : (k : Fin n) → equivalence_of unionList k k
| symm : {i j : Fin n} → equivalence_of unionList i j → equivalence_of unionList j i
| trans : {i j k : Fin n} → equivalence_of unionList i j → equivalence_of unionList j k → equivalence_of unionList i k
| exact : {i j : Fin n} → unionList.prop_contains ⟨i,j⟩ → equivalence_of unionList i j

structure EquivStructure {n : Nat} (unionList : List (Fin n × Fin n)) where
  (query : (i j : Fin n) → Decidable (equivalence_of unionList i j))

