import UniqueList
import UnionFind

universe u

inductive equivalence_of {n : Nat} (unionList : List (Fin n × Fin n)) : Fin n → Fin n → Prop where
| refl : {i j : Fin n} → i = j → equivalence_of unionList i j
| symm : {i j : Fin n} → equivalence_of unionList i j → equivalence_of unionList j i
| trans : {i j k : Fin n} → equivalence_of unionList i j → equivalence_of unionList j k → equivalence_of unionList i k
| exact : {i j : Fin n} → unionList.prop_contains ⟨i,j⟩ → equivalence_of unionList i j



def extend_equivalence {n : Nat} (unionList : List (Fin n × Fin n)) :
  (i j a b : Fin n) →
  equivalence_of unionList a b →
  equivalence_of (⟨i, j⟩ :: unionList) a b
| i, j, a, b, a_equiv_b => by
  induction a_equiv_b
  case refl a_eq_b =>
    exact equivalence_of.refl a_eq_b
  case symm a b _ h =>
    exact equivalence_of.symm h
  case trans a b c _ _ h1 h2 =>
    exact equivalence_of.trans h1 h2
  case exact a b ab_in_unionList =>
    exact equivalence_of.exact (Or.inr ab_in_unionList)


def biweaken_map {n : Nat} :
  List (Fin n × Fin n) → List (Fin (n+1) × Fin (n+1))
| [] => []
| ⟨⟨i, i_lt_n⟩ , ⟨j, j_lt_n⟩⟩ :: xs => ⟨⟨i, Nat.le.step i_lt_n⟩ , ⟨j, Nat.le.step j_lt_n⟩⟩ :: biweaken_map xs

theorem biweaken_map_doesn't_connect_max {n : Nat} :
  ∀ xs : List (Fin n × Fin n),
  ∀ a : Fin (n+1),
  ¬(biweaken_map xs).prop_contains ⟨a, ⟨n, Nat.lt.base n⟩⟩
  ∧
  ¬(biweaken_map xs).prop_contains ⟨⟨n, Nat.lt.base n⟩, a⟩
| [], _ => ⟨λ h => h, λ h => h⟩
| ⟨i,j⟩ :: tail, a =>
  ⟨ by
    intro mapxs_contains_an
    cases mapxs_contains_an
    case inl ij_eq_an =>
      let j_eq_n : j = n := Fin.val_eq_of_eq $ congrArg Prod.snd ij_eq_an
      let n_lt_n := j.isLt; rw [j_eq_n] at n_lt_n
      exact Nat.ne_of_lt n_lt_n (by rfl)
    case inr an_in_tail =>
      exact (biweaken_map_doesn't_connect_max tail a).left an_in_tail
  , by
    intro mapxs_contains_na
    cases mapxs_contains_na
    case inl ij_eq_na =>
      let i_eq_n : i = n := Fin.val_eq_of_eq $ congrArg Prod.fst ij_eq_na
      let n_lt_n := i.isLt; rw [i_eq_n] at n_lt_n
      exact Nat.ne_of_lt n_lt_n (by rfl)
    case inr na_in_tail =>
      exact (biweaken_map_doesn't_connect_max tail a).right na_in_tail
  ⟩

theorem equivalent_implies_nearby_exact {n : Nat} (unionList : List (Fin n × Fin n)) :
  ∀ i j,
  equivalence_of unionList i j →
  i = j ∨ (
    (∃ x, unionList.prop_contains ⟨i, x⟩ ∨ unionList.prop_contains ⟨x, i⟩)
    ∧
    (∃ y, unionList.prop_contains ⟨j, y⟩ ∨ unionList.prop_contains ⟨y, j⟩)
  )
| i, j, i_equiv_j => by
  induction i_equiv_j
  case refl i j i_eq_j =>
    exact Or.inl i_eq_j
  case symm i j j_equiv_i hind =>
    cases hind
    case inl i_eq_j =>
      exact Or.inl i_eq_j.symm
    case inr conjunction =>
      cases conjunction
      case intro exists_x exists_y =>
      exact Or.inr ⟨exists_y, exists_x⟩
  case trans i a j i_equiv_a a_equiv_j hind_ia hind_aj =>
    cases hind_ia
    case inl i_eq_a =>
      rw [i_eq_a]; exact hind_aj
    case inr exists_x =>
    apply Or.inr
    cases hind_aj
    case inl a_eq_j =>
      rw [a_eq_j] at exists_x
      exact exists_x
    case inr exists_y =>
      constructor
      case left =>
        exact exists_x.left
      case right =>
        exact exists_y.right
  case exact i j ij_in_unionList =>
    exact Or.inr ⟨⟨j, Or.inl ij_in_unionList⟩, ⟨i, Or.inr ij_in_unionList⟩⟩


def not_equivalent_to_new {n : Nat} (unionList : List (Fin n × Fin n)) :
  (a : Fin n) →
  ¬equivalence_of (biweaken_map unionList) ⟨a.val, Nat.lt.step a.isLt⟩ ⟨n, Nat.lt.base n⟩
| a, a_equiv_n => by
  cases equivalent_implies_nearby_exact (biweaken_map unionList) ⟨a.val, Nat.lt.step a.isLt⟩ ⟨n, Nat.lt.base n⟩ a_equiv_n
  case inl a_eq'_n =>
    let a_eq_n : a.val = n := Fin.val_eq_of_eq a_eq'_n
    let a_ne_n := Nat.ne_of_lt a.isLt
    contradiction
  case inr conj =>
    apply conj.right.elim; intro x n_connected_x
    cases n_connected_x
    case inl nx_in_unionList =>
      exact (biweaken_map_doesn't_connect_max unionList x).right nx_in_unionList
    case inr xn_in_unionList =>
      exact (biweaken_map_doesn't_connect_max unionList x).left xn_in_unionList


def still_equivalent_post_weaken {n : Nat} (unionList : List (Fin n × Fin n)) :
  (a b : Fin n) →
  equivalence_of unionList a b →
  equivalence_of (biweaken_map unionList) ⟨a.val, Nat.le.step a.isLt⟩ ⟨b.val, Nat.le.step b.isLt⟩
| a, b, a_equiv_b => by
  induction a_equiv_b
  case refl a b a_eq_b =>
    let aval_eq_bval := Fin.val_eq_of_eq a_eq_b
    exact equivalence_of.refl $ Fin.eq_of_val_eq $ aval_eq_bval
  case symm a b _a_equiv_b a_equiv'_b =>
    exact equivalence_of.symm a_equiv'_b
  case trans a b c _a_equiv_b _b_equiv_c a_equiv'_b b_equiv'_c =>
    exact equivalence_of.trans a_equiv'_b b_equiv'_c
  case exact a b ab_in_unionList =>
    apply equivalence_of.exact
    induction unionList
    case a.nil =>
      contradiction
    case a.cons head tail hind =>
      cases ab_in_unionList
      case inl head_eq_ab =>
        apply Or.inl
        let fst_eq_a : head.1.val = a.val := Fin.val_eq_of_eq $ congrArg Prod.fst head_eq_ab
        let snd_eq_b : head.2.val = b.val := Fin.val_eq_of_eq $ congrArg Prod.snd head_eq_ab
        let fst_eq_a' : ⟨head.1.val, Nat.le.step head.1.isLt⟩ = ⟨a.val, Nat.le.step a.isLt⟩ := Fin.eq_of_val_eq fst_eq_a
        let snd_eq_b' : ⟨head.2.val, Nat.le.step head.2.isLt⟩ = ⟨b.val, Nat.le.step b.isLt⟩ := Fin.eq_of_val_eq snd_eq_b
        rw [fst_eq_a', snd_eq_b']
      case inr ab_in_tail =>
        exact Or.inr $ hind ab_in_tail

def still_equivalent_pre_weaken {n : Nat} (unionList : List (Fin n × Fin n)) :
  (a b : Fin (n+1)) →
  (a_not_last : a.val ≠ n) →
  (b_not_last : b.val ≠ n) →
  equivalence_of (biweaken_map unionList) a b →
  let a_s : Fin n := ⟨a.val, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ a.isLt) a_not_last⟩
  let b_s : Fin n := ⟨b.val, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ b.isLt) b_not_last⟩
  equivalence_of unionList a_s b_s
  
| a, b, a_not_last, b_not_last, a_equiv_b => by
  induction a_equiv_b
  case refl a b a_eq_b =>
    let aval_eq_bval := Fin.val_eq_of_eq a_eq_b
    exact equivalence_of.refl $ Fin.eq_of_val_eq $ aval_eq_bval
  case symm b a _b_equiv'_a hind_ab =>
    let b_equiv_a := hind_ab b_not_last a_not_last
    exact equivalence_of.symm b_equiv_a
  case trans a x b a_equiv'_x _x_equiv'_b hind_ax hind_xb =>
    let a_s : Fin n := ⟨a.val, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ a.isLt) a_not_last⟩
    let x_not_last : x.val ≠ n := by
      intro x_eq_n
      apply not_equivalent_to_new unionList a_s
      let new : Fin (n+1) := ⟨n, Nat.lt.base n⟩
      show equivalence_of (biweaken_map unionList) a new
      let x_eq_new : x = new := Fin.eq_of_val_eq x_eq_n
      rw [x_eq_new.symm]
      exact a_equiv'_x
    let a_equiv_x := hind_ax a_not_last x_not_last
    let x_equiv_b := hind_xb x_not_last b_not_last
    exact equivalence_of.trans a_equiv_x x_equiv_b
  case exact a b ab_in_unionList' =>
    apply equivalence_of.exact
    induction unionList
    case a.nil =>
      contradiction
    case a.cons head tail hind =>
      cases ab_in_unionList'
      case inl head_eq_ab =>
        apply Or.inl
        let fst_eq_a : head.1.val = a.val := Fin.val_eq_of_eq $ congrArg Prod.fst head_eq_ab
        let snd_eq_b : head.2.val = b.val := Fin.val_eq_of_eq $ congrArg Prod.snd head_eq_ab
        let a_s : Fin n := ⟨a.val, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ a.isLt) a_not_last⟩
        let b_s : Fin n := ⟨b.val, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ b.isLt) b_not_last⟩
        show (⟨head.1, head.2⟩ : Fin n × Fin n) = ⟨a_s, b_s⟩
        let fst_eq_a_s : head.1  = a_s := Fin.eq_of_val_eq fst_eq_a
        let snd_eq_b_s : head.2 = b_s := Fin.eq_of_val_eq snd_eq_b
        rw [fst_eq_a_s, snd_eq_b_s]
      case inr ab_in_tail =>
        exact Or.inr $ hind ab_in_tail



--reads "a model [model] with query function [query] is a [unionList]-[EquivStructure] precisely when..."
def EquivStructure :
  {n : Nat} →
  {ModelType : Type u} →
  (model : ModelType) →
  (query : ModelType → Fin n → Fin n → Bool) →
  (unionList : List (Fin n × Fin n)) →
  Prop
| n, _, model, query, unionList => ∀ (i j : Fin n), (query model i j) = true ↔ equivalence_of unionList i j



namespace UnionFindLinks

  def query_and_modify {size : Nat} (uf : UnionFindLinks size) :
    Fin size → Fin size → Bool × UnionFindLinks size
  | i, j => do {
      let i_root <- find i;
      let j_root <- find j;
      return i_root == j_root
    }.run uf
  
  def query {size : Nat} (uf : UnionFindLinks size) :
    Fin size → Fin size → Bool
  | i, j => (uf.query_and_modify i j).fst

  --after calling query, do not use the old unionFind
  --use the one from calling this on it
  def post_query_reclaim {size : Nat} (uf : UnionFindLinks size) :
    Fin size → Fin size → UnionFindLinks size
  | i, j => (uf.query_and_modify i j).snd

  theorem query_true_iff_same_root {size : Nat} (uf : UnionFindLinks size) :
    ∀ (i j : Fin size), uf.query i j = true ↔ ∃ r, uf.is_root r ∧ uf.is_ancestor i r ∧ uf.is_ancestor j r
  | i, j => by
    
    let post_i_find_uf := (uf.find_aux i).fst
    let final_uf := (post_i_find_uf.find_aux j).fst
    let uf_eq_post_i_find_uf : uf.equivalent_to post_i_find_uf := (uf.find_aux i).snd.property.right
    let post_i_find_uf_eq_final_uf : post_i_find_uf.equivalent_to final_uf := (post_i_find_uf.find_aux j).snd.property.right
    let i_root := (uf.find_aux i).snd.val.val
    let j_root := (post_i_find_uf.find_aux j).snd.val.val
    let i_root_is_root : uf.is_root i_root := ((equivalent_symmetric uf_eq_post_i_find_uf) (uf.find_aux i).snd.val.property).left
    let j_root_is_intermediate_root : post_i_find_uf.is_root j_root := ((equivalent_symmetric post_i_find_uf_eq_final_uf) (post_i_find_uf.find_aux j).snd.val.property).left
    let j_root_is_root : uf.is_root j_root := ((equivalent_symmetric uf_eq_post_i_find_uf) j_root_is_intermediate_root).left
    let i_root_anc_i : uf.is_ancestor i i_root := (uf.find_aux i).snd.property.left
    let j_root_anc_j : uf.is_ancestor j j_root := ((equivalent_symmetric uf_eq_post_i_find_uf) j_root_is_intermediate_root).right j (post_i_find_uf.find_aux j).snd.property.left

    constructor
    case mp =>
      intro query_true
      let query_true : (i_root == j_root) = true := query_true
      let query_true : decide (i_root = j_root) = true := query_true
      let roots_equal : i_root = j_root := of_decide_eq_true query_true
      let i_root_anc_j : uf.is_ancestor j i_root := by rw [roots_equal]; assumption
      exact ⟨i_root, i_root_is_root, i_root_anc_i, i_root_anc_j⟩
    case mpr =>
      intro ⟨r, r_is_root, r_anc_i, r_anc_j⟩
      apply decide_eq_true
      show i_root = j_root
      let i_root_eq_r : i_root = r := uf.root_ancestors_equal i i_root r i_root_is_root r_is_root i_root_anc_i r_anc_i
      let j_root_eq_r : j_root = r := uf.root_ancestors_equal j j_root r j_root_is_root r_is_root j_root_anc_j r_anc_j
      rw [i_root_eq_r, j_root_eq_r]

  theorem equivalent_implies_same_equivstruct {size : Nat} (uf uf' : UnionFindLinks size) :
    uf.equivalent_to uf' →
    {unionList : List (Fin size × Fin size)} →
    EquivStructure uf query unionList →
    EquivStructure uf' query unionList
  | equivalent, unionList, is_equivstruct, i, j => by
      
    let post_i_find_uf' := (uf'.find_aux i).fst
    let final_uf' := (post_i_find_uf'.find_aux j).fst
    let uf'_eq_post_i_find_uf' : uf'.equivalent_to post_i_find_uf' := (uf'.find_aux i).snd.property.right
    let post_i_find_uf'_eq_final_uf' : post_i_find_uf'.equivalent_to final_uf' := (post_i_find_uf'.find_aux j).snd.property.right
    let i_root'_val := (uf'.find_aux i).snd.val.val
    let j_root'_val := (post_i_find_uf'.find_aux j).snd.val.val
    let i_root'_is_root' : uf'.is_root i_root'_val := ((equivalent_symmetric uf'_eq_post_i_find_uf') (uf'.find_aux i).snd.val.property).left
    let j_root'_is_intermediate_root' : post_i_find_uf'.is_root j_root'_val := ((equivalent_symmetric post_i_find_uf'_eq_final_uf') (post_i_find_uf'.find_aux j).snd.val.property).left
    let j_root'_is_root' : uf'.is_root j_root'_val := ((equivalent_symmetric uf'_eq_post_i_find_uf') j_root'_is_intermediate_root').left
    let i_root'_is_root : uf.is_root i_root'_val := ((equivalent_symmetric equivalent) i_root'_is_root').left
    let j_root'_is_root : uf.is_root j_root'_val := ((equivalent_symmetric equivalent) j_root'_is_root').left
    
    
    let post_i_find_uf := (uf.find_aux i).fst
    let final_uf := (post_i_find_uf.find_aux j).fst
    let uf_eq_post_i_find_uf : uf.equivalent_to post_i_find_uf := (uf.find_aux i).snd.property.right
    let post_i_find_uf_eq_final_uf : post_i_find_uf.equivalent_to final_uf := (post_i_find_uf.find_aux j).snd.property.right
    let i_root_val := (uf.find_aux i).snd.val.val
    let j_root_val := (post_i_find_uf.find_aux j).snd.val.val
    let i_root_is_root : uf.is_root i_root_val := ((equivalent_symmetric uf_eq_post_i_find_uf) (uf.find_aux i).snd.val.property).left
    let j_root_is_intermediate_root : post_i_find_uf.is_root j_root_val := ((equivalent_symmetric post_i_find_uf_eq_final_uf) (post_i_find_uf.find_aux j).snd.val.property).left
    let j_root_is_root : uf.is_root j_root_val := ((equivalent_symmetric uf_eq_post_i_find_uf) j_root_is_intermediate_root).left

    let i_root'_anc_i : uf.is_ancestor i i_root'_val := ((equivalent_symmetric equivalent) i_root'_is_root').right i (uf'.find_aux i).snd.property.left
    let j_root'_anc_j : uf.is_ancestor j j_root'_val := ((equivalent_symmetric (equivalent_transitive equivalent uf'_eq_post_i_find_uf')) j_root'_is_intermediate_root').right j (post_i_find_uf'.find_aux j).snd.property.left
    let i_root_anc_i : uf.is_ancestor i i_root_val := (uf.find_aux i).snd.property.left
    let j_root_anc_j : uf.is_ancestor j j_root_val := ((equivalent_symmetric uf_eq_post_i_find_uf) j_root_is_intermediate_root).right j (post_i_find_uf.find_aux j).snd.property.left

    let i_root_eq_i_root' : i_root_val = i_root'_val := uf.root_ancestors_equal i i_root_val i_root'_val i_root_is_root i_root'_is_root i_root_anc_i i_root'_anc_i
    let j_root_eq_j_root' : j_root_val = j_root'_val := uf.root_ancestors_equal j j_root_val j_root'_val j_root_is_root j_root'_is_root j_root_anc_j j_root'_anc_j
    
    show (i_root'_val == j_root'_val) = true ↔ equivalence_of unionList i j
    rw [i_root_eq_i_root'.symm, j_root_eq_j_root'.symm]

    constructor
    case mp =>
      intro query_true
      apply (is_equivstruct i j).mp
      show (i_root_val == j_root_val) = true
      exact query_true

    case mpr =>
      intro i_j_equivalent
      apply (is_equivstruct i j).mpr
      exact i_j_equivalent

  theorem query_doesn't_modify {size : Nat} (uf : UnionFindLinks size) :
    {unionList : List (Fin size × Fin size)} →
    (i j : Fin size) →
    EquivStructure uf query unionList ↔
    EquivStructure (uf.post_query_reclaim i j) query unionList
  | unionList, i, j => by
    let post_find_i_uf := (uf.find_aux i).fst
    let final_uf := (post_find_i_uf.find_aux j).fst
    let uf_equiv_final : uf.equivalent_to final_uf := equivalent_transitive (uf.find_aux i).snd.property.right (post_find_i_uf.find_aux j).snd.property.right
    constructor
    case mp =>
      intro is_eqst
      exact equivalent_implies_same_equivstruct uf final_uf uf_equiv_final is_eqst
    case mpr =>
      intro final_is_eqst
      exact equivalent_implies_same_equivstruct final_uf uf (equivalent_symmetric uf_equiv_final) final_is_eqst

  def unite_aux {size : Nat} (uf : UnionFindLinks size) :
    (i j : Fin size) →
    {uf_out : UnionFindLinks size //
      (
        ∀ i_root j_root,
        uf.is_root i_root →
        uf.is_root j_root →
        uf.is_ancestor i i_root →
        uf.is_ancestor j j_root →
        ∀ k,
        uf.is_ancestor k i_root →
        uf_out.is_ancestor k j_root
      ) ∧ (
        ∀ r,
        uf.is_root r →
        ¬uf.is_ancestor i r →
        uf_out.is_root r
      ) ∧ (
        ∀ j_root,
        uf.is_root j_root →
        uf.is_ancestor j j_root →
        uf_out.is_root j_root
      ) ∧ (
        ∀ k r,
        uf.is_root r →
        uf.is_ancestor k r →
        uf_out.is_ancestor k r
      ) ∧ (
        ∀ r,
        uf_out.is_root r →
        uf.is_root r
      ) ∧ (
        ∀ r k,
        uf_out.is_root r →
        uf_out.is_ancestor k r →
        (uf.is_ancestor k r) ∨ (uf.query i k = true)
      ) }
  | i, j =>
    let ⟨uf', ⟨i_root, i_root_is_root'⟩, i_root_anc_i, uf_eq_uf'⟩ := uf.find_aux i
    let ⟨uf'', ⟨j_root, j_root_is_root''⟩, j_root_anc'_j, uf'_eq_uf''⟩ := uf'.find_aux j
    let i_root_is_root := (equivalent_symmetric uf_eq_uf' i_root_is_root').left
    let j_root_is_root' := (equivalent_symmetric uf'_eq_uf'' j_root_is_root'').left
    
    let i_root_is_root'' := (equivalent_transitive uf_eq_uf' uf'_eq_uf'' i_root_is_root).left
    let i_root_anc''_i := (equivalent_transitive uf_eq_uf' uf'_eq_uf'' i_root_is_root).right i i_root_anc_i
    --I guess I never use this
    --let j_root_anc''_j := (uf'_eq_uf'' j_root_is_root').right j j_root_anc'_j

    let uf_eq_uf'' : uf.equivalent_to uf'' := equivalent_transitive uf_eq_uf' uf'_eq_uf''

    let j_root_is_root := (equivalent_symmetric uf_eq_uf' j_root_is_root').left
    let j_root_anc_j := (equivalent_symmetric uf_eq_uf' j_root_is_root').right j j_root_anc'_j

    let uf_out := uf''.set_to_root i_root ⟨j_root, j_root_is_root''⟩

    ⟨uf_out, ( by
      constructor
      case left =>
        intro i_root2 j_root2 i_root2_is_root j_root2_is_root i_root2_anc_i j_root2_anc_j
        let i_root2_eq_i_root : i_root2 = i_root := uf.root_ancestors_equal i i_root2 i_root i_root2_is_root i_root_is_root i_root2_anc_i i_root_anc_i
        let j_root2_eq_j_root : j_root2 = j_root := uf.root_ancestors_equal j j_root2 j_root j_root2_is_root j_root_is_root j_root2_anc_j j_root_anc_j
        rw [i_root2_eq_i_root, j_root2_eq_j_root]
        
        intro k i_root_anc_k
        let i_root_anc''_k := (uf_eq_uf'' i_root_is_root).right k i_root_anc_k
        let i_root_ancout_k : uf_out.is_ancestor k i_root := uf''.unite_keeps_ancestors i_root ⟨j_root, j_root_is_root''⟩ i_root_is_root'' k i_root i_root_anc''_k
        let j_root_parentout_i_root : uf_out.parent i_root = j_root := uf''.unite_sets_targetted_root i_root ⟨j_root, j_root_is_root''⟩ i_root_is_root''

        apply i_root_ancout_k.elim
        intro n n_steps
        constructor
        case w =>
          exact n+1
        case h =>
          show Nat.repeat uf_out.parent n (uf_out.parent k) = j_root
          rw [Nat.repeat_assoc uf_out.parent n k]
          rw [n_steps]
          exact j_root_parentout_i_root
      
      case right =>
      constructor
      case left =>
        intro r r_is_root r_not_anc_i
        
        let r_is_root'' := (uf_eq_uf'' r_is_root).left
        let r_not_anc''_i : ¬uf''.is_ancestor i r := λ r_anc''_i => r_not_anc_i $ (equivalent_symmetric uf_eq_uf'' r_is_root'').right i r_anc''_i

        apply λ h => (uf''.unite_keeps_untargetted_roots i_root ⟨j_root, j_root_is_root''⟩ i_root_is_root'' r h).mp r_is_root''
        intro r_eq_i_root
        rw [r_eq_i_root] at r_not_anc''_i
        contradiction

      case right =>
      constructor
      case left =>
        intro j_root2 j_root2_is_root j_root2_anc_j
        let j_root2_eq_j_root : j_root2 = j_root := uf.root_ancestors_equal j j_root2 j_root j_root2_is_root j_root_is_root j_root2_anc_j j_root_anc_j
        rw [j_root2_eq_j_root]
        exact uf''.unite_keeps_set_root i_root ⟨j_root, j_root_is_root''⟩ i_root_is_root''
      
      case right =>
      constructor
      case left =>
        intro k r r_is_root r_anc_k
        let r_anc''_k := (uf_eq_uf'' r_is_root).right k r_anc_k
        exact uf''.unite_keeps_ancestors i_root ⟨j_root, j_root_is_root''⟩ i_root_is_root'' k r r_anc''_k
      
      case right =>
      constructor
      case left =>
        intro r r_is_out_root
        by_cases i_root = r
        case inl i_root_eq_r =>
          rw [i_root_eq_r.symm]
          exact i_root_is_root
        case inr i_root_ne_r =>
          let r_is_root'' : uf''.is_root r := (uf''.unite_keeps_untargetted_roots i_root ⟨j_root, j_root_is_root''⟩ i_root_is_root'' r (λ h => i_root_ne_r h.symm)).mpr r_is_out_root
          exact (equivalent_symmetric uf_eq_uf'' r_is_root'').left
      
      case right =>
        intro r k r_is_root_out r_anc_out_k
        by_cases j_root = r
        case inl j_root_eq_r =>
          rw [j_root_eq_r.symm] at r_anc_out_k
          rw [j_root_eq_r.symm]
          cases uf''.unite_ambiguous_root i_root ⟨j_root, j_root_is_root''⟩ i_root_is_root'' k r_anc_out_k
          case inl i_root_anc''_k =>
            let i_root_anc_k := (equivalent_symmetric uf_eq_uf'' i_root_is_root'').right k i_root_anc''_k
            apply Or.inr
            apply (uf.query_true_iff_same_root i k).mpr
            exact ⟨i_root, i_root_is_root, i_root_anc_i, i_root_anc_k⟩
          case inr j_root_anc''_k =>
            exact Or.inl $ (equivalent_symmetric uf_eq_uf'' j_root_is_root'').right k j_root_anc''_k
        case inr j_root_ne_r =>
          apply Or.inl
          let i_root_ne_r : i_root ≠ r := by
            intro i_root_eq_r
            let r_parent_out_eq_j_root : uf_out.parent i_root = j_root := uf''.unite_sets_targetted_root i_root ⟨j_root, j_root_is_root''⟩ i_root_is_root''
            rw [i_root_eq_r] at r_parent_out_eq_j_root
            let j_root_eq_r := r_parent_out_eq_j_root.symm.trans r_is_root_out
            contradiction
          let r_anc''_k := uf''.unite_ancestors_in_original i_root ⟨j_root, j_root_is_root''⟩ i_root_is_root'' k r (λ h => j_root_ne_r h.symm) r_anc_out_k
          let r_is_root'' := (uf''.unite_keeps_untargetted_roots i_root ⟨j_root, j_root_is_root''⟩ i_root_is_root'' r (λ h => i_root_ne_r h.symm)).mpr r_is_root_out
          exact (equivalent_symmetric uf_eq_uf'' r_is_root'').right k r_anc''_k
    )⟩
  
  def unite {size : Nat} (uf : UnionFindLinks size) :
    Fin size → Fin size → UnionFindLinks size
  | i, j => (uf.unite_aux i j).val
  
  theorem unite_equivstruct_append {size : Nat} (uf : UnionFindLinks size) :
    {unionList : List (Fin size × Fin size)} →
    (is_equivstruct : EquivStructure uf query unionList) →
    (i j : Fin size) →
    EquivStructure (uf.unite i j) query (⟨i, j⟩ :: unionList)
  | unionList, is_equivstruct, i, j, a, b => by

    let uf' := (uf.unite_aux i j).val
    let ⟨j_root_anc_i_class, non_i_roots_stay_roots, j_root_stays_root, root_ancestry_preserved, root_preimage, root_ancestry_preimage⟩ := (uf.unite_aux i j).property
    show query uf' a b = true ↔ equivalence_of ((i, j) :: unionList) a b


    constructor
    case mp =>
      intro query'_ab_true
      let same_root := (uf'.query_true_iff_same_root a b).mp query'_ab_true
      apply same_root.elim
      intro r ⟨r_is_root', r_anc'_a, r_anc'_b⟩
      by_cases uf.query i a = true
      case inl query_ia_true =>
        by_cases uf.query i b = true
        case inl query_ib_true =>
          apply ((uf.query_true_iff_same_root i a).mp query_ia_true).elim
          intro ia_root ⟨ia_root_is_root, ia_root_anc_i, ia_root_anc_a⟩
          apply ((uf.query_true_iff_same_root i b).mp query_ib_true).elim
          intro ib_root ⟨ib_root_is_root, ib_root_anc_i, ib_root_anc_b⟩
          let roots_equal := uf.root_ancestors_equal i ia_root ib_root ia_root_is_root ib_root_is_root ia_root_anc_i ib_root_anc_i
          rw [roots_equal] at ia_root_anc_a
          let query_ab_true := (uf.query_true_iff_same_root a b).mpr ⟨ib_root, ib_root_is_root, ia_root_anc_a, ib_root_anc_b⟩
          let a_equiv_b := (is_equivstruct a b).mp query_ab_true
          exact extend_equivalence unionList i j a b a_equiv_b
        case inr query_ib_false =>
          apply ((uf.query_true_iff_same_root i a).mp query_ia_true).elim
          intro ia_root ⟨ia_root_is_root, ia_root_anc_i, ia_root_anc_a⟩
          apply (uf.root_exists j).elim
          intro j_root ⟨j_root_is_root, j_root_anc_j⟩
          let j_root_anc'_a : uf'.is_ancestor a j_root := j_root_anc_i_class ia_root j_root ia_root_is_root j_root_is_root ia_root_anc_i j_root_anc_j a ia_root_anc_a
          let _j_root_anc'_j : uf'.is_ancestor j j_root := root_ancestry_preserved j j_root j_root_is_root j_root_anc_j
          let j_root_is_root' : uf'.is_root j_root := j_root_stays_root j_root j_root_is_root j_root_anc_j
          let r_eq_j_root : r = j_root := uf'.root_ancestors_equal a r j_root r_is_root' j_root_is_root' r_anc'_a j_root_anc'_a
          let j_root_anc'_b := r_anc'_b; rw [r_eq_j_root] at j_root_anc'_b
          cases root_ancestry_preimage j_root b j_root_is_root' j_root_anc'_b
          case inl j_root_anc_b =>
            let query_jb_true : uf.query j b = true := (uf.query_true_iff_same_root j b).mpr ⟨j_root, j_root_is_root, j_root_anc_j, j_root_anc_b⟩
            let i_equiv_a : equivalence_of unionList i a := (is_equivstruct i a).mp query_ia_true
            let j_equiv_b : equivalence_of unionList j b := (is_equivstruct j b).mp query_jb_true
            let a_equiv'_i : equivalence_of (⟨i,j⟩ :: unionList) a i := extend_equivalence unionList i j a i (equivalence_of.symm i_equiv_a)
            let i_equiv'_j : equivalence_of (⟨i,j⟩ :: unionList) i j := equivalence_of.exact $ Or.inl (by rfl)
            let j_equiv'_b : equivalence_of (⟨i,j⟩ :: unionList) j b := extend_equivalence unionList i j j b j_equiv_b
            exact equivalence_of.trans a_equiv'_i $ equivalence_of.trans i_equiv'_j j_equiv'_b
          case inr query_ib_true =>
            contradiction
      case inr query_ia_false =>
        by_cases uf.query i b = true
        case inl query_ib_true =>
          apply ((uf.query_true_iff_same_root i b).mp query_ib_true).elim
          intro ib_root ⟨ib_root_is_root, ib_root_anc_i, ib_root_anc_b⟩
          apply (uf.root_exists j).elim
          intro j_root ⟨j_root_is_root, j_root_anc_j⟩
          let j_root_anc'_b : uf'.is_ancestor b j_root := j_root_anc_i_class ib_root j_root ib_root_is_root j_root_is_root ib_root_anc_i j_root_anc_j b ib_root_anc_b
          let _j_root_anc'_j : uf'.is_ancestor j j_root := root_ancestry_preserved j j_root j_root_is_root j_root_anc_j
          let j_root_is_root' : uf'.is_root j_root := j_root_stays_root j_root j_root_is_root j_root_anc_j
          let r_eq_j_root : r = j_root := uf'.root_ancestors_equal b r j_root r_is_root' j_root_is_root' r_anc'_b j_root_anc'_b
          let j_root_anc'_a := r_anc'_a; rw [r_eq_j_root] at j_root_anc'_a
          cases root_ancestry_preimage j_root a j_root_is_root' j_root_anc'_a
          case inl j_root_anc_a =>
            let query_ja_true : uf.query j a = true := (uf.query_true_iff_same_root j a).mpr ⟨j_root, j_root_is_root, j_root_anc_j, j_root_anc_a⟩
            let i_equiv_b : equivalence_of unionList i b := (is_equivstruct i b).mp query_ib_true
            let j_equiv_a : equivalence_of unionList j a := (is_equivstruct j a).mp query_ja_true
            let b_equiv'_i : equivalence_of (⟨i,j⟩ :: unionList) b i := extend_equivalence unionList i j b i (equivalence_of.symm i_equiv_b)
            let i_equiv'_j : equivalence_of (⟨i,j⟩ :: unionList) i j := equivalence_of.exact $ Or.inl (by rfl)
            let j_equiv'_a : equivalence_of (⟨i,j⟩ :: unionList) j a := extend_equivalence unionList i j j a j_equiv_a
            exact equivalence_of.symm $ equivalence_of.trans b_equiv'_i $ equivalence_of.trans i_equiv'_j j_equiv'_a
          case inr query_ib_true =>
            contradiction
        case inr query_ib_false =>
          apply (uf.root_exists a).elim
          intro a_root ⟨a_root_is_root, a_root_anc_a⟩
          apply (uf.root_exists b).elim
          intro b_root ⟨b_root_is_root, b_root_anc_b⟩
          let a_root_not_anc_i : ¬uf.is_ancestor i a_root := by
            intro a_root_anc_i
            let query_ia_true : uf.query i a = true := (uf.query_true_iff_same_root i a).mpr ⟨a_root, a_root_is_root, a_root_anc_i, a_root_anc_a⟩
            contradiction
          let b_root_not_anc_i : ¬uf.is_ancestor i b_root := by
            intro b_root_anc_i
            let query_ia_true : uf.query i b = true := (uf.query_true_iff_same_root i b).mpr ⟨b_root, b_root_is_root, b_root_anc_i, b_root_anc_b⟩
            contradiction
          let r_is_root : uf.is_root r := root_preimage r r_is_root'
          let a_root_is_root' : uf'.is_root a_root := non_i_roots_stay_roots a_root a_root_is_root a_root_not_anc_i
          let b_root_is_root' : uf'.is_root b_root := non_i_roots_stay_roots b_root b_root_is_root b_root_not_anc_i
          let a_root_anc'_a : uf'.is_ancestor a a_root := root_ancestry_preserved a a_root a_root_is_root a_root_anc_a
          let b_root_anc'_b : uf'.is_ancestor b b_root := root_ancestry_preserved b b_root b_root_is_root b_root_anc_b
          let a_root_eq_r : a_root = r := uf'.root_ancestors_equal a a_root r a_root_is_root' r_is_root' a_root_anc'_a r_anc'_a
          let b_root_eq_r : b_root = r := uf'.root_ancestors_equal b b_root r b_root_is_root' r_is_root' b_root_anc'_b r_anc'_b
          let r_anc_a := a_root_anc_a; rw [a_root_eq_r] at r_anc_a
          let r_anc_b := b_root_anc_b; rw [b_root_eq_r] at r_anc_b
          let query_ab_true := (uf.query_true_iff_same_root a b).mpr ⟨r, r_is_root, r_anc_a, r_anc_b⟩
          let a_equiv_b : equivalence_of unionList a b := (is_equivstruct a b).mp query_ab_true
          exact extend_equivalence unionList i j a b a_equiv_b
    case mpr =>
      intro a_equiv_b
      induction a_equiv_b
      case refl a b a_eq_b =>
        rw [a_eq_b.symm]
        apply (uf'.query_true_iff_same_root a a).mpr
        apply (uf'.root_exists a).elim
        intro r ⟨r_is_root, r_anc_a⟩
        exact ⟨r, r_is_root, r_anc_a, r_anc_a⟩
      case symm a b _a_equiv_b query_ab_true =>
        apply (uf'.query_true_iff_same_root b a).mpr
        let ⟨r, r_is_root, r_anc_a, r_anc_b⟩ := (uf'.query_true_iff_same_root a b).mp query_ab_true
        exact ⟨r, r_is_root, r_anc_b, r_anc_a⟩
      case trans a b c _a_equiv_b _b_equiv_c query_ab_true query_bc_true =>
        apply (uf'.query_true_iff_same_root a c).mpr
        let ⟨r, r_is_root, r_anc_a, r_anc_b⟩ := (uf'.query_true_iff_same_root a b).mp query_ab_true
        let ⟨r', r'_is_root, r'_anc_b, r'_anc_c⟩ := (uf'.query_true_iff_same_root b c).mp query_bc_true
        let r'_eq_r : r' = r := uf'.root_ancestors_equal b r' r r'_is_root r_is_root r'_anc_b r_anc_b
        let r_anc_c := r'_anc_c; rw [r'_eq_r] at r_anc_c
        exact ⟨r, r_is_root, r_anc_a, r_anc_c⟩
      case exact a b ab_in_unionList' =>
        cases ab_in_unionList'
        case inl ab_eq_ij =>
          let i_eq_a : i = a := congrArg Prod.fst ab_eq_ij
          let j_eq_b : j = b := congrArg Prod.snd ab_eq_ij
          rw [i_eq_a.symm, j_eq_b.symm]
          apply (uf'.query_true_iff_same_root i j).mpr
          apply (uf.root_exists i).elim
          intro i_root ⟨i_root_is_root, i_root_anc_i⟩
          apply (uf.root_exists j).elim
          intro j_root ⟨j_root_is_root, j_root_anc_j⟩
          let j_root_is_root' : uf'.is_root j_root := j_root_stays_root j_root j_root_is_root j_root_anc_j
          let j_root_anc'_j : uf'.is_ancestor j j_root := root_ancestry_preserved j j_root j_root_is_root j_root_anc_j
          let j_root_anc'_i : uf'.is_ancestor i j_root := j_root_anc_i_class i_root j_root i_root_is_root j_root_is_root i_root_anc_i j_root_anc_j i i_root_anc_i
          exact ⟨j_root, j_root_is_root', j_root_anc'_i, j_root_anc'_j⟩
        case inr ab_in_unionList =>
          apply (uf'.query_true_iff_same_root a b).mpr
          let a_equiv_b := equivalence_of.exact ab_in_unionList
          let query_ab_true := (is_equivstruct a b).mpr a_equiv_b
          apply ((uf.query_true_iff_same_root a b).mp query_ab_true).elim
          intro r ⟨r_is_root, r_anc_a, r_anc_b⟩
          apply (uf.root_exists i).elim
          intro i_root ⟨i_root_is_root, i_root_anc_i⟩
          apply (uf.root_exists j).elim
          intro j_root ⟨j_root_is_root, j_root_anc_j⟩
          by_cases i_root = r
          case inl i_root_eq_r =>
            let r_anc_i := i_root_anc_i; rw [i_root_eq_r] at r_anc_i
            let j_root_is_root' : uf'.is_root j_root := j_root_stays_root j_root j_root_is_root j_root_anc_j
            let j_root_anc'_a : uf'.is_ancestor a j_root := j_root_anc_i_class r j_root r_is_root j_root_is_root r_anc_i j_root_anc_j a r_anc_a
            let j_root_anc'_b : uf'.is_ancestor b j_root := j_root_anc_i_class r j_root r_is_root j_root_is_root r_anc_i j_root_anc_j b r_anc_b
            exact ⟨j_root, j_root_is_root', j_root_anc'_a, j_root_anc'_b⟩
          case inr i_root_ne_r =>
            let r_not_anc_i : ¬uf.is_ancestor i r := by
              intro r_anc_i
              let i_root_eq_r : i_root = r := uf.root_ancestors_equal i i_root r i_root_is_root r_is_root i_root_anc_i r_anc_i
              contradiction
            let r_is_root' : uf'.is_root r := non_i_roots_stay_roots r r_is_root r_not_anc_i
            let r_anc'_a : uf'.is_ancestor a r := root_ancestry_preserved a r r_is_root r_anc_a
            let r_anc'_b : uf'.is_ancestor b r := root_ancestry_preserved b r r_is_root r_anc_b
            exact ⟨r, r_is_root', r_anc'_a, r_anc'_b⟩


  theorem empty_is_equivstruct :
    EquivStructure empty query []
  | i, _ => Fin.elim0 i

  theorem expand_preserves_equivstruct {size : Nat} (uf : UnionFindLinks size) :
    {unionList : List (Fin size × Fin size)} →
    EquivStructure uf query unionList →
    EquivStructure uf.expand query (biweaken_map unionList)
  | unionList, is_eqst, i, j =>
    let new : Fin (size + 1) := ⟨size, Nat.lt.base size⟩
    let new_is_root : uf.expand.is_root new := uf.expand_last_root
    if hi : i.val = size then if hj : j.val = size then by
      let hi : i = new := Fin.eq_of_val_eq hi
      let hj : j = new := Fin.eq_of_val_eq hj
      rw [hi, hj]
      constructor
      case mp =>
        intro
        exact equivalence_of.refl (by rfl)
      case mpr =>
        intro
        apply (uf.expand.query_true_iff_same_root new new).mpr
        constructor
        case w =>
          exact new
        case h =>
          let new_anc_self : uf.expand.is_ancestor new new := ⟨0, by rfl⟩
          exact ⟨new_is_root, new_anc_self, new_anc_self⟩
    else by
      let i_eq_new : i = new := Fin.eq_of_val_eq hi
      constructor
      case mp =>
        intro query_true
        apply ((uf.expand.query_true_iff_same_root i j).mp query_true).elim
        intro r ⟨r_is_root, r_anc_i, r_anc_j⟩
        let r_eq_new : r = new := uf.expand.root_ancestors_equal i r new r_is_root new_is_root r_anc_i ⟨0, Fin.eq_of_val_eq hi⟩
        let new_anc_j := r_anc_j
        rw [r_eq_new] at new_anc_j
        let impossible := uf.expand_last_nanc_old j hj new_anc_j
        contradiction
      case mpr =>
        intro i_equiv_j
        let j_equiv_new : equivalence_of (biweaken_map unionList) j new := by
          rw [i_eq_new] at i_equiv_j
          exact i_equiv_j.symm
        let strengthened_j : Fin size := ⟨j.val, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ j.isLt) hj⟩
        let impossible := not_equivalent_to_new unionList strengthened_j j_equiv_new
        contradiction
    else if hj : j.val = size then by
      let j_eq_new : j = new := Fin.eq_of_val_eq hj
      constructor
      case mp =>
        intro query_true
        apply ((uf.expand.query_true_iff_same_root i j).mp query_true).elim
        intro r ⟨r_is_root, r_anc_i, r_anc_j⟩
        let r_eq_new : r = new := uf.expand.root_ancestors_equal j r new r_is_root new_is_root r_anc_j ⟨0, Fin.eq_of_val_eq hj⟩
        let new_anc_i := r_anc_i
        rw [r_eq_new] at new_anc_i
        let impossible := uf.expand_last_nanc_old i hi new_anc_i
        contradiction
      case mpr =>
        intro i_equiv_j
        let i_equiv_new : equivalence_of (biweaken_map unionList) i new := by
          rw [j_eq_new] at i_equiv_j
          exact i_equiv_j
        let strengthened_i : Fin size := ⟨i.val, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ i.isLt) hi⟩
        let impossible := not_equivalent_to_new unionList strengthened_i i_equiv_new
        contradiction
    else by
      let i_s : Fin size := ⟨i.val, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ i.isLt) hi⟩
      let j_s : Fin size := ⟨j.val, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ j.isLt) hj⟩
      constructor
      case mp =>
        intro query'_true
        apply ((uf.expand.query_true_iff_same_root i j).mp query'_true).elim
        intro r ⟨r_is_root', r_anc'_i, r_anc'_j⟩
        let r_ne_size : r.val ≠ size := by
          intro r_eq_size
          let r_eq_new : r = new := Fin.eq_of_val_eq r_eq_size
          rw [r_eq_new] at r_anc'_i
          exact uf.expand_last_nanc_old i hi r_anc'_i
        let r_s : Fin size := ⟨r.val, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ r.isLt) r_ne_size⟩
        apply still_equivalent_post_weaken unionList i_s j_s
        apply (is_eqst i_s j_s).mp
        apply (uf.query_true_iff_same_root i_s j_s).mpr
        constructor
        case w =>
          exact r_s
        case h =>
        constructor
        case left =>
          let h : (uf.expand.parent r).val = (uf.parent r_s).val := Fin.val_eq_of_eq $ uf.expand_preserves_parent r_s
          let h' : (uf.expand.parent r).val = r_s.val := Fin.val_eq_of_eq r_is_root'
          rw [h] at h'
          exact Fin.eq_of_val_eq h'
        case right =>
        constructor
        case left =>
          exact (uf.expand_preserves_ancestry i_s r_s).mpr r_anc'_i
        case right =>
          exact (uf.expand_preserves_ancestry j_s r_s).mpr r_anc'_j
      case mpr =>
        intro i_equiv'_j
        apply (uf.expand.query_true_iff_same_root i j).mpr
        let i_s_equiv_j_s : equivalence_of unionList i_s j_s := still_equivalent_pre_weaken unionList i j hi hj i_equiv'_j
        let query_true := (is_eqst i_s j_s).mpr i_s_equiv_j_s
        apply ((uf.query_true_iff_same_root i_s j_s).mp query_true).elim
        intro r ⟨r_is_root, r_anc_is, r_anc_js⟩
        let r_w : Fin (size+1) := ⟨r.val, Nat.lt.step r.isLt⟩
        constructor
        case w =>
          exact r_w
        case h =>
        constructor
        case left =>
          let h : (uf.expand.parent r_w).val = (uf.parent r).val := Fin.val_eq_of_eq $ uf.expand_preserves_parent r
          rw [r_is_root] at h
          exact Fin.eq_of_val_eq h
        case right =>
        constructor
        case left =>
          exact (uf.expand_preserves_ancestry i_s r).mp r_anc_is
        case right =>
          exact (uf.expand_preserves_ancestry j_s r).mp r_anc_js

end UnionFindLinks