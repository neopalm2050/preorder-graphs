import UniqueList

universe u v

namespace Nat
  theorem repeat_assoc {α : Type u} :
    (f : α → α) →
    (n : Nat) →
    (a : α) →
    Nat.repeat f n (f a) = f (Nat.repeat f n a)
  | f, 0, a => Eq.refl _
  | f, n+1, a => by
    let h : Nat.repeat f (n + 1) (f a) = Nat.repeat f n (f (f a)) := Eq.refl _
    let h' : Nat.repeat f (n + 1) a = Nat.repeat f n (f a) := Eq.refl _
    rw [h, h']
    rw [repeat_assoc f n (f a)]
  
  theorem repeat_add {α : Type u} :
    (f : α → α) →
    (m n : Nat) →
    (a : α) →
    Nat.repeat f m (Nat.repeat f n a) = Nat.repeat f (m + n) a
  | f, m, 0, a => by rfl
  | f, m, n+1, a => repeat_add f m n (f a)
end Nat

namespace Fin
  def weaken :
    {m n : Nat} →
    m ≤ n →
    (Fin m) →
    Fin n
  | _, _, isLe, ⟨x, isLt⟩ => ⟨x, Nat.lt_of_lt_of_le isLt isLe⟩

  theorem weaken_preserves_val :
    {m n : Nat} →
    (h : m ≤ n) →
    (x : Fin m) →
    (weaken h x).val = x.val
  | m, n, h, x => by rfl
end Fin

namespace List
  theorem concat_length_succ {α : Type u} :
    (xs : List α) →
    (elem : α) →
    (xs.concat elem).length = xs.length + 1
  | [], _ => by rfl
  | x::xs, x' => congrArg Nat.succ (concat_length_succ xs x')

  theorem concat_get_last {α : Type u} :
    (xs : List α) →
    (elem : α) →
    (xs.concat elem).get ⟨xs.length, by rw [concat_length_succ xs elem]; exact Nat.lt_succ_self _⟩ = elem
  | [], _ => by rfl
  | _::xs, x' => concat_get_last xs x'

  theorem concat_get_other {α : Type u} :
    (xs : List α) →
    (elem : α) →
    (n : Fin xs.length) →
      let n_weakened : Fin (xs.length + 1) := (Fin.weaken (Nat.le.step Nat.le.refl) n)
      let n_concat_fin : Fin ((xs.concat elem).length) := ⟨n, by rw [xs.concat_length_succ elem]; exact n_weakened.isLt⟩
    (xs.concat elem).get n_concat_fin = xs.get n
  | [], _, fin0 => Fin.elim0 fin0
  | x::xs, elem, ⟨0, _⟩ => by rfl
  | _::xs, elem, ⟨n+1, sn_lt_slxs⟩ => concat_get_other xs elem ⟨n, Nat.lt_of_succ_lt_succ sn_lt_slxs⟩

  theorem map_get {α : Type u} {β : Type v} :
    (f : α → β) →
    (xs : List α) →
    (n : Fin xs.length) →
    (List.map f xs).get ⟨n.val, by rw [xs.length_map f]; exact n.isLt⟩ = f (xs.get n)
  | _, [], fin0 => Fin.elim0 fin0
  | f, x::xs, ⟨0, isLt⟩ => by rfl
  | f, _::xs, ⟨n+1, isLt⟩ => map_get f xs ⟨n, Nat.lt_of_succ_lt_succ isLt⟩
end List

namespace Array
  theorem push_get_last {α : Type u} :
    (xs : Array α) →
    (elem : α) →
    (xs.push elem).get ⟨xs.size, by rw [xs.size_push elem]; exact Nat.lt_succ_self xs.size⟩ = elem
  | ⟨xs⟩, x' => List.concat_get_last xs x'

  theorem push_get_other {α : Type u} :
    (xs : Array α) →
    (elem : α) →
    (n : Fin xs.size) →
      let n_weakened : Fin (xs.size + 1) := (Fin.weaken (Nat.le.step Nat.le.refl) n)
      let n_push_fin : Fin ((xs.push elem).size) := ⟨n, by rw [xs.size_push elem]; exact n_weakened.isLt⟩
    (xs.push elem).get n_push_fin = xs.get n
  | ⟨xs⟩, x', n => List.concat_get_other xs x' n
end Array

#print Array.map
#print Array.mapM
#print Array.foldlM
#print Array.size
#print Array.foldlM.loop
#print Array.push
#print List.concat
#print List.map


def FinArray (size : Nat) :=
  {xs : Array (Fin size) // xs.size = size}

namespace FinArray
  def get {size : Nat} (array : FinArray size) (id : Fin size) : Fin size :=
    array.val.get (
      let in_range : id.val < Array.size array.val := by
        rw [array.property]
        exact id.isLt
      ⟨id.val, in_range⟩
    )
  
  def set {size : Nat} (array : FinArray size) (loc : Fin size) (new : Fin size) : FinArray size :=
    ⟨
      array.val.set (
        let in_range : loc.val < Array.size array.val := by
          rw [array.property]
          exact loc.isLt
        ⟨loc.val, in_range⟩
      ) new,
      (array.val.size_set _ _).trans array.property
    ⟩
  
  def expand {size : Nat} (array : FinArray size) (elem : Fin (size+1)) : FinArray (size+1) :=
    
    let h : size ≤ size + 1 := Nat.le.step Nat.le.refl
    let array_weaker : Array (Fin (size + 1)) :=
      ⟨List.map (Fin.weaken h) array.val.data⟩
    
    let array_out := array_weaker.push elem
    
    ⟨array_out, by
      rw [array_weaker.size_push elem]
      apply congrArg Nat.succ
      exact (array.val.data.length_map (Fin.weaken h)).trans array.property⟩
  
  theorem expand_get_last {size : Nat} (array : FinArray size) (elem : Fin (size+1)) :
    (array.expand elem).get ⟨size, Nat.lt_succ_self size⟩ = elem :=
    
    let h : size ≤ size + 1 := Nat.le.step Nat.le.refl
    let array_weaker : Array (Fin (size + 1)) :=
      ⟨List.map (Fin.weaken h) array.val.data⟩

    let g : size < (array_weaker.push elem).size := by
      rw [Array.size_push]
      let h'' : Array.size array_weaker = size := (List.length_map array.val.data (Fin.weaken h)).trans array.property
      rw [h'']
      exact Nat.lt_succ_self size

    let h' : (array_weaker.push elem).get ⟨size, g⟩ = elem := by
      let g' := array_weaker.push_get_last elem
      let g''' : Array.size array_weaker < Array.size (Array.push array_weaker elem) := by rw [(array_weaker.size_push elem)]; exact Nat.lt_succ_self _
      let g'' : Fin.mk (Array.size array_weaker) g''' = Fin.mk size g := Fin.eq_of_val_eq ((List.length_map array.val.data (Fin.weaken h)).trans array.property)
      rw [g''] at g'
      exact g'

    h'
  
  theorem expand_get_other {size : Nat} (array : FinArray size) (elem : Fin (size+1)) :
    (index : Fin size) →
    let weak_index := Fin.weaken (Nat.le.step Nat.le.refl) index
    ((array.expand elem).get weak_index).val = (array.get index).val
  | index =>
    let h : size ≤ size + 1 := Nat.le.step Nat.le.refl
    let array_weaker : Array (Fin (size + 1)) :=
      ⟨List.map (Fin.weaken h) array.val.data⟩
    
    
    let idx := index.val
    
    let idx_lt_size : idx < size := index.isLt
    let idx_lt_array_size : idx < array.val.size := by rw [array.property]; exact idx_lt_size
    let idx_lt_weaker_size : idx < array_weaker.size := Nat.lt_of_lt_of_eq idx_lt_array_size (array.val.data.length_map (Fin.weaken h)).symm
    let idx_lt_pushed_weaker_size : idx < (array_weaker.push elem).size := by rw [array_weaker.size_push elem]; exact Nat.le.step idx_lt_weaker_size

    let array_weaker_same_number : (array_weaker.get ⟨idx, idx_lt_weaker_size⟩) = Fin.weaken h (array.get index) :=
      List.map_get (Fin.weaken h) array.val.data ⟨idx, idx_lt_array_size⟩
    
    let j : (array_weaker.push elem).get ⟨idx, idx_lt_pushed_weaker_size⟩ = array_weaker.get ⟨idx, idx_lt_weaker_size⟩ := array_weaker.push_get_other elem ⟨idx, idx_lt_weaker_size⟩

    let k : (Fin.weaken h (array.get index)).val = (array.get index).val := Fin.weaken_preserves_val h (array.get index)

    let h' : ((array_weaker.push elem).get ⟨idx, idx_lt_pushed_weaker_size⟩).val = (array.get index).val :=
      (Fin.val_eq_of_eq (j.trans array_weaker_same_number)).trans k
    
    h'

  theorem get_set {size : Nat} :
    ∀ array : FinArray size,
    ∀ loc val : Fin size,
    (array.set loc val).get loc = val
  | ⟨⟨list⟩, len_proof⟩, ⟨loc, loc_lt_size⟩, val =>
    let list_len_proof : list.length = size := len_proof
    let list_loc : Fin (list.length) := ⟨loc, by
      rw [list_len_proof]
      exact loc_lt_size
    ⟩
    list.get_set list_loc val

  theorem get_set_ne {size : Nat} :
    ∀ array : FinArray size,
    ∀ setloc getloc val : Fin size,
    setloc ≠ getloc →
    array.get getloc = (array.set setloc val).get getloc
  | ⟨⟨list⟩, len_proof⟩, ⟨setloc, hsetloc⟩, ⟨getloc, hgetloc⟩, val, setloc_ne_getloc =>
    let list_len_proof : list.length = size := len_proof
    let list_setloc : Fin (list.length) := ⟨setloc, by
      rw [list_len_proof]
      exact hsetloc
    ⟩
    let list_getloc : Fin (list.length) := ⟨getloc, by
      rw [list_len_proof]
      exact hgetloc
    ⟩
    let list_setloc_ne_list_getloc : list_setloc ≠ list_getloc := (
      λ equal =>
      let h : setloc = getloc := Fin.val_eq_of_eq equal
      setloc_ne_getloc (Fin.eq_of_val_eq h)
    )
    list.get_set_ne list_setloc list_getloc val list_setloc_ne_list_getloc
end FinArray

def UnionFindLinks (size : Nat) :=
  {
    parent_array : FinArray size //
    ∀ id, ∃ steps,
      let is_root := λ x => parent_array.get x = x
      is_root (Nat.repeat parent_array.get steps id) ∧
      ∀ n, n < steps → ¬(is_root (Nat.repeat parent_array.get n id))
  }


namespace UnionFindLinks

  def empty : UnionFindLinks 0 :=
    ⟨⟨⟨[]⟩, by rfl⟩, λ fin0 => Fin.elim0 fin0⟩

  def parent {size : Nat} (uf : UnionFindLinks size) (id : Fin size) : Fin size :=
    uf.val.get id

  def is_ancestor {size : Nat} (uf : UnionFindLinks size) (id : Fin size) (ancestor : Fin size) : Prop :=
    ∃ n : Nat, Nat.repeat uf.parent n id = ancestor

  def is_root {size : Nat} (uf : UnionFindLinks size) (id : Fin size) : Prop :=
    uf.parent id = id
  
  def rooted_in_steps {size : Nat} (uf : UnionFindLinks size) (id : Fin size) (steps : Nat) : Prop :=
    uf.is_root (Nat.repeat uf.parent steps id)

  def rooted_in_exact_steps {size : Nat} (uf : UnionFindLinks size) (id : Fin size) (steps : Nat) : Prop :=
    uf.is_root (Nat.repeat uf.parent steps id) ∧
    ∀ n : Nat, n < steps → ¬(uf.is_root (Nat.repeat uf.parent n id))

  def roots {size : Nat} (uf : UnionFindLinks size) : Type :=
    {id : Fin size // uf.is_root id}

  def is_descendency {size : Nat} (uf : UnionFindLinks size) : Fin size → List (Fin size) → Prop
  | _x, [] => True
  | final, (x::xs) => (
    uf.parent x = final ∧ uf.is_descendency x xs
  )

  def get_ancestry {size : Nat} (uf : UnionFindLinks size) :
    (id : Fin size) →
    (n : Nat) →
    {path : Fin size × List (Fin size) // uf.is_descendency path.fst path.snd ∧ path.fst = Nat.repeat uf.parent n id ∧ path.snd.length = n}
  | id, 0 => ⟨⟨id, []⟩, trivial, by rfl, by rfl⟩
  | id, n+1 =>
    let ⟨⟨lower_top, lower_path⟩, lower_is_desc, lower_top_val, lower_size⟩ := uf.get_ancestry id n
    let new_path := lower_top :: lower_path
    let new_top := uf.parent lower_top
    let new_is_desc : uf.is_descendency new_top new_path := ⟨by rfl, lower_is_desc⟩
    let new_top_val : new_top = Nat.repeat uf.parent n (uf.parent id) := by
      simp
      rw [Nat.repeat_assoc, lower_top_val.symm]
    let new_size : new_path.length = (n+1) := congrArg Nat.succ lower_size
    ⟨⟨new_top, new_path⟩, new_is_desc, new_top_val, new_size⟩

  theorem root_ancestor_root {size : Nat} (uf : UnionFindLinks size) :
    ∀ id steps, uf.is_root id → uf.is_root (Nat.repeat uf.parent steps id) := by
    intro id steps
    induction steps
    case zero =>
      intro h; exact h
    case succ steps h_ind =>
      intro id_is_root
      let hroot := h_ind id_is_root
      let h_eq : uf.parent (Nat.repeat (uf.parent) steps id) = (Nat.repeat (uf.parent) steps id) := hroot
      let associate_parent := Nat.repeat_assoc uf.parent steps id
      rw [associate_parent.symm] at h_eq
      let h_eq : Nat.repeat (parent uf) (steps+1) id = Nat.repeat (parent uf) steps id := h_eq
      rw [h_eq]
      exact hroot

  theorem exact_rooted {size : Nat} (uf : UnionFindLinks size) :
    ∀ id, ∃ steps, uf.rooted_in_exact_steps id steps :=
      uf.property
  
  def from_exact_rooted {size : Nat} :
    (parent_array : FinArray size) →
    (∀ id, ∃ steps,
      let is_root := λ x => parent_array.get x = x
      is_root (Nat.repeat parent_array.get steps id) ∧
      ∀ n, n < steps → ¬(is_root (Nat.repeat parent_array.get n id))
    ) →
    UnionFindLinks size :=
    λ parent_array is_exact_rooted => ⟨parent_array, is_exact_rooted⟩

  theorem rooted {size : Nat} (uf : UnionFindLinks size) :
    ∀ id, ∃ steps, uf.rooted_in_steps id steps :=
      λ id => 
      (uf.exact_rooted id).elim (
        λ steps ⟨rooted_in_steps, _⟩ =>
        ⟨steps, rooted_in_steps⟩
      )
  
  theorem root_exists {size : Nat} (uf : UnionFindLinks size) :
    ∀ id, ∃ root, uf.is_root root ∧ uf.is_ancestor id root
  | id => (uf.rooted id).elim (
    λ n is_root =>
    let root := Nat.repeat uf.parent n id
    ⟨root, is_root, n, by rfl⟩
  )
    
  def from_rooted {size : Nat} :
    (parent_array : FinArray size) →
    (∀ id, ∃ steps,
      let r := Nat.repeat parent_array.get steps id
      parent_array.get r = r) →
    UnionFindLinks size
  | parent_array, rooted => ⟨parent_array,
      λ id =>
      (rooted id).elim (by
        intro steps
        induction steps
        case zero =>
          intro h_is_root
          exact ⟨0, h_is_root, 
            λ n n_lt_zero =>
            False.elim (Nat.not_lt_zero n n_lt_zero)
          ⟩
        case succ steps h_ind =>
          intro root_in_succ_steps
          exact (
            let l := Nat.repeat parent_array.get steps id
            if h_steps_root : parent_array.get l = l then
              h_ind h_steps_root
            else
              let is_root := λ x => parent_array.get x = x
              let no_roots_below_aux : ∀ (k : Nat), k < steps + 1 → ¬is_root (Nat.repeat parent_array.get (steps - k) id) := by
                intro k
                induction k
                case zero =>
                  intro _
                  exact h_steps_root
                case succ k h_ind =>
                  intro succ_k_lt_succ_steps
                  let k_lt_steps := Nat.lt_of_succ_lt_succ succ_k_lt_succ_steps
                  let steps_sub_k_ne_zero := Nat.sub_ne_zero_of_lt k_lt_steps
                  let h : steps - (k + 1) = steps - k - 1 := Nat.sub_succ steps k
                  let h' : steps - k - 1 + 1 = steps - k := Nat.succ_pred steps_sub_k_ne_zero
                  intro root_in_succ_n_steps
                  rw [h] at root_in_succ_n_steps
                  rw [h'.symm] at h_ind
                  let k_lt_succ_steps := Nat.lt_of_succ_lt succ_k_lt_succ_steps
                  let ind_h : ¬is_root ( (Nat.repeat parent_array.get (steps - k - 1) (parent_array.get id)) ) := h_ind k_lt_succ_steps
                  let h'' :
                    Nat.repeat parent_array.get (steps - k - 1) (parent_array.get id) =
                    parent_array.get (Nat.repeat parent_array.get (steps - k - 1) id) :=
                    Nat.repeat_assoc parent_array.get (steps - k - 1) id
                  rw [h''] at ind_h
                  rw [root_in_succ_n_steps] at ind_h
                  exact ind_h root_in_succ_n_steps
              
              let no_roots_below : ∀ (n : Nat), n < steps + 1 → ¬is_root (Nat.repeat parent_array.get n id) := by
                intro n n_lt_succ_steps
                let k := steps - n
                let k_le_steps : k ≤ steps := Nat.sub_le steps n
                let n_le_steps : n ≤ steps := Nat.le_of_lt_succ n_lt_succ_steps
                let k_lt_succ_steps : k < steps + 1 := Nat.lt_succ_of_le k_le_steps
                let aux_output := no_roots_below_aux k k_lt_succ_steps
                let steps_eq_n_add_k : steps = n + k := (Nat.eq_add_of_sub_eq n_le_steps (Eq.refl _)).trans (Nat.add_comm k n)
                let steps_sub_k_eq_n : steps - k = n := Nat.sub_eq_of_eq_add steps_eq_n_add_k
                rw [steps_sub_k_eq_n] at aux_output
                exact aux_output

              ⟨steps+1, root_in_succ_steps, no_roots_below⟩
          )
      )
    ⟩
  
  theorem no_cycles {size : Nat} (uf : UnionFindLinks size) :
    ∀ id steps,
      Nat.repeat uf.parent (steps+1) id = id →
      uf.is_root id :=
    λ id steps repeat_in_succ_steps =>
    if hroot : uf.parent id = id then
      hroot
    else
      let cycles_in_succ_steps : ∀ n : Nat, Nat.repeat uf.parent ((steps+1) * n) id = id := by
        intro n
        induction n
        case zero =>
          rfl
        case succ n h_ind =>
          let h : (steps+1) * (n+1) = (steps+1) * n + (steps+1) := by rfl
          rw [h]
          rw [(Nat.repeat_add uf.parent ((steps+1) * n) (steps+1) id).symm]
          rw [repeat_in_succ_steps]
          rw [h_ind]
      
      let multiple_not_root : ∀ n : Nat, ¬uf.is_root (Nat.repeat uf.parent ((steps+1) * n) id) := by
        intro n
        rw [cycles_in_succ_steps n]
        exact hroot
      
      let never_reaching_root : ∀ n : Nat, ¬uf.is_root (Nat.repeat uf.parent n id) :=
        λ n n_is_root =>
        let rem := n % (steps+1)
        let to_next := (steps+1) - rem
        let quot := n / (steps+1)
        let n_sum : (steps+1) * quot + rem = n := Nat.div_add_mod n (steps+1)
        let total_sum : n + to_next = (steps+1) * (quot+1) := by
          rw [n_sum.symm]
          rw [Nat.add_assoc, Nat.add_comm rem to_next]
          let h : to_next = steps + 1 - rem := by rfl
          rw [h]
          let rem_not_large : rem ≤ steps+1 :=
            Nat.le_of_lt (Nat.mod_lt n (Nat.zero_lt_succ steps))
          rw [Nat.sub_add_cancel rem_not_large]
          rfl
        let multiple_is_root := uf.root_ancestor_root (Nat.repeat (parent uf) n id) to_next n_is_root
        (by
          rw [Nat.repeat_add uf.parent to_next n, Nat.add_comm, total_sum] at multiple_is_root
          exact multiple_not_root (quot+1) multiple_is_root
        )
      
      (uf.rooted id).elim (
        λ n rooted_in_n =>
        False.elim (
          never_reaching_root n rooted_in_n
        )
      )

  
  
  --not used
  /-
  def from_no_cycles {size : Nat} :
    (parent_array : FinArray size) →
    (∀ id steps,
      Nat.repeat parent_array.get (steps+1) id = id →
      parent_array.get id = id) →
    UnionFindLinks size
  | parent_array, no_cycles => from_rooted parent_array (by
    intro id
    constructor
    case w => exact size
    case h =>
      --basically, make a list that gets the parent size times
      --pigeonhole principle says there's a repeat
      --that means there's a root, therefore it's all root from there onwards
      sorry
  )
  -/
  

  theorem path_containing_ancestor_end_ends_repeat {size : Nat} (uf : UnionFindLinks size) :
    ∀ id final path, uf.is_descendency final path → path.prop_contains id →
    (∃ steps, Nat.repeat uf.parent steps final = id) →
    ∃ steps, Nat.repeat uf.parent (steps+1) id = id
    | _, _, [] => by intro _ _ _; contradiction
    | id, final, (x::xs) => by
      intro is_desc id_in_xs final_desc_id
      cases id_in_xs
      case inl x_eq_id =>
        exact final_desc_id.elim ( by
          intro n final_to_id_in_n_steps
          rw [is_desc.left.symm, x_eq_id] at final_to_id_in_n_steps
          exact ⟨n, final_to_id_in_n_steps⟩
        )
      case inr id_in_xs =>
        let h := uf.path_containing_ancestor_end_ends_repeat id x xs is_desc.right id_in_xs
        exact final_desc_id.elim ( by
          intro n final_to_id_in_n_steps
          rw [is_desc.left.symm] at final_to_id_in_n_steps
          exact h ⟨n+1, final_to_id_in_n_steps⟩
        )

  theorem path_containing_end_ends_root {size : Nat} (uf : UnionFindLinks size) :
    ∀ id path, uf.is_descendency id path →
    path.prop_contains id → uf.is_root id := 
      λ id path is_desc id_in_path =>
      let id_is_repeat := uf.path_containing_ancestor_end_ends_repeat id id path is_desc id_in_path ⟨0, Eq.refl _⟩
      id_is_repeat.elim (uf.no_cycles id)
  
  theorem non_repeating_path {size : Nat} (uf : UnionFindLinks size) :
    ∀ id path, uf.is_descendency id path → ¬uf.is_root id → (id::path).unique := by
      intro id path is_desc not_root
      constructor
      case left =>
        intro id_in_path
        apply not_root
        let id_is_repeat := uf.path_containing_ancestor_end_ends_repeat id id path is_desc id_in_path ⟨0, Eq.refl _⟩
        exact id_is_repeat.elim (uf.no_cycles id)
      case right =>
        cases path
        case nil =>
          trivial
        case cons x xs =>
          let x_not_root : ¬uf.is_root x := by
            intro x_is_root
            rw [is_desc.left.symm] at not_root
            rw [x_is_root] at not_root
            exact not_root x_is_root
          exact uf.non_repeating_path x xs is_desc.right x_not_root

  def root_distance_aux {size : Nat} (uf : UnionFindLinks size) :
    (id : Fin size) → (n : Nat) →
    (∃ desc : List (Fin size),
      uf.is_descendency id desc ∧
      desc.length + n = size
    ) →
    {
      path_length : Nat //
      uf.rooted_in_exact_steps id path_length
    } :=
    λ id n desc_ex =>
    if hroot : uf.parent id = id then
      ⟨0, hroot, 
        λ _ h _ =>
        Nat.not_lt_zero _ h
      ⟩
    else 
      let parent := uf.parent id
      let next_n := n-1

      --if n is zero, that means we've failed to find the parent size times.
      --that leaves us with more nodes on the path to root than can exist.
      let n_ne_zero : n ≠ 0 := desc_ex.elim (
        λ desc ⟨h_desc, h_length⟩ =>

        let next_desc := id :: desc
        
        λ n_eq_zero =>
        let desc_length_size : desc.length = size := by rw [n_eq_zero] at h_length; exact h_length
        let next_desc_larger : next_desc.length = size + 1 := congrArg Nat.succ desc_length_size
        let next_desc_too_big : next_desc.length > size := by
          rw [next_desc_larger]
          exact Nat.lt_succ_self size
        let next_desc_unique : next_desc.unique := uf.non_repeating_path id desc h_desc hroot
        pigeonhole_principle next_desc_unique next_desc_too_big
      )
      
      let next_desc_ex :
        ∃ desc : List (Fin size),
          uf.is_descendency parent desc ∧
          desc.length + next_n = size := desc_ex.elim (
        λ desc ⟨h_desc, h_length⟩ =>
        
        let next_desc := id :: desc
        let next_is_desc : uf.is_descendency parent next_desc :=
          ⟨by rfl, h_desc⟩
        let next_right_length : next_desc.length + next_n = size := by
          rw [(Nat.succ_pred n_ne_zero).symm] at h_length
          let h_length : desc.length + (next_n + 1) = size := h_length
          rw [Nat.add_comm next_n 1, (Nat.add_assoc _ _ _).symm] at h_length
          exact h_length 
        
        ⟨next_desc, next_is_desc, next_right_length⟩
      )

      --not needed apparently? I guess the n_ne_zero already does it?
      --let term : next_n < n := Nat.pred_lt n_ne_zero

      let ⟨parent_root_dist, root_in_dist_steps, not_less_steps⟩ := uf.root_distance_aux parent next_n next_desc_ex
      let our_root_dist := parent_root_dist + 1
      let our_root_dist_proof : uf.is_root (Nat.repeat uf.parent our_root_dist id) := root_in_dist_steps
      let our_first_dist_proof : ∀ (n : Nat),
        n < our_root_dist →
        ¬uf.is_root (Nat.repeat uf.parent n id) := by
        intro n hn
        cases n
        case zero =>
          exact hroot
        case succ n =>
          let hn := Nat.lt_of_succ_lt_succ hn
          exact not_less_steps n hn
      ⟨our_root_dist, our_root_dist_proof, our_first_dist_proof⟩
    

  def root_distance {size : Nat} (uf : UnionFindLinks size) (id : Fin size) : Nat :=
    (uf.root_distance_aux id size ⟨[], trivial, (by rw [Nat.add_comm]; rfl)⟩).val
  
  theorem root_distance_property {size : Nat} (uf : UnionFindLinks size) (id : Fin size) : uf.rooted_in_exact_steps id (uf.root_distance id) :=
    (uf.root_distance_aux id size ⟨[], trivial, (by rw [Nat.add_comm]; rfl)⟩).property

  theorem parent_nearer_root {size : Nat} (uf : UnionFindLinks size) :
    (id : Fin size) →
    (¬uf.is_root id) →
    uf.root_distance (uf.parent id) < uf.root_distance id :=
    λ id not_root =>
    if h : uf.root_distance (uf.parent id) < uf.root_distance id then
      h
    else False.elim (
      let root_distance_not_zero : uf.root_distance id ≠ 0 := by
        intro is_zero
        apply not_root
        let h := (uf.root_distance_property id).left
        rw [is_zero] at h
        exact h
      let h : uf.root_distance id ≤ uf.root_distance (uf.parent id)     := Nat.ge_of_not_lt h
      let h : uf.root_distance id < uf.root_distance (uf.parent id) + 1 := Nat.lt_succ_of_le h
      let h : uf.root_distance id - 1 < uf.root_distance (uf.parent id) := Nat.lt_of_succ_lt_succ (by
        let h' : Nat.succ (uf.root_distance id - 1) = uf.root_distance id := Nat.succ_pred root_distance_not_zero
        rw [h']
        exact h
      )

      (uf.root_distance_property (uf.parent id)).right (uf.root_distance id - 1) h (by
        let h := (uf.root_distance_property id).left
        rw [(Nat.succ_pred root_distance_not_zero).symm] at h
        exact h
      )
    )
  
  theorem root_ancestors_equal {size : Nat} (uf : UnionFindLinks size) :
    ∀ (id r1 r2 : Fin size),
    uf.is_root r1 → uf.is_root r2 →
    uf.is_ancestor id r1 → uf.is_ancestor id r2 →
    r1 = r2
  | id, r1, r2, r1_is_root, r2_is_root, r1_anc_id, r2_anc_id =>
    if hid : uf.parent id = id then
      let all_ancestors_same : ∀ n, Nat.repeat uf.parent n id = id := by
        intro n
        induction n
        case zero => rfl
        case succ n hind =>
          show Nat.repeat uf.parent n (uf.parent id) = id
          rw [hid]; exact hind
      let r1_eq_id : r1 = id := r1_anc_id.elim λ n h => h.symm.trans $ all_ancestors_same n
      let r2_eq_id : r2 = id := r2_anc_id.elim λ n h => h.symm.trans $ all_ancestors_same n
      r1_eq_id.trans r2_eq_id.symm
    else
      let r1_anc_parent : uf.is_ancestor (uf.parent id) r1 := r1_anc_id.elim (by
        intro n; cases n
        case zero =>
          intro id_eq_r1; let id_eq_r1 : id = r1 := id_eq_r1
          rw [id_eq_r1.symm] at r1_is_root
          contradiction
        case succ n =>
          intro h; exact ⟨n, h⟩
      )
      let r2_anc_parent : uf.is_ancestor (uf.parent id) r2 := r2_anc_id.elim (by
        intro n; cases n
        case zero =>
          intro id_eq_r2; let id_eq_r2 : id = r2 := id_eq_r2
          rw [id_eq_r2.symm] at r2_is_root
          contradiction
        case succ n =>
          intro h; exact ⟨n, h⟩
      )
      let _terminator := uf.parent_nearer_root id hid
      uf.root_ancestors_equal (uf.parent id) r1 r2 r1_is_root r2_is_root r1_anc_parent r2_anc_parent
    termination_by root_ancestors_equal _ _ id _ _ _ _ _ _ => uf.root_distance id
  

  def expand {size : Nat} (uf : UnionFindLinks size) : UnionFindLinks (size+1) :=
    let new_elem : Fin (size + 1) := ⟨size, Nat.lt_succ_self size⟩
    let new_FinArray := uf.val.expand new_elem
    UnionFindLinks.from_rooted new_FinArray (
      λ id =>
      if hlast : id.val = size then by
        constructor
        case w => exact 0
        case h =>
          let h : new_FinArray.get new_elem = new_elem := uf.val.expand_get_last new_elem
          let g : new_elem = id := Fin.eq_of_val_eq hlast.symm
          rw [g] at h
          exact h
      else
        let same_get : ∀ id : Fin size, (new_FinArray.get (Fin.weaken (Nat.le.step Nat.le.refl) id)).val = (uf.parent id).val :=
          λ id =>
          uf.val.expand_get_other new_elem id
        let rec same_get_repeat : ∀ id n, (Nat.repeat new_FinArray.get n (Fin.weaken (Nat.le.step Nat.le.refl) id)).val = (Nat.repeat uf.parent n id).val
        | id, 0 => by rfl
        | id, n+1 => by
          let a : (Nat.repeat new_FinArray.get n (Fin.weaken (Nat.le.step Nat.le.refl) (uf.parent id))).val = (Nat.repeat uf.parent (n+1) id).val := same_get_repeat (uf.parent id) n
          let b : Fin.weaken (Nat.le.step Nat.le.refl) (uf.parent id) = new_FinArray.get (Fin.weaken (Nat.le.step Nat.le.refl) id) := by
            apply Fin.eq_of_val_eq
            rw [Fin.weaken_preserves_val]
            exact (same_get id).symm
          rw [b] at a
          exact a
        let constrained_id : Fin size := ⟨id.val, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ id.isLt) hlast⟩
        (uf.rooted constrained_id).elim ( by
          intro steps old_uf_rooted_in_steps
          constructor
          case w => exact steps
          case h =>
            let r := Nat.repeat new_FinArray.get steps id
            let s := Nat.repeat uf.parent steps constrained_id
            let h : r.val = s.val := same_get_repeat constrained_id steps
            let s_is_root : uf.parent s = s := old_uf_rooted_in_steps
            let r_eq_s_parent : r.val = (uf.parent s).val := h.trans (Fin.val_eq_of_eq s_is_root).symm
            let h' : (new_FinArray.get r).val = (uf.parent s).val := by
              rw [(Nat.repeat_assoc new_FinArray.get steps id).symm]
              rw [(Nat.repeat_assoc uf.parent steps constrained_id).symm]
              exact same_get_repeat constrained_id (steps+1)
            let r_eq_r_parent : new_FinArray.get r = r := by
              apply Fin.eq_of_val_eq
              exact h'.trans r_eq_s_parent.symm
            exact r_eq_r_parent
        )
    )
  
  theorem expand_preserves_parent {size : Nat} (uf : UnionFindLinks size) :
    ∀ id : Fin size, uf.expand.parent (Fin.weaken (Nat.le.step Nat.le.refl) id) = Fin.weaken (Nat.le.step Nat.le.refl) (uf.parent id)
  | id => Fin.eq_of_val_eq (uf.val.expand_get_other ⟨size, Nat.lt_succ_self _⟩ id)
  
  theorem expand_last_root {size : Nat} (uf : UnionFindLinks size) :
    uf.expand.is_root ⟨size, Nat.lt_succ_self _⟩ :=
    uf.val.expand_get_last ⟨size, Nat.lt_succ_self _⟩
  
  theorem expand_preserves_ancestry {size : Nat} (uf : UnionFindLinks size) :
    ∀ id anc : Fin size,
    uf.is_ancestor id anc ↔
    uf.expand.is_ancestor ⟨id.val, Nat.lt.step id.isLt⟩ ⟨anc.val, Nat.lt.step anc.isLt⟩
  | id, anc =>
    let weaken : Fin size → Fin (size + 1) := Fin.weaken (Nat.le.step Nat.le.refl)
    let repeat_parent_equal : ∀ n : Nat, Nat.repeat uf.expand.parent n (weaken id) = weaken (Nat.repeat uf.parent n id) := by
      intro n; induction n
      case zero =>
        rfl
      case succ n hind =>
        show Nat.repeat uf.expand.parent n (uf.expand.parent (weaken id)) = weaken (Nat.repeat uf.parent n (uf.parent id))
        rw [Nat.repeat_assoc uf.expand.parent n (weaken id)]
        rw [Nat.repeat_assoc uf.parent n id]
        rw [hind]
        exact uf.expand_preserves_parent $ Nat.repeat uf.parent n id
    ⟨
      λ hanc =>
      hanc.elim ( by
        intro n h
        rw [h.symm]
        show uf.expand.is_ancestor (weaken id) (weaken (Nat.repeat uf.parent n id))
        exact ⟨n, repeat_parent_equal n⟩
      )
    ,
      λ hancout =>
      hancout.elim ( by
        intro n h
        let h : Nat.repeat uf.expand.parent n (weaken id) = Fin.weaken (Nat.le.step Nat.le.refl) anc := h
        let h' := repeat_parent_equal n
        rw [h] at h'
        let h' := Fin.val_eq_of_eq h'
        let h' : anc.val = (Nat.repeat (parent uf) n id).val := h'
        exact ⟨n, Fin.eq_of_val_eq h'.symm⟩
      )
    ⟩

  theorem expand_last_nanc_old {size : Nat} (uf : UnionFindLinks size) :
    ∀ id : Fin (size+1),
    id.val ≠ size →
    ¬uf.expand.is_ancestor id ⟨size, Nat.lt.base size⟩
  | id, id_ne_last, last_anc_id =>
    if hroot : uf.expand.parent id = id then
      let id_anc_self : uf.expand.is_ancestor id id := ⟨0, by rfl⟩
      let id_eq_last := uf.expand.root_ancestors_equal id id ⟨size, Nat.lt.base size⟩ hroot (uf.expand_last_root) id_anc_self last_anc_id
      id_ne_last $ Fin.val_eq_of_eq id_eq_last
    else
      let _terminator := uf.expand.parent_nearer_root id hroot
      let parent_ne_last : (uf.expand.parent id).val ≠ size := by
        intro parent_eq_last
        let strengthened_id : Fin size := ⟨id.val, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ id.isLt) id_ne_last⟩
        let parent_eq_strengthened_parent : uf.expand.parent id = Fin.weaken (Nat.le.step Nat.le.refl) (uf.parent strengthened_id) := uf.expand_preserves_parent strengthened_id
        let parent_eq_strengthened_parent : (uf.expand.parent id).val = (uf.parent strengthened_id).val := Fin.val_eq_of_eq parent_eq_strengthened_parent
        let parent_lt_last := (uf.parent strengthened_id).isLt
        rw [parent_eq_strengthened_parent.symm] at parent_lt_last
        let parent_ne_last := Nat.ne_of_lt parent_lt_last
        contradiction
      let last_anc_parent : uf.expand.is_ancestor (uf.expand.parent id) ⟨size, Nat.lt.base size⟩ := by
        apply last_anc_id.elim; intro n
        cases n
        case zero =>
          intro id_eq_last; let id_eq_last : id.val = size := Fin.val_eq_of_eq id_eq_last
          contradiction
        case succ n =>
          intro sn_steps
          exact ⟨n, sn_steps⟩
      uf.expand_last_nanc_old (uf.expand.parent id) parent_ne_last last_anc_parent
  termination_by expand_last_nanc_old uf _ id _ _ => uf.expand.root_distance id

  def set_to_root_raw {size : Nat} (uf : UnionFindLinks size) :
    Fin size → uf.roots → FinArray size :=
    λ set_loc new_root =>
    uf.val.set set_loc new_root.val
  
  def set_to_root_gives_rooted {size : Nat} (uf : UnionFindLinks size)
    (set_loc : Fin size) (new_root : uf.roots) (id : Fin size) :
    let new_FinArray := uf.set_to_root_raw set_loc new_root
    ∃ steps,
      let r := Nat.repeat new_FinArray.get steps id
      new_FinArray.get r = r :=
    
    let new_FinArray := uf.set_to_root_raw set_loc new_root
    if hchanged : id = set_loc then
      let get_eq_new_root : new_FinArray.get set_loc = new_root.val := uf.val.get_set set_loc new_root.val
      let get_eq_new_root' : new_FinArray.get id = new_root.val := by
        rw [hchanged.symm] at get_eq_new_root
        exact get_eq_new_root
      let get_is_a_root : new_FinArray.get (new_FinArray.get id) = new_FinArray.get id := by
        rw [get_eq_new_root']
        exact if h : set_loc = new_root.val then by
          rw [h] at get_eq_new_root
          exact get_eq_new_root
        else by
          let h' : uf.val.get new_root.val = new_FinArray.get new_root.val := uf.val.get_set_ne set_loc new_root.val new_root.val h
          rw [h'.symm]
          exact new_root.property
      ⟨1, get_is_a_root⟩
    else
      let same_get : uf.parent id = new_FinArray.get id := uf.val.get_set_ne set_loc id new_root.val (λ x => hchanged x.symm)
      if hroot : uf.parent id = id then
        ⟨0, by rw [same_get] at hroot; exact hroot⟩
      else
        --required for termination
        let _hterm : uf.root_distance (uf.parent id) < uf.root_distance id :=
          uf.parent_nearer_root id hroot

        (uf.set_to_root_gives_rooted set_loc new_root (uf.parent id)).elim (
          λ steps hsteps =>
          ⟨steps+1, by rw [same_get] at hsteps; exact hsteps⟩
        )
  termination_by set_to_root_gives_rooted uf set_loc new_root id => uf.root_distance id

  def set_to_root {size : Nat} (uf : UnionFindLinks size) :
    Fin size → uf.roots → UnionFindLinks size :=
    λ set_loc new_root =>
    let new_FinArray := uf.set_to_root_raw set_loc new_root
    let is_rooted := uf.set_to_root_gives_rooted set_loc new_root
    UnionFindLinks.from_rooted new_FinArray is_rooted
  
  --simple, but inefficient. Good for proofs.
  --"silent" in that it doesn't spit out a modified unionfind.
  --unused. There's not actually any reason to ever find silently.
  --if finding proofs, then there's no reason to stop considering the old unionfind.
  def silent_find {size : Nat} (uf : UnionFindLinks size) :
    Fin size → uf.roots := λ id =>
    if hroot : uf.parent id = id then
      ⟨id, hroot⟩
    else
      let _hterm : uf.root_distance (uf.parent id) < uf.root_distance id :=
        uf.parent_nearer_root id hroot
      uf.silent_find (uf.parent id)
  termination_by silent_find id => uf.root_distance id


  def equivalent_to {size : Nat} (uf uf' : UnionFindLinks size) : Prop :=
    ∀ {a : Fin size}, uf.is_root a →
      uf'.is_root a ∧
      ∀ b : Fin size, uf.is_ancestor b a → uf'.is_ancestor b a
  
  theorem equivalent_reflexive {size : Nat} (uf : UnionFindLinks size) : uf.equivalent_to uf :=
    λ {_} hroot => ⟨hroot, λ _ is_anc => is_anc⟩
  
  theorem equivalent_symmetric {size : Nat} {uf uf' : UnionFindLinks size} :
    uf.equivalent_to uf' → uf'.equivalent_to uf :=
    λ uf_equiv_uf' r is_root' =>
    let is_root : uf.is_root r :=
      (uf.rooted r).elim ( by
        intro n
        let true_root := Nat.repeat uf.parent n r
        intro true_root_is_root; let true_root_is_root : uf.parent true_root = true_root := true_root_is_root
        let true_root_anc_r : uf.is_ancestor r true_root := ⟨n, by rfl⟩
        let true_root_anc'_r : uf'.is_ancestor r true_root := (uf_equiv_uf' true_root_is_root).right r true_root_anc_r
        
        let r_eq_true_root_sufficient : r = true_root → uf.is_root r := by
          intro r_eq_true_root
          rw [r_eq_true_root.symm] at true_root_is_root
          exact true_root_is_root
        apply r_eq_true_root_sufficient
        apply true_root_anc'_r.elim
        intro n; induction n;
        case zero =>
          intro r_eq_true_root
          exact r_eq_true_root
        case succ n hind =>
          intro true_root_in_sn_steps; let true_root_in_sn_steps : Nat.repeat uf'.parent n (uf'.parent r) = true_root := true_root_in_sn_steps
          apply hind
          rw [is_root'] at true_root_in_sn_steps
          exact true_root_in_sn_steps
      )
    
    ⟨is_root, (
      λ id r_anc'_id => (uf.rooted id).elim ( by
        intro n
        let root := Nat.repeat uf.parent n id
        intro hroot; let hroot : uf.is_root root := hroot
        let hroot' : uf'.is_root root := (uf_equiv_uf' hroot).left
        let root_anc_id : uf.is_ancestor id root := ⟨n, by rfl⟩
        let root_anc'_id : uf'.is_ancestor id root := (uf_equiv_uf' hroot).right id root_anc_id
        let root_eq_r : root = r := uf'.root_ancestors_equal id root r hroot' is_root' root_anc'_id r_anc'_id
        rw [root_eq_r] at root_anc_id
        exact root_anc_id
      )
    )⟩
  
  theorem equivalent_transitive {size : Nat} {uf uf' uf'' : UnionFindLinks size} :
    uf.equivalent_to uf' → uf'.equivalent_to uf'' → uf.equivalent_to uf'' :=
    λ uf_equiv_uf' uf'_equiv_uf'' _r is_root =>
    let is_root' := (uf_equiv_uf' is_root).left
    ⟨
      (uf'_equiv_uf'' is_root').left
    ,
      λ id r_anc_id => (uf'_equiv_uf'' is_root').right id $ (uf_equiv_uf' is_root).right id r_anc_id
    ⟩


  theorem contract_keeps_roots {size : Nat} (uf : UnionFindLinks size) :
    ∀ (id : Fin size) (root : uf.roots),
    uf.is_ancestor id root.val →
    ∀ r, uf.is_root r → (uf.set_to_root id root).is_root r :=
    λ id root root_ancestor_of_id =>
    λ r hroot =>
    if hid : id = r then
    let h : (uf.val.set id root.val).get r = r := by
      rw [hid.symm, uf.val.get_set id root.val]
      apply root_ancestor_of_id.elim
      intro a
      induction a
      case zero =>
        exact Eq.symm
      case succ a hind =>
        intro root_in_steps
        let root_in_steps : Nat.repeat uf.parent a (uf.parent id) = root.val := root_in_steps
        let id_is_root : uf.parent r = r := hroot
        let id_is_root : uf.parent id = id := by rw [hid.symm] at id_is_root; exact id_is_root
        rw [id_is_root] at root_in_steps
        exact hind root_in_steps
    h
  else
    let g := uf.val.get_set_ne id r root.val hid
    let h : (uf.val.set id root.val).get r = r := by
      let hroot : uf.val.get r = r := hroot
      rw [hroot] at g
      exact g.symm
    h

  theorem contract_preserves_ancestry {size : Nat} (uf : UnionFindLinks size) :
    ∀ (id : Fin size) (root : uf.roots),
    uf.is_ancestor id root.val →
    ∀ r, uf.is_root r →
    ∀ a : Fin size, uf.is_ancestor a r → (uf.set_to_root id root).is_ancestor a r :=
    λ id root root_ancestor_of_id =>
    λ r hroot =>
    λ a r_ancestor_of_a =>
    if hid : id = a then

      let new_parent_is_root : (uf.val.set id root.val).get a = root.val := by
        rw [hid]
        exact uf.val.get_set a root.val
      
      
      let r_must_be_root : root.val = r := by
        rw [hid.symm] at r_ancestor_of_a
        exact uf.root_ancestors_equal id root.val r root.property hroot root_ancestor_of_id r_ancestor_of_a

      ⟨1, new_parent_is_root.trans r_must_be_root⟩
    else
    
    let same_lookup : (uf.set_to_root id root).parent a = uf.parent a :=
      (uf.val.get_set_ne id a root.val hid).symm
    if hbasecase : uf.parent a = a then
      ⟨0, r_ancestor_of_a.elim (by
        intro n
        induction n
        case zero =>
          intro h; exact h
        case succ n hind =>
          intro sn_steps
          let sn_steps : Nat.repeat uf.parent n (uf.parent a) = r := sn_steps
          rw [hbasecase] at sn_steps
          exact hind sn_steps
      )⟩
    
    else
      let r_ancestor_of_parent : uf.is_ancestor (uf.parent a) r := r_ancestor_of_a.elim ( by
        intro n
        cases n
        case zero =>
          intro a_eq_r
          let a_eq_r : a = r := a_eq_r
          rw [a_eq_r] at hbasecase
          contradiction
        case succ n =>
          intro h
          exact ⟨n, h⟩
      )
      
      let _terminator := uf.parent_nearer_root a hbasecase
      let parents_agree := uf.contract_preserves_ancestry id root root_ancestor_of_id r hroot (uf.parent a) r_ancestor_of_parent
      parents_agree.elim (
        λ n n_steps_from_parent => 

        let h : Nat.repeat (uf.set_to_root id root).parent n ((uf.set_to_root id root).parent a) = r := by
          rw [same_lookup]
          exact n_steps_from_parent

        ⟨n+1, h⟩
      )
  termination_by contract_preserves_ancestry _ _ _ _ _ _ _ a _ => uf.root_distance a

  theorem contract_equivalence {size : Nat} (uf : UnionFindLinks size) :
    ∀ (id : Fin size) (root : uf.roots),
    uf.is_ancestor id root.val →
    uf.equivalent_to (uf.set_to_root id root) :=
    λ id root root_ancestor_of_id =>
    λ {r} hroot =>
    ⟨
      uf.contract_keeps_roots id root root_ancestor_of_id r hroot
    , 
      uf.contract_preserves_ancestry id root root_ancestor_of_id r hroot
    ⟩

  theorem unite_sets_targetted_root {size : Nat} (uf : UnionFindLinks size) :
    ∀ (old_root : Fin size) (new_root : uf.roots),
    uf.is_root old_root →
    (uf.set_to_root old_root new_root).parent old_root = new_root.val
  | old_root, new_root, _ =>
    uf.val.get_set old_root new_root.val
  
  theorem unite_keeps_set_root {size : Nat} (uf : UnionFindLinks size) :
    ∀ (old_root : Fin size) (new_root : uf.roots),
    uf.is_root old_root →
    (uf.set_to_root old_root new_root).is_root new_root.val
  | old_root, ⟨new_root, new_root_is_root⟩, _ =>
    if h : old_root = new_root then by
      rw [h]
      exact uf.val.get_set new_root new_root
    else
      (uf.val.get_set_ne old_root new_root new_root h).symm.trans new_root_is_root
  
  theorem unite_keeps_ancestors {size : Nat} (uf : UnionFindLinks size) :
    ∀ (old_root : Fin size) (new_root : uf.roots),
    uf.is_root old_root →
    ∀ id anc : Fin size,
    uf.is_ancestor id anc →
    (uf.set_to_root old_root new_root).is_ancestor id anc
  | old_root, new_root, old_is_root, id, anc, anc_of_id =>
    if hmodified : old_root = id then
      let id_eq_anc : id = anc := anc_of_id.elim (by
        intro n; induction n
        case zero => intro id_eq_anc; exact id_eq_anc
        case succ n hind =>
          intro sn_steps; let sn_steps : Nat.repeat uf.parent n (uf.parent id) = anc := sn_steps
          let id_is_root : uf.parent id = id := by rw [hmodified] at old_is_root; exact old_is_root
          rw [id_is_root] at sn_steps
          exact hind sn_steps
      )
      ⟨0, id_eq_anc⟩
    else if hidroot : uf.parent id = id then
      let id_eq_anc : id = anc := anc_of_id.elim ( by
        intro n; induction n
        case zero =>
          intro id_eq_anc; exact id_eq_anc
        case succ n hind =>
          intro sn_steps; let sn_steps : Nat.repeat uf.parent n (uf.parent id) = anc := sn_steps
          apply hind
          rw [hidroot] at sn_steps
          exact sn_steps
      )
      ⟨0, id_eq_anc⟩
    else if hid_anc : id = anc then
      ⟨0, hid_anc⟩
    else
      let same_parent : uf.parent id = (set_to_root uf old_root new_root).parent id := uf.val.get_set_ne old_root id new_root.val hmodified
      let anc_of_parent : uf.is_ancestor (uf.parent id) anc := anc_of_id.elim ( by
        intro n; cases n
        case zero =>
          intro id_eq_anc; contradiction
        case succ n =>
          intro sn_steps
          exact ⟨n, sn_steps⟩
      )
      let _terminator := uf.parent_nearer_root id hidroot
      (uf.unite_keeps_ancestors old_root new_root old_is_root (uf.parent id) anc anc_of_parent).elim ( by
        intro n n_steps
        rw [same_parent] at n_steps
        exact ⟨n+1, n_steps⟩
      )
  termination_by unite_keeps_ancestors _ _ _ _ _ id _ _ => uf.root_distance id

  theorem unite_ancestors_in_original {size : Nat} (uf : UnionFindLinks size) :
    ∀ (old_root : Fin size) (new_root : uf.roots),
    uf.is_root old_root →
    ∀ id anc : Fin size,
    anc ≠ new_root.val →
    (uf.set_to_root old_root new_root).is_ancestor id anc →
    uf.is_ancestor id anc
  | old_root, ⟨new_root, new_root_is_root⟩, old_root_is_root, id, anc, anc_ne_new_root, anc'_of_id =>
    
    let uf' := uf.set_to_root old_root ⟨new_root, new_root_is_root⟩
    
    if hmodified : old_root = id then
      anc'_of_id.elim ( by
        intro n n_steps
        cases n
        case zero =>
          exact ⟨0, n_steps⟩
        case succ n =>
          let n_steps : Nat.repeat uf'.parent n (uf'.parent id) = anc := n_steps
          rw [hmodified.symm] at n_steps
          let parent'_old_eq_new : uf'.parent old_root = new_root := uf.unite_sets_targetted_root old_root ⟨new_root, new_root_is_root⟩ old_root_is_root
          rw [parent'_old_eq_new] at n_steps
          let anc'_of_new_root : uf'.is_ancestor new_root anc := ⟨n, n_steps⟩
          let new_root_is_root' : uf'.is_root new_root := uf.unite_keeps_set_root old_root ⟨new_root, new_root_is_root⟩ old_root_is_root
          let anc_is_root' := uf'.root_ancestor_root new_root n new_root_is_root'
          rw [n_steps] at anc_is_root'
          let new_root_self_anc' : uf'.is_ancestor new_root new_root := ⟨0, by rfl⟩
          let anc_eq_new_root : anc = new_root := uf'.root_ancestors_equal new_root anc new_root anc_is_root' new_root_is_root' anc'_of_new_root new_root_self_anc'
          contradiction
      )
    else if hidroot : uf'.parent id = id then
      let id_eq_anc : id = anc := anc'_of_id.elim ( by
        intro n; induction n
        case zero =>
          intro id_eq_anc; exact id_eq_anc
        case succ n hind =>
          intro sn_steps; let sn_steps : Nat.repeat uf'.parent n (uf'.parent id) = anc := sn_steps
          apply hind
          rw [hidroot] at sn_steps
          exact sn_steps
      )
      ⟨0, id_eq_anc⟩
    else if hid_anc : id = anc then
      ⟨0, hid_anc⟩
    else by
      let same_parent : uf.parent id = uf'.parent id := uf.val.get_set_ne old_root id new_root hmodified
      let anc'_of_parent : uf'.is_ancestor (uf'.parent id) anc := anc'_of_id.elim ( by
        intro n; cases n
        case zero =>
          intro id_eq_anc; contradiction
        case succ n =>
          intro sn_steps
          exact ⟨n, sn_steps⟩
      )
      let _terminator := uf'.parent_nearer_root id hidroot
      let anc_of_parent : uf.is_ancestor (uf'.parent id) anc := uf.unite_ancestors_in_original old_root ⟨new_root, new_root_is_root⟩ old_root_is_root (uf'.parent id) anc anc_ne_new_root anc'_of_parent
      rw [same_parent.symm] at anc_of_parent
      apply anc_of_parent.elim
      intro n sn_steps
      exact ⟨n+1, sn_steps⟩
  termination_by unite_ancestors_in_original size uf old_root new_root _ id _ _ _ => (uf.set_to_root old_root new_root).root_distance id

  theorem unite_ambiguous_root {size : Nat} (uf : UnionFindLinks size) :
    ∀ (old_root : Fin size) (new_root : uf.roots),
    uf.is_root old_root →
    ∀ id : Fin size,
    (uf.set_to_root old_root new_root).is_ancestor id new_root.val →
    uf.is_ancestor id old_root ∨ uf.is_ancestor id new_root.val
  | old_root, ⟨new_root, new_root_is_root⟩, old_root_is_root, id, new_root_anc'_id =>
    
    let uf' := uf.set_to_root old_root ⟨new_root, new_root_is_root⟩
    
    if hold_root : old_root = id then
      Or.inl ⟨0, hold_root.symm⟩
    else if hnew_root : new_root = id then
      Or.inr ⟨0, hnew_root.symm⟩
    else by
      let same_parent : uf.parent id = uf'.parent id := uf.val.get_set_ne old_root id new_root hold_root
      let new_root_is_root' : uf'.is_root new_root := uf.unite_keeps_set_root old_root ⟨new_root, new_root_is_root⟩ old_root_is_root
      let not_root' : ¬uf'.is_root id :=
        λ is_root' =>
        let id_eq_new_root : id = new_root := uf'.root_ancestors_equal id id new_root is_root' new_root_is_root' ⟨0, by rfl⟩ new_root_anc'_id
        hnew_root id_eq_new_root.symm
      
      let _terminator := uf'.parent_nearer_root id not_root'
      let new_root_anc'_parent : uf'.is_ancestor (uf'.parent id) new_root := new_root_anc'_id.elim ( by
        intro n
        cases n
        case zero =>
          intro id_eq_new_root
          let new_root_eq_id := id_eq_new_root.symm
          contradiction
        case succ n =>
          intro sn_steps
          exact ⟨n, sn_steps⟩
      )
      let parent_result := uf.unite_ambiguous_root old_root ⟨new_root, new_root_is_root⟩ old_root_is_root (uf'.parent id) new_root_anc'_parent
      rw [same_parent.symm] at parent_result
      cases parent_result
      case inl old_root_anc_parent =>
        apply old_root_anc_parent.elim
        intro n sn_steps
        exact Or.inl ⟨n+1, sn_steps⟩
      case inr new_root_anc_parent =>
        apply new_root_anc_parent.elim
        intro n sn_steps
        exact Or.inr ⟨n+1, sn_steps⟩
  termination_by unite_ambiguous_root size uf old_root new_root old_root_is_root id new_root_anc'_id => (uf.set_to_root old_root new_root).root_distance id


  theorem unite_keeps_untargetted_roots {size : Nat} (uf : UnionFindLinks size) :
    ∀ (old_root : Fin size) (new_root : uf.roots),
    uf.is_root old_root →
    ∀ r : Fin size,
    r ≠ old_root →
    (uf.is_root r ↔ (uf.set_to_root old_root new_root).is_root r)
  | old_root, new_root, _, r, r_ne_old_root =>
    ⟨
      λ r_is_root =>
      let old_root_ne_r : old_root ≠ r := λ h => r_ne_old_root h.symm
      (uf.val.get_set_ne old_root r new_root.val old_root_ne_r).symm.trans r_is_root
    ,
      λ r_is_root' =>
      let old_root_ne_r : old_root ≠ r := λ h => r_ne_old_root h.symm
      (uf.val.get_set_ne old_root r new_root.val old_root_ne_r).trans r_is_root'
    ⟩

  def find_aux {size : Nat} (uf : UnionFindLinks size) (id : Fin size) :
    Σ (new_uf : UnionFindLinks size),
      {root : new_uf.roots //
      uf.is_ancestor id root.val ∧ 
      uf.equivalent_to new_uf} :=
    if hroot : uf.parent id = id then (
      ⟨uf, ⟨id, hroot⟩, ⟨0, by rfl⟩, uf.equivalent_reflexive⟩
    ) else
      --termination checking
      let _hterm : uf.root_distance (uf.parent id) < uf.root_distance id :=
        uf.parent_nearer_root id hroot

      let ⟨new_uf, root, is_correct_root, old_equiv_new⟩ := uf.find_aux (uf.parent id)
      let out_uf : UnionFindLinks size := new_uf.set_to_root id root

      let is_old_root : uf.is_root root.val := (equivalent_symmetric old_equiv_new root.property).left
      let is_correct_root : uf.is_ancestor id root.val := is_correct_root.elim (λ n h => ⟨n+1, h⟩)
      let root_anc'_id : new_uf.is_ancestor id root.val := (old_equiv_new is_old_root).right id is_correct_root

      let new_equiv_out : new_uf.equivalent_to out_uf := new_uf.contract_equivalence id root root_anc'_id
      
      let root : out_uf.roots := ⟨root.val, (new_equiv_out root.property).left⟩

      let old_equiv_out : uf.equivalent_to out_uf := UnionFindLinks.equivalent_transitive old_equiv_new new_equiv_out

      ⟨out_uf, root, is_correct_root, old_equiv_out⟩
  termination_by find_aux uf id => uf.root_distance id

  def find {size : Nat} : Fin size → StateM (UnionFindLinks size) (Fin size)
  | id, uf => (
    let ⟨new_uf, root, _⟩ := uf.find_aux id
    ⟨root.val, new_uf⟩
  )
  
end UnionFindLinks


--while ranks should store the number of children for each root,
--this isn't really an important invariant or anything, and is only
--there to help the program run faster, so no stored proof
--required for lean to accept.
structure UnionFind (size : Nat) : Type where
  (links : UnionFindLinks size)
  (ranks : {xs : Array Nat // xs.size = size})

namespace UnionFind
  def empty : UnionFind 0 := ⟨UnionFindLinks.empty, ⟨⟨[]⟩, by rfl⟩⟩

  def expand {size : Nat} : UnionFind size → UnionFind (size + 1)
  | ⟨links, ⟨ranks, ranks_size⟩⟩ => ⟨links.expand, ⟨ranks.push 1, by rw [ranks_size.symm]; exact ranks.size_push 1⟩⟩

  def union {size : Nat} : Fin size → Fin size → StateM (UnionFind size) (Fin size) :=
    λ id1 id2 uf =>
    let uf_links := uf.links
    let ⟨uf_links, root1, _, _    ⟩ := uf_links.find_aux id1
    let ⟨uf_links, root2, _, equiv⟩ := uf_links.find_aux id2

    let root1 : uf_links.roots := ⟨root1.val, (equiv root1.property).left⟩

    if root1.val = root2.val then
      ⟨root1.val, uf_links, uf.ranks⟩
    else
      let rank1 := uf.ranks.val.get ⟨
        root1.val,
        by rw [uf.ranks.property]; exact root1.val.isLt
      ⟩

      let rank2 := uf.ranks.val.get ⟨
        root2.val,
        by rw [uf.ranks.property]; exact root2.val.isLt
      ⟩

      let ⟨bigroot, smallroot⟩ :=
        if rank1 < rank2 then
          (root2, root1)
        else
          (root1, root2)
      
      let uf_links := uf_links.set_to_root smallroot.val bigroot
      
      let bigroot_array_loc : Fin uf.ranks.val.size := ⟨
        bigroot.val.val,
        by rw [uf.ranks.property]; exact bigroot.val.isLt
      ⟩

      let new_ranks := uf.ranks.val.set bigroot_array_loc (rank1 + rank2)
      let same_size := uf.ranks.val.size_set bigroot_array_loc (rank1 + rank2)
      let expected_size : new_ranks.size = size := same_size.trans uf.ranks.property

      ⟨bigroot.val, uf_links, new_ranks, expected_size⟩
    
    def find {size : Nat} : Fin size → StateM (UnionFind size) (Fin size) :=
      λ id uf =>
      let ⟨root, uf_links⟩ := do {
        UnionFindLinks.find id
      }.run uf.links
      ⟨root, uf_links, uf.ranks⟩
end UnionFind
