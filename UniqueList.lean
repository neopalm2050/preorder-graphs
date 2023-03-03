universe u v

namespace List
  def prop_contains {α : Type u} : List α → α → Prop
    | [], _ => False
    | (x :: xs), y => (x = y) ∨ (prop_contains xs y)
  
  def unique {α : Type u} : List α → Prop
    | [] => True
    | x :: xs => ¬(xs.prop_contains x) ∧ (unique xs)


  def constrain {α : Type u} :
    (xs : List α) →
    {constraint : α → Prop} →
    (∀ x:α, xs.prop_contains x → constraint x) →
    List {x : α // constraint x}
  | [], _, _ => []
  | (x :: xs), constraint, holds => (

    let holds_xs : (∀ y:α, xs.prop_contains y → constraint y) := (
      λ y xs_contains_y =>
      let xxs_contains_y : (x :: xs).prop_contains y := (
        Or.inr xs_contains_y
      )
      holds y xxs_contains_y
    )

    let holds_x : constraint x := (
      let xxs_contains_x : (x :: xs).prop_contains x := (
        Or.inl (Eq.refl x)
      )
      holds x xxs_contains_x
    )

    let tail_out := constrain xs holds_xs
    let head_out := ⟨ x , holds_x ⟩

    head_out :: tail_out
  )

  theorem length_constrain {α : Type u} :
    (xs : List α) →
    {constraint : α → Prop} →
    (holds : (∀ x:α, xs.prop_contains x → constraint x)) →
    length (constrain xs holds) = length xs
  | [], _, _ => Eq.refl 0
  | (x :: xs), constraint, holds => (

    let holds_xs : (∀ y:α, xs.prop_contains y → constraint y) := (
      λ y xs_contains_y =>
      let xxs_contains_y : (x :: xs).prop_contains y := (
        Or.inr xs_contains_y
      )
      holds y xxs_contains_y
    )

    congrArg (Nat.succ) (length_constrain xs holds_xs)
  )

  theorem contains_constrain {α : Type u} :
    (xs : List α) →
    {constraint : α → Prop} →
    (holds : (∀ x:α, xs.prop_contains x → constraint x)) →
    ∀ {y:α}, (holds_y : constraint y) →
    (
      (constrain xs holds).prop_contains ⟨y,holds_y⟩ ↔
      xs.prop_contains y
    )
    | xs, constraint, holds, y, holds_y => by
      induction xs
      case nil =>
        apply Iff.intro
        case mp =>
          intro contradiction
          exact contradiction
        case mpr =>
          intro contradiction
          exact contradiction
      case cons h =>
      apply Iff.intro
      case mp =>
        intro contains_after_constrain
        cases contains_after_constrain
        case inl is_head =>
          let x_eq_y : _ = y := congrArg Subtype.val is_head
          rw [x_eq_y.symm]
          apply Or.inl
          simp
        case inr in_tail =>
          apply Or.inr
          exact (h (
            λ x x_in_tail =>
            holds x (Or.inr x_in_tail)
          )).mp in_tail
      
      case mpr =>
        intro contains_before_constrain
        cases contains_before_constrain
        case inl is_head =>
          apply Or.inl
          exact Subtype.eq is_head
        case inr in_tail =>
          apply Or.inr
          exact (h (
            λ x x_in_tail =>
            holds x (Or.inr x_in_tail)
          )).mpr in_tail

  theorem unique_constrain {α : Type u} :
    (xs : List α) →
    {constraint : α → Prop} →
    (holds : (∀ x:α, xs.prop_contains x → constraint x)) →
    (
      unique (constrain xs holds) ↔
      unique xs
    )
  | [], _, _ => by
    constructor
    case mp =>
      intro _
      trivial
    case mpr =>
      intro _
      trivial
  | (x :: xs), constraint, holds => by

    let holds_xs : ∀ x0:α, xs.prop_contains x0 → constraint x0 := by
      intro x0
      intro xs_contains_x0
      exact holds x0 (Or.inr xs_contains_x0)
    let holds_x : constraint x := by
      apply holds x
      apply Or.inl
      exact Eq.refl x
    constructor
    case mp =>
      intro unique_xxs_constrained
      let unique_xs_constrained := unique_xxs_constrained.right
      let unique_xs := (xs.unique_constrain holds_xs).mp unique_xs_constrained
      let xs_lacks_x_constrained := unique_xxs_constrained.left
      constructor
      case left =>
        intro xs_contains_x
        let xs_contains_x_constrained := (xs.contains_constrain holds_xs holds_x).mpr xs_contains_x
        exact xs_lacks_x_constrained xs_contains_x_constrained
      case right =>
        exact unique_xs
    case mpr =>
      intro unique_xxs
      let unique_xs := unique_xxs.right
      let unique_xs_constrained := (xs.unique_constrain holds_xs).mpr unique_xs
      let xs_lacks_x := unique_xxs.left
      constructor
      case left =>
        intro xs_contains_x_constrained
        let xs_contains_x := (xs.contains_constrain holds_xs holds_x).mp xs_contains_x_constrained
        exact xs_lacks_x xs_contains_x
      case right =>
        exact unique_xs_constrained
  
  theorem unique_injection {α β : Type u} :
    (xs : List α) →
    {f : α → β} →
    (∀ x y, f x = f y → x = y) →
    xs.unique →
    (List.map f xs).unique
  | [], _, _, _ => trivial
  | (x::xs), f, injective, unique => by
    constructor
    case left =>
      intro fxs_contains_fx
      apply unique.left
      induction xs
      case nil =>
        trivial
      case cons y ys h =>
        cases fxs_contains_fx
        case inl fx_eq_fy =>
          apply Or.inl
          exact injective y x fx_eq_fy
        case inr fx_in_fys =>
          apply Or.inr
          let xys_unique : List.unique (x::ys) := by
            constructor
            case left =>
              intro x_in_ys
              apply unique.left
              apply Or.inr
              exact x_in_ys
            case right =>
              exact unique.right.right
          exact h xys_unique fx_in_fys
    case right =>
      exact xs.unique_injection injective unique.right

  theorem contains_injection {α β : Type u} :
    (xs : List α) →
    {f : α → β} →
    (∀ x y, f x = f y → x = y) →
    ∀ x:α,
    (List.map f xs).prop_contains (f x) →
    xs.prop_contains x
  | [], _, _, _, impossible => impossible
  | (x::xs), f, injective, y, image_contains => by
    cases image_contains
    case inl fx_eq_fy =>
      apply Or.inl
      exact injective x y fx_eq_fy
    case inr image_tail_contains_y =>
      apply Or.inr
      exact xs.contains_injection injective y image_tail_contains_y

  theorem get_set {α : Type u} :
    (xs : List α) →
    (i : Fin xs.length) →
    (val : α) →
    (xs.set i.val val).get ⟨i.val, by rw [xs.length_set i.val val]; exact i.isLt⟩ = val
  | x::xs, ⟨0, isLt⟩, val => by rfl
  | _::xs, ⟨i+1, lt_proof⟩, val => get_set xs ⟨i, (Nat.lt_of_succ_lt_succ lt_proof)⟩ val

  theorem get_set_ne {α : Type u} :
    (xs : List α) →
    (i j : Fin xs.length) →
    (val : α) →
    i ≠ j →
    xs.get j = (xs.set i.val val).get ⟨j.val, by rw [xs.length_set i.val val]; exact j.isLt⟩
  | x::xs, ⟨0, _⟩, ⟨_+1, _⟩, _, _ => by rfl
  | x::xs, ⟨_+1, _⟩, ⟨0, _⟩, _, _ => by rfl
  | _::xs, ⟨i+1, hi⟩, ⟨j+1, hj⟩, val, si_ne_sj => (
    get_set_ne xs ⟨i, Nat.lt_of_succ_lt_succ hi⟩ ⟨j, Nat.lt_of_succ_lt_succ hj⟩
      val (
        λ si_eq_sj => si_ne_sj (Fin.eq_of_val_eq (
          congrArg Nat.succ (Fin.val_eq_of_eq si_eq_sj)
        ))
      )
  )

end List

#print List.set

theorem unique_saturated :
  {n : Nat} →
  {xs : List (Fin n)} → xs.unique →
  xs.length = n →
  ∀ x:Fin n, xs.prop_contains x
| 0, [], _, _ => (λ x => x.elim0)
| n+1, (x :: xs), uniqueness, maximal => (
  let xs_maximal : xs.length = n :=
    congrArg Nat.pred
      ((List.length_cons x xs).symm.trans maximal)
  
  let xs_lacks_x := uniqueness.left

  let xs_ne_x : ∀ x0:Fin n.succ, xs.prop_contains x0 → x0 ≠ x := by
    intro x0 xs_contains_x0 x0_eq_x
    apply xs_lacks_x
    rw [x0_eq_x.symm]
    exact xs_contains_x0

  let n_to_x_with_decidable : (x0 : {a : Fin (n+1) // a ≠ x}) → Decidable (x0.val.val = n) →
    {a : Fin n // a.val = x0.val.val ∨ (a.val = x ∧ x0.val = n)}
  | ⟨x0, x0_ne_x⟩, isTrue x0_eq_n => (
      let x_ne_n : x.val ≠ n := by
        intro x_eq_n
        apply x0_ne_x
        apply Fin.eq_of_val_eq
        rw [x0_eq_n, x_eq_n]
      let x_at_most_n : x.val ≤ n := Nat.le_of_lt_succ x.isLt
      let x_under_n : x.val < n := Nat.lt_of_le_of_ne x_at_most_n (x_ne_n)
      ⟨⟨x, x_under_n⟩, Or.inr ⟨Eq.refl x.val, x0_eq_n⟩⟩
    )
  | ⟨x0, x0_ne_x⟩, isFalse x0_ne_n => (
      let x0_at_most_n : x0.val ≤ n := Nat.le_of_lt_succ x0.isLt
      let x0_under_n : x0.val < n := Nat.lt_of_le_of_ne x0_at_most_n (x0_ne_n)
      ⟨⟨x0, x0_under_n⟩, Or.inl (Eq.refl x0.val)⟩
    )

  let n_to_x : (x0 : {a : Fin (n+1) // a ≠ x}) → Fin n :=
    λ x0 => (n_to_x_with_decidable x0 (x0.val.val.decEq n)).val
  
  let n_to_x_injective : ∀ y1 y2, n_to_x y1 = n_to_x y2 → y1 = y2 := by
    intro y1 y2
    intro fy1_eq_fy2
    cases (n_to_x_with_decidable y1 (y1.val.val.decEq n)).property
    case inl fy1_eq_y1 =>
      cases (n_to_x_with_decidable y2 (y2.val.val.decEq n)).property
      case inl fy2_eq_y2 =>
        apply Subtype.eq
        apply Fin.eq_of_val_eq
        rw [fy2_eq_y2.symm, fy1_eq_y1.symm]
        exact Fin.val_eq_of_eq fy1_eq_fy2
      case inr conj =>
        cases conj
        case intro fy2_eq_x y2_eq_n =>
        let fy1_eq_x := (Fin.val_eq_of_eq fy1_eq_fy2).trans fy2_eq_x
        let y1_eq_x := Fin.eq_of_val_eq (fy1_eq_y1.symm.trans fy1_eq_x)
        let impossible := y1.property y1_eq_x
        contradiction
    case inr conj =>
      cases conj
      case intro fy1_eq_x y1_eq_n =>
      cases (n_to_x_with_decidable y2 (y2.val.val.decEq n)).property
      case inl fy2_eq_y2 =>
        let fy2_eq_x := (Fin.val_eq_of_eq fy1_eq_fy2).symm.trans fy1_eq_x
        let y2_eq_x := Fin.eq_of_val_eq (fy2_eq_y2.symm.trans fy2_eq_x)
        let impossible := y2.property y2_eq_x
        contradiction
      case inr conj =>
      cases conj
      case intro fy2_eq_x y2_eq_n =>
        apply Subtype.eq
        apply Fin.eq_of_val_eq
        exact y1_eq_n.trans y2_eq_n.symm


  let xs_constrained : List (Fin n) := List.map n_to_x (xs.constrain xs_ne_x)

  let xs_constrained_maximal : xs_constrained.length = n := by
    rw [(xs.constrain xs_ne_x).length_map n_to_x]
    rw [xs.length_constrain xs_ne_x]
    exact xs_maximal

  let xs_constrained_unique : xs_constrained.unique := by
    apply (xs.constrain xs_ne_x).unique_injection n_to_x_injective
    apply (xs.unique_constrain xs_ne_x).mpr
    exact uniqueness.right
  
  λ y =>

  (x.val.decEq y).byCases (
    λ x_eq_y =>
    Or.inl (Fin.eq_of_val_eq x_eq_y)
  ) (
    λ x_ne_y =>
    let y_with_proof : {a : Fin (n+1) // a ≠ x} := ⟨y, (λ y_eq_x => x_ne_y (Fin.val_eq_of_eq y_eq_x.symm))⟩
    let z : Fin n := n_to_x y_with_proof
    let z_in_xs_constrained := unique_saturated xs_constrained_unique xs_constrained_maximal z
    let y_in_xs_mapped := (xs.constrain xs_ne_x).contains_injection n_to_x_injective y_with_proof z_in_xs_constrained
    let y_in_xs : xs.prop_contains y := (xs.contains_constrain xs_ne_x y_with_proof.property).mp y_in_xs_mapped
    Or.inr y_in_xs
  )
)

theorem pigeonhole_principle :
  {n : Nat} →
  {xs : List (Fin n)} → xs.unique →
  xs.length > n →
  False
| n, (x::xs), unique, too_big => (
  let xs_at_least_saturated := Nat.le_of_lt_succ too_big
  (Nat.eq_or_lt_of_le xs_at_least_saturated).elim (
    λ xs_saturated =>
    let x_in_xs := unique_saturated unique.right xs_saturated.symm x
    unique.left x_in_xs
  ) (
    λ xs_too_big =>
    pigeonhole_principle unique.right xs_too_big
  )
)