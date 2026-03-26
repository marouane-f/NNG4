## Inequality World

### Level 1
```lean
theorem le_refl (x : ℕ) : x ≤ x := by

use 0
decide
```

### Level 2
```lean
theorem zero_le (x : ℕ) : 0 ≤ x := by

use x
decide
rw [zero_add]
rfl
```

### Level 3
```lean
theorem le_succ_self (x : ℕ) : x ≤ succ x := by

use 1
decide
```

### Level 4
```lean
theorem le_trans (x y z : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by

cases hxy with a ha
cases hyz with b hn
use a+b
rw [hn]
rw [ha]
decide
rw [add_assoc]
rfl
```

### Level 5
```lean
theorem le_zero (x : ℕ) (hx : x ≤ 0) : x = 0 := by

cases hx with y h
induction x with d hd
trivial
symm at h
rw [succ_add] at h
apply succ_ne_zero at h
trivial
```

### Level 6
```lean
theorem le_antisymm (x y : ℕ) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by

cases hxy with c hc
cases hyx with d hd
rw [hc, add_assoc] at hd
symm at hd
apply add_right_eq_self at hd
apply add_right_eq_zero at hd
rw [hd, add_zero] at hc
exact hc.symm
```

### Level 7
```lean
example (x y : ℕ) (h : x = 37 ∨ y = 42) : y = 42 ∨ x = 37 := by

cases h with hx hy
right
exact hx
left
exact hy
```

### Level 8
```lean
theorem le_total (x y : ℕ) : x ≤ y ∨ y ≤ x := by

induction y with d hd
right
apply zero_le
cases hd with hp hq
left
cases hp with z hz
rw [succ_eq_add_one]
rw [hz]
use z + 1
rw [add_assoc]
rfl
cases hq with z hz
cases z with z1
rw [add_zero] at hz
left
rw [hz]
exact le_succ_self d
right
rw [succ_eq_add_one]
rw [succ_eq_add_one] at hz
rw [add_comm] at hz
rw [add_assoc] at hz
nth_rewrite 2 [add_comm] at hz
use z1
rw [add_comm]
exact hz
```

### Level 9
```lean
theorem succ_le_succ (x y : ℕ) (hx : succ x ≤ succ y) : x ≤ y := by

cases hx with c
use c
apply succ_inj
rw [succ_add] at h
exact h
```

### Level 10
```lean
theorem le_one (x : ℕ) (hx : x ≤ 1) : x = 0 ∨ x = 1 := by

cases x with x1
left
rfl
rw [one_eq_succ_zero] at hx
apply succ_le_succ x1 0 at hx
right
rw [one_eq_succ_zero]
apply le_zero at hx
rw [hx]
rfl
```

### Level 11
```lean
theorem le_two (x : ℕ) (hx : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := by

cases x with c
left
rfl
cases hx with a
cases a with a1
rw [add_zero] at h
right
right
symm
exact h
rw [succ_add] at h
rw [two_eq_succ_one] at h
apply succ_inj at h
rw [add_succ] at h
rw [one_eq_succ_zero] at h
apply succ_inj at h
symm at h
apply add_right_eq_zero at h
rw [h]
right
left
rw [← one_eq_succ_zero]
rfl
```