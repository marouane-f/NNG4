## Addition World

### Level 1
```lean
theorem zero_add (n : ℕ) : 0 + n = n := by

induction n with d hd
rw [add_zero]
rfl
rw [add_succ]
rw [  hd]
rfl
```

### Level 2
```lean
theorem succ_add (a b : ℕ) : succ a + b = succ (a + b) := by

induction b with d hd
rw [add_zero a]
rw [add_zero]
rfl
rw [add_succ]
rw [hd]
rw [add_succ]
rfl
```

### Level 3
```lean
theorem add_comm (a b : ℕ) : a + b = b + a := by

induction b with d hd
rw [add_zero]
rw [zero_add]
rfl
rw [  add_succ]
rw [succ_add]
rw [hd]
rfl
```

### Level 4
```lean
theorem add_assoc (a b c : ℕ) : a + b + c = a + (b + c) := by

induction a with d hd
rw [zero_add]
rw [zero_add]
rfl
rw [succ_add]
rw [succ_add]
rw [succ_add]
rw [succ_eq_add_one]
rw [succ_eq_add_one]
rw [hd]
rfl
```

### Level 5
```lean
theorem add_right_comm (a b c : ℕ) : a + b + c = a + c + b := by

rw [add_comm]
rw [← add_assoc]
nth_rewrite 2 [add_comm]
rfl
```