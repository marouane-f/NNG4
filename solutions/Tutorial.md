## Tutorial World

### Level 1
```lean
example (x q : ℕ) : 37 * x + q = 37 * x + q := by

rfl
```

### Level 2
```lean
example (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by

rw [h]
rfl
```

### Level 3
```lean
example : 2 = succ (succ 0) := by

rw [two_eq_succ_one]
rw [one_eq_succ_zero]
rfl
```

### Level 4
```lean
example : 2 = succ (succ 0) := by

rw [← one_eq_succ_zero]
rw [← two_eq_succ_one]
rfl
```

### Level 5
```lean
example (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by

rw [add_zero]
rw [add_zero]
rfl
```

### Level 6
```lean
example (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by

rw [add_zero c]
rw [add_zero b]
rfl
```

### Level 7
```lean
theorem succ_eq_add_one n : succ n = n + 1 := by

rw [one_eq_succ_zero]
rw [add_succ]
rw [add_zero n]
rfl
```

### Level 8
```lean
example : (2 : ℕ) + 2 = 4 := by

rw [← add_zero 4]
rw [four_eq_succ_three]
rw [add_zero]
rw [three_eq_succ_two]
nth_rewrite 2 [two_eq_succ_one]
rw [add_succ]
rw [← succ_eq_add_one]
rfl
```