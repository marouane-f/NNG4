## Implication World

### Level 1
```lean
example (x y z : ℕ) (h1 : x + y = 37) (h2 : 3 * x + z = 42) : x + y = 37 := by

exact h1
```

### Level 2
```lean
example (x y : ℕ) (h : 0 + x = 0 + y + 2) : x = y + 2 := by

rw [zero_add] at h
rw [zero_add] at h
exact h
```

### Level 3
```lean
example (x y : ℕ) (h1 : x = 37) (h2 : x = 37 → y = 42) : y = 42 := by

apply h2 at h1
exact h1
```

### Level 4
```lean
example (x : ℕ) (h : x + 1 = 4) : x = 3 := by

rw [← succ_eq_add_one] at h
rw [four_eq_succ_three] at h
apply succ_inj at h
exact h
```

### Level 5
```lean
example (x : ℕ) (h : x + 1 = 4) : x = 3 := by

apply succ_inj
rw [succ_eq_add_one]
rw [← four_eq_succ_three]
exact h
```

### Level 6
```lean
example (x : ℕ) : x = 37 → x = 37 := by

intro h
exact h
```

### Level 7
```lean
example (x y : ℕ) : x + 1 = y + 1 → x = y := by

intro h
apply succ_inj
repeat rw [succ_eq_add_one]
apply h
```

### Level 8
```lean
example (x y : ℕ) (h1 : x = y) (h2 : x ≠ y) : False := by

apply h2
exact h1
```

### Level 9
```lean
theorem zero_ne_one : (0 : ℕ) ≠ 1 := by

intro h
rw [one_eq_succ_zero] at h
apply zero_ne_succ at h
exact h
```

### Level 10
```lean
theorem one_ne_zero : (1 : ℕ) ≠ 0 := by

symm
apply zero_ne_one
```

### Level 11
```lean
example : succ (succ 0) + succ (succ 0) ≠ succ (succ (succ (succ (succ 0)))) := by

intro h
rw [succ_add] at h
rw [succ_add] at h
rw [zero_add] at h
apply succ_inj at h
apply succ_inj at h
apply succ_inj at h
apply succ_inj at h
apply zero_ne_succ at h
exact h
```