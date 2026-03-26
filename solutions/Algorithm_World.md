## Algorithm World

### Level 1
```lean
theorem add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by

rw [← add_assoc a b c]
rw [add_comm a b]
rw [add_assoc b a c]
rfl
```

### Level 2
```lean
example (a b c d : ℕ) : a + b + (c + d) = a + c + d + b := by

repeat rw [add_assoc]
rw [add_left_comm b c]
rw [add_comm b d]
rfl
```

### Level 3
```lean
example (a b c d e f g h : ℕ) : (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by

simp only [add_left_comm, add_comm]
```

### Level 4
```lean
example (a b c d e f g h : ℕ) : (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by

simp_add
```

### Level 5
```lean
example (a b : ℕ) (h : succ a = succ b) : a = b := by

rw [← pred_succ a]
rw [← pred_succ b]
rw [h]
rfl
```

### Level 6
```lean
theorem succ_ne_zero (a : ℕ) : succ a ≠ 0 := by

intro h
rw [← is_zero_succ a]
rw [h]
rw [is_zero_zero]
trivial
```

### Level 7
```lean
theorem succ_ne_succ (m n : ℕ) (h : m ≠ n) : succ m ≠ succ n := by

contrapose! h
rw [← pred_succ m]
rw [← pred_succ n]
rw [h]
trivial
```

### Level 8
```lean
example : (20 : ℕ) + 20 = 40 := by

decide
```

### Level 9
```lean
example : (2 : ℕ) + 2 ≠ 5 := by

decide

```