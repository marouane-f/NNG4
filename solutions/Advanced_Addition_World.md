## Advanced Addition World

### Level 1
```lean
theorem add_right_cancel (a b n : ℕ) : a + n = b + n → a = b := by

intro h
induction n with d hd
repeat rw [add_zero] at h
exact h
repeat rw [add_succ] at h
apply succ_inj at h
apply hd 
exact h
```

### Level 2
```lean
theorem add_left_cancel (a b n : ℕ) : n + a = n + b → a = b := by

intro h
rw [add_comm] at h
nth_rewrite 2 [add_comm] at h
apply add_right_cancel
exact h
```

### Level 3
```lean
theorem add_left_eq_self (x y : ℕ) : x + y = y → x = 0 := by

nth_rewrite 2 [← zero_add y]
intro h
apply add_right_cancel x 0 y
exact h
```

### Level 4
```lean
theorem add_right_eq_self (x y : ℕ) : x + y = x → y = 0 := by

intro h
rw [add_comm] at h
apply add_left_eq_self y x at h
exact h
```

### Level 5
```lean
theorem add_right_eq_zero (a b : ℕ) : a + b = 0 → a = 0 := by

cases b with d
rw [add_zero]
intro h
apply h
intro h
induction a with d hd
rfl
rw [succ_add] at h
symm at h
apply zero_ne_succ at h
cases h
```

### Level 6
```lean
theorem add_left_eq_zero (a b : ℕ) : a + b = 0 → b = 0 := by

intro h
rw [add_comm] at h
apply add_right_eq_zero at h
exact h
```