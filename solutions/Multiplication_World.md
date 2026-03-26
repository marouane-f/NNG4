## Multiplication World

### Level 1
```lean
theorem mul_one (m : ℕ) : m * 1 = m := by

rw [one_eq_succ_zero]
rw [mul_succ]
rw [mul_zero]
rw [zero_add]
rfl
```

### Level 2
```lean
theorem zero_mul (m : ℕ) : 0 * m = 0 := by

induction m with d hd
rw [mul_zero]
rfl
rw [mul_succ]
rw [hd]
rw [add_zero]
rfl
```

### Level 3
```lean
theorem succ_mul (a b : ℕ) : succ a * b = a * b + b := by

induction b with d hd
rw [mul_zero]
rw [mul_zero]
rw [add_zero]
rfl
rw [mul_succ]
rw [hd]
rw [mul_succ]
rw [succ_eq_add_one]
rw [succ_eq_add_one]
rw [add_assoc]
rw [add_assoc]
nth_rewrite 1 [← add_assoc]
nth_rewrite 3 [add_comm]
nth_rewrite 5 [add_comm]
nth_rewrite 1 [← add_assoc]
nth_rewrite 1 [← add_assoc]
nth_rewrite 1 [← add_assoc]
rfl
```

### Level 4
```lean
theorem mul_comm (a b : ℕ) : a * b = b * a := by

induction a with d hd
rw [zero_mul]
rw [mul_zero]
rfl
rw [succ_mul]
rw [hd]
rw [mul_succ]
rfl
```

### Level 5
```lean
theorem one_mul (m : ℕ): 1 * m = m := by

rw [mul_comm]
rw [mul_one]
rfl
```

### Level 6
```lean
theorem two_mul (m : ℕ): 2 * m = m + m := by

rw [two_eq_succ_one]
rw [mul_comm]
rw [mul_succ]
rw [mul_one]
rfl
```

### Level 7
```lean
theorem mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c := by

induction c with d hd
rw [add_zero, mul_zero, add_zero]
rfl
rw [mul_succ]
rw [← add_assoc]
rw [← hd]
rw [← mul_succ]
rw [← add_succ]
rfl
```

### Level 8
```lean
theorem add_mul (a b c : ℕ) : (a + b) * c = a * c + b * c := by

rw [← mul_comm]
nth_rewrite 2 [← mul_comm]
nth_rewrite 3 [← mul_comm]
rw [mul_add]
rfl
```

### Level 9
```lean
theorem mul_assoc (a b c : ℕ) : (a * b) * c = a * (b * c) := by

induction a with d hd
rw [zero_mul]
rw [zero_mul]
rw [zero_mul]
rfl
rw [succ_mul]
rw [succ_mul]
rw [add_mul]
rw [← hd]
rfl
```