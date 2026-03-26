## Power World

### Level 1
```lean
theorem zero_pow_zero : (0 : ℕ) ^ 0 = 1 := by

rw [pow_zero]
rfl
```

### Level 2
```lean
theorem zero_pow_succ (m : ℕ) : (0 : ℕ) ^ (succ m) = 0 := by

rw [pow_succ]
rw [mul_zero]
rfl
```

### Level 3
```lean
theorem pow_one (a : ℕ) : a ^ 1 = a := by

rw [one_eq_succ_zero]
rw [pow_succ]
rw [pow_zero]
rw [mul_comm]
rw [mul_one]
rfl
```

### Level 4
```lean
theorem one_pow (m : ℕ) : (1 : ℕ) ^ m = 1 := by

induction m with d hd
rw [pow_zero]
rfl
rw [pow_succ]
rw [mul_one]
rw [hd]
rfl
```

### Level 5
```lean
theorem pow_two (a : ℕ) : a ^ 2 = a * a := by

rw [two_eq_succ_one]
rw [pow_succ]
rw [pow_one]
rfl
```

### Level 6
```lean
theorem pow_add (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by

induction n with d hd
rw [add_zero, pow_zero]
rw [mul_one]
rfl
rw [pow_succ]
rw [← mul_assoc]
rw [← hd]
rw [add_succ]
rw [← pow_succ]
rfl
```

### Level 7
```lean
theorem mul_pow (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by

induction n with d hd
rw [pow_zero]
rw [pow_zero]
rw [pow_zero]
rw [one_mul]
rfl
repeat rw [pow_succ]
rw [hd]
nth_rewrite 1 [mul_assoc]
nth_rewrite 1 [mul_assoc]
nth_rewrite 2 [← mul_assoc]
nth_rewrite 3 [← mul_assoc]
nth_rewrite 3 [← mul_comm]
rfl
```

### Level 8
```lean
theorem pow_pow (a m n : ℕ) : (a ^ m) ^ n = a ^ (m * n) := by

induction n with d hd
repeat rw [pow_zero]
rw [mul_zero]
rw [pow_zero]
rfl
rw [pow_succ]
rw [mul_succ]
rw [hd]
rw [pow_add]
rfl
```

### Level 9
```lean
theorem add_sq (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by

nth_rewrite 1 [pow_two]
nth_rewrite 1 [add_mul]
nth_rewrite 1 [mul_add]
nth_rewrite 1 [mul_add]
nth_rewrite 1 [← pow_two]
nth_rewrite 1 [← pow_two]
nth_rewrite 2 [← mul_comm]
nth_rewrite 1 [add_assoc]
nth_rewrite 2 [← add_assoc]
rw [← two_mul]
nth_rewrite 2 [add_comm]
nth_rewrite 1 [← add_assoc]
nth_rewrite 1 [← mul_assoc]
rfl
```

### Level 10
```lean
example (a b c n : ℕ) : (a + 1) ^ (n + 3) + (b + 1) ^ (n + 3) ≠ (c + 1) ^ (n + 3) := by
sorry
```