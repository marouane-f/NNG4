## Advanced Multiplication World

### Level 1
```lean
theorem mul_le_mul_right (a b t : ℕ) (h : a ≤ b) : a * t ≤ b * t := by

cases h with d hd
use d * t
rw [hd, add_mul]
rfl
```

### Level 2
```lean
theorem mul_left_ne_zero (a b : ℕ) (h : a * b ≠ 0) : b ≠ 0 := by

contrapose! h
rw [h]
apply mul_zero a
```

### Level 3
```lean
theorem eq_succ_of_ne_zero (a : ℕ) (ha : a ≠ 0) : ∃ n, a = succ n := by

cases a with d
tauto
contrapose! ha
tauto
```

### Level 4
```lean
theorem one_le_of_ne_zero (a : ℕ) (ha : a ≠ 0) : 1 ≤ a := by

apply eq_succ_of_ne_zero a at ha
cases ha with n hn
rw [succ_eq_add_one] at hn
use n
rw [hn]
simp_add
```

### Level 5
```lean
theorem le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by

cases b with n
rw [mul_zero] at h
tauto
rw [succ_eq_add_one]
rw [mul_add]
rw [mul_one]
use a * n
simp_add
```

### Level 6
```lean
theorem mul_right_eq_one (x y : ℕ) (h : x * y = 1) : x = 1 := by

have h2 : x * y ≠ 0
rw [h]
tauto
rw [mul_comm] at h2
apply le_mul_right y x at h2
rw [mul_comm] at h
rw [h] at h2
apply le_one at h2
cases h2
rw [h_1] at h
rw [zero_mul] at h
tauto
rw [h_1] at h
rw [one_mul] at h
exact h
```

### Level 7
```lean
theorem mul_ne_zero (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by

cases a
tauto
cases b
tauto
rw [succ_eq_add_one]
rw [succ_eq_add_one]
rw [mul_add]
rw [mul_one]
rw [add_mul]
rw [one_mul]
rw [← succ_eq_add_one]
rw [add_succ]
symm
apply zero_ne_succ
```

### Level 8
```lean
theorem mul_eq_zero (a b : ℕ) (h : a * b = 0) : a = 0 ∨ b = 0 := by

have h2 := mul_ne_zero a b
tauto
```

### Level 9
```lean
theorem mul_left_cancel (a b c : ℕ) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by

induction b with d hd generalizing c
rw [mul_zero] at h
have h2 := mul_eq_zero a c
tauto
cases c with n
rw [mul_zero] at h
apply mul_eq_zero at h
cases h
tauto

-- a) Case split on c
exact h_1
rw [mul_succ, mul_succ] at h
apply add_right_cancel at h
apply hd at h
rw [h]
rfl

-- b) Alternatively, by first proving that c ≠ 0
have result : a * c ≠ 0
apply eq_succ_of_ne_zero a at ha
cases ha
nth_rewrite 1 [h_1] at h
contrapose! h
rw [h]
rw [succ_eq_add_one]
rw [succ_eq_add_one]
rw [mul_add]
rw [add_mul]
rw [mul_one]
rw [one_mul]
rw [← succ_eq_add_one]
symm
rw [add_comm]
rw [succ_add]
apply zero_ne_succ
apply mul_left_ne_zero a c at result
apply eq_succ_of_ne_zero c at result
cases result
rw [h_1] at h
rw [succ_eq_add_one] at h
rw [succ_eq_add_one] at h
repeat rw [mul_add] at h
repeat rw [mul_add] at h
rw [mul_one] at h
apply add_right_cancel at h
apply hd at h
rw [h]
rw [h_1]
rfl

```

### Level 10
```lean
theorem mul_right_eq_self (a b : ℕ) (ha : a ≠ 0) (h : a * b = a) : b = 1 := by

nth_rewrite 2 [← mul_one a] at h
apply mul_left_cancel a b 1 at h
exact h
exact ha
```