# nyasfibonacci

An attempt to calculate fibonacci number as fast as possible.

---

The implementation details is in my [zhihu page](https://zhuanlan.zhihu.com/p/21525013391).

---

1. `recursion` : based on `fibonacci(n) = fibonacci(n-1) + fibonacci(n-2)`,

2. `iteration` : same as above,

3. `matrix_pow` : based on `M = [0, 1; 1, 1]`, `M^n = (M^2⁰)^n₀ * (M^2¹)^n₁ * (M^2²)^n₂ * (M^2³)^n₃ * ...`, where
`n = n₀*2⁰ + n₁*2¹ + n₂*2² + n₃*2³ + ...`, and the `fibonacci(n)` is the top right element in `M^n`,

4. `small_matrix` : based on `M^n = [fibonacci(n-1), fibonacci(n); fibonacci(n), fibonacci(n-1)+fibonacci(n)]` to simplify
the matrix to `(fibonacci(n-1), fibonacci(n))`,

5. `rev_pow` : based on `n = ((((...)*2 + n₃)*2 + n₂)*2 + n₁)*2 + n₀` to simplify to
`M^2 = ((((...)^2 * M^n₃)^2 * M^n₂)^2 * M^n₁)^2 * M^n₀`,

6. `karatsuba` : based on when `a = a₀ + a₁*M` and `b = b₀ + b₁*M` then `a*b = z₀ + z₁*M + z₂*M²`, where
`z₀ = a₀*b₀`, `z₂ = a₁*b₁` and `z₁ = (a₀ + a₁)*(b₀ + b₁) - z₀ - z₂`,
