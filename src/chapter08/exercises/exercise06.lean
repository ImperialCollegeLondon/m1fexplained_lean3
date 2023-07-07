import tactic

namespace chapter08.exercise06

-- l for Lucas. For convenience set l₀ = 2.
def l : ℕ → ℕ
| 0 := 2
| 1 := 1
| (n+2) := l n + l (n + 1)

end chapter08.exercise06

