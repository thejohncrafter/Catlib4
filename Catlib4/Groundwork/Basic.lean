
theorem Prod.ext' : {p q : α × β} → p.1 = q.1 → p.2 = q.2 → p = q
  | (a, b), (c, d) => by simp_all
