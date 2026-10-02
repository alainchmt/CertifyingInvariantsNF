# SkolemTableNFLean.sage
#
# Generator for the `UnitPowMod{num}.lean` files: the elementary-Skolem certificate
# (S1)(S2)(S3) for a fundamental unit `zeta1` of a cubic field, written as a chain of
# coordinate-vector multiplications modulo `p ^ 2`.
#
# What a generated file contains, in order:
#
#   * `kMu`, `mu`, `mu_one`      -- the `theta^2`-coordinate functional
#   * `TMod`, `hTMod`            -- the times table of O reduced mod `p ^ 2`
#   * `hbase`, `hC1 ... hCf`     -- coordinates of `zeta1 ^ r` mod `p ^ 2`, one
#                                   `coordMod_pow_succ` per step
#   * `not_dvd_mu_zeta1_pow`     -- (S3), for every `r < f` outside the surviving classes
#   * `zeta1_pow_{f}`            -- (S1), (S2) and, for each surviving class `r`, the
#                                   re-centering hypothesis `p is not a divisor of mu (zeta1^r * delta)`
#
# The last item is what lets a *multi-solution* Thue equation be finished off by
# `skolem_zpow_eq_zero_iff_mem` (ElementarySkolem): one surviving class per solution,
# each containing exactly one.
#
# Usage:
#   load("SkolemTableNFLean.sage")
#   generate_skolem_table("3_1_459_1", x^3+3*x-8, [1, x, (x^2+x)/2], [21,2,8], 11,
#                         [0,-1], import_module="IdealArithmetic.MordellExamples.MordellExample17....")
#
# `p` is chosen by `search_skolem_prime` below: the smallest prime whose table `f` is small
# and whose surviving classes are exactly the classes of the known solutions.
#
# Opus 5

import os

LEAN_ROOT = os.path.dirname(os.path.abspath("."))


def _struct_constants(T, basis):
    r"""Structure constants of `O` in the given integral basis: an `n x n x n` integer array
    `c` with `basis[i] * basis[j] = sum_k c[i][j][k] * basis[k]`."""
    n = len(basis)
    R = T.parent()
    K = NumberField(T, 'th')
    bK = [K(R(b)) for b in basis]
    M = matrix(QQ, [(list(b.list()) + [0] * n)[:n] for b in bK]).transpose()
    Minv = M.inverse()
    c = []
    for i in range(n):
        row = []
        for j in range(n):
            v = (list((bK[i] * bK[j]).list()) + [0] * n)[:n]
            coeffs = Minv * vector(QQ, v)
            assert all(t in ZZ for t in coeffs), "basis is not closed under multiplication"
            row.append([ZZ(t) for t in coeffs])
        c.append(row)
    return c, bK


def _coord_mul(c, u, v, m):
    r"""Multiply two coordinate vectors modulo `m` using the structure constants."""
    n = len(u)
    out = [0] * n
    for i in range(n):
        if u[i] == 0:
            continue
        for j in range(n):
            if v[j] == 0:
                continue
            uv = u[i] * v[j]
            for k in range(n):
                out[k] = (out[k] + uv * c[i][j][k]) % m
    return out


def skolem_data(T, basis, z, p, mu_index=2, fbound=500):
    r"""The certificate data at `p`: the order `f`, the chain of coordinate vectors mod
    `p^2`, the surviving classes, and `delta`'s coordinates mod `p`.  Returns `None` if
    `zeta1` is not `1` mod `p` for any `f <= fbound`."""
    c, _ = _struct_constants(T, basis)
    n = len(basis)
    m = p ^ 2
    one = [1] + [0] * (n - 1)
    zm = [ZZ(t) % m for t in z]
    chain = [one[:]]
    cur = one[:]
    f = None
    for r in range(1, fbound + 1):
        cur = _coord_mul(c, cur, zm, m)
        chain.append(cur[:])
        if all((cur[k] - one[k]) % p == 0 for k in range(n)):
            f = r
            break
    if f is None:
        return None
    surv = [r for r in range(f) if chain[r][mu_index] % p == 0]
    delta = [((chain[f][k] - one[k]) // p) % p for k in range(n)]
    # the re-centering quantity `mu (zeta1^r * delta)` mod p, for each surviving class
    W = {}
    for r in surv:
        cr = [t % p for t in chain[r]]
        W[r] = _coord_mul(c, cr, delta, p)[mu_index]
    return dict(f=f, chain=chain, surv=surv, delta=delta, W=W, c=c, m=m)


def search_skolem_prime(T, basis, z, sols, pmax=5000, fmax=500, mu_index=2):
    r"""Smallest table: scan primes and keep the one with the fewest residue classes whose
    surviving classes are exactly the classes of `sols` and for which every re-centering
    quantity `W` is nonzero (so each class holds exactly one solution)."""
    best = None
    for p in primes(5, pmax):
        d = skolem_data(T, basis, z, p, mu_index, fbound=fmax)
        if d is None:
            continue
        want = sorted(set(ZZ(s) % d['f'] for s in sols))
        if sorted(d['surv']) != want:
            continue
        if any(d['W'][r] % p == 0 for r in d['surv']):
            continue
        if best is None or d['f'] < best[1]['f']:
            best = (p, d)
            if d['f'] <= len(sols) + 2:
                break
    return best


def _vec(v):
    return "![" + ", ".join(str(t) for t in v) + "]"


def generate_skolem_table(num, T, basis, z, p, sols, import_module,
                          out_dir=None, lean_root=None, mu_index=2, poly_desc=None):
    r"""Write `UnitPowMod{num}.lean`."""
    d = skolem_data(T, basis, z, p, mu_index, fbound=10000)
    assert d is not None, "zeta1 is not 1 mod p for any small f"
    f, chain, surv, delta, W, c = d['f'], d['chain'], d['surv'], d['delta'], d['W'], d['c']
    m = p ^ 2
    want = sorted(set(ZZ(s) % f for s in sols))
    assert sorted(surv) == want, "surviving classes %s != classes of the solutions %s" % (surv, want)
    for r in surv:
        assert W[r] % p != 0, "class %s does not separate" % r
    n = len(basis)
    ns = "NF" + num
    if lean_root is None:
        lean_root = LEAN_ROOT
    if out_dir is None:
        out_dir = os.path.join(lean_root, "IdealArithmetic", ns)
    if poly_desc is None:
        poly_desc = str(T)

    L = []
    A = L.append
    A("import IdealArithmetic.MordellThueProject.SkolemTimesTable")
    A("import %s" % import_module)
    A("")
    A("/-!")
    A("# The Skolem certificate at `p = %d` for `K = ℚ(θ)`, `%s = 0`" % (p, poly_desc))
    A("")
    A("`mu` is the last coordinate for the integral basis recorded in `RI%s`.  Iterated" % num)
    A("multiplication of coordinate vectors modulo `%d ^ 2 = %d` verifies" % (p, m))
    A("")
    A("* `hC1 … hC%d` : the coordinates of `zeta1 ^ r` mod `%d`, one multiplication per step;" % (f, m))
    A("* `not_dvd_mu_zeta1_pow` : **(S3)** -- `%d ∤ mu (zeta1 ^ r)` for every `r < %d` outside" % (p, f))
    A("  the surviving class%s %s;" % ("es" if len(surv) > 1 else "", ", ".join("`%d`" % r for r in surv)))
    A("* `zeta1_pow_%d` : **(S1)**, **(S2)** and the re-centering hypothes%s, i.e."
      % (f, "es" if len(surv) > 1 else "is"))
    A("  `%d ∤ mu (zeta1 ^ r * δ)` for each surviving `r`, which is what makes each" % p)
    A("  surviving class contain exactly one solution.")
    A("")
    A("Generated by `SkolemTableNFLean.sage`.")
    A("-/")
    A("")
    A("namespace %s" % ns)
    A("")
    A("set_option linter.all false")
    A("")
    A("open Module")
    A("")
    A("noncomputable section")
    A("")
    A("abbrev pS : ℕ := %d" % p)
    A("abbrev mS : ℕ := pS ^ 2")
    A("")
    A("/-- The weights picking out the last coordinate of the integral basis. -/")
    A("def kMu : Fin %d → ℤ := %s" % (n, _vec([1 if i == mu_index else 0 for i in range(n)])))
    A("")
    A("/-- `mu`: the last coordinate. -/")
    A("abbrev mu : O →ₗ[ℤ] ℤ := muOfBasis timesTableO.basis kMu")
    A("")
    A("lemma mu_one : mu 1 = 0 := by")
    A("  have h : mu (B 0) = kMu 0 := muOfBasis_basis (b := timesTableO.basis) kMu 0")
    A("  rwa [B_one] at h")
    A("")
    A("/-- The times table of `O`, reduced modulo `%d`. -/" % m)
    A("def TMod : Fin %d → Fin %d → List (ZMod mS) :=" % (n, n))
    rows = []
    for i in range(n):
        rows.append(" ![" + ", ".join("[" + ", ".join(str(ZZ(t) % m) for t in c[i][j]) + "]"
                                      for j in range(n)) + "]")
    A(" ![" + ",\n".join(rows) + "]")
    A("")
    A("lemma hTMod : ∀ i j, List.map (algebraMap ℤ (ZMod mS)) (Table i j) = TMod i j := by decide")
    A("")
    A("/-! ### The coordinate vector of `zeta1` modulo `%d` -/" % m)
    A("")
    A("lemma hbase : coordMod timesTableO.basis mS zeta1 = %s := by" % _vec(chain[1]))
    A("  have hv : timesTableO.basis.equivFun zeta1 = %s := by" % _vec(z))
    A("    rw [zeta1]; exact B.equivFun.apply_symm_apply _")
    A("  funext i")
    A("  simp only [coordMod, Function.comp_apply, hv]")
    A("  fin_cases i <;> decide")
    A("")
    A("/-! ### The chain `zeta1 ^ 1, …, zeta1 ^ %d`, one multiplication per step -/" % f)
    A("")
    A("lemma hC0 : coordMod timesTableO.basis mS (zeta1 ^ 0) = %s := by" % _vec(chain[0]))
    A("  rw [pow_zero, coordMod_one (b := timesTableO.basis) (i₀ := 0) B_one]")
    A("  funext i; fin_cases i <;> decide")
    A("")
    A("lemma hC1 : coordMod timesTableO.basis mS (zeta1 ^ 1) = %s := by" % _vec(chain[1]))
    A("  rw [pow_one]; exact hbase")
    A("")
    for r in range(2, f + 1):
        A("lemma hC%d : coordMod timesTableO.basis mS (zeta1 ^ %d) = %s :=" % (r, r, _vec(chain[r])))
        A("  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC%d (by decide)" % (r - 1))
        A("")
    A("/-! ### `(S3)`: the sieve -/")
    A("")
    dead = [r for r in range(1, f) if r not in surv]
    for r in dead:
        A("lemma hS%d : ¬ ((pS : ℤ) ∣ mu (zeta1 ^ %d)) :=" % (r, r))
        A("  (not_dvd_muOfBasis_iff (by norm_num) hC%d kMu).mpr (by decide)" % r)
        A("")
    guard = " ".join("→ r ≠ %d" % r for r in surv)
    A("/-- **`(S3)`.**  `%d ∤ mu (zeta1 ^ r)` for every `r < %d` outside the surviving" % (p, f))
    A("class%s %s. -/" % ("es" if len(surv) > 1 else "", ", ".join(str(r) for r in surv)))
    A("theorem not_dvd_mu_zeta1_pow : ∀ r : ℕ, r < %d %s → ¬ ((pS : ℤ) ∣ mu (zeta1 ^ r)) := by"
      % (f, guard))
    A("  intro r hr " + " ".join("h%d" % r for r in surv))
    A("  interval_cases r")
    for r in range(f):
        if r in surv:
            A("  · exact absurd rfl h%d" % r)
        else:
            A("  · exact hS%d" % r)
    A("")
    A("/-! ### `(S1)`, `(S2)` and the re-centering data -/")
    A("")
    A("/-- The coordinates of `δ = (zeta1 ^ %d - 1) / %d` modulo `%d`. -/" % (f, p, p))
    A("def eDelta : Fin %d → ZMod pS := %s" % (n, _vec(delta)))
    A("")
    A("/-- The times table of `O`, reduced modulo `%d`. -/" % p)
    A("def TModP : Fin %d → Fin %d → List (ZMod pS) :=" % (n, n))
    rows = []
    for i in range(n):
        rows.append(" ![" + ", ".join("[" + ", ".join(str(ZZ(t) % p) for t in c[i][j]) + "]"
                                      for j in range(n)) + "]")
    A(" ![" + ",\n".join(rows) + "]")
    A("")
    A("lemma hTModP : ∀ i j, List.map (algebraMap ℤ (ZMod pS)) (Table i j) = TModP i j := by decide")
    A("")
    for r in surv:
        A("lemma hP%d : coordMod timesTableO.basis pS (zeta1 ^ %d) = %s := by"
          % (r, r, _vec([ZZ(t) % p for t in chain[r]])))
        A("  rw [coordMod_castHom (by norm_num : pS ∣ mS), hC%d]" % r)
        A("  funext i; fin_cases i <;> decide")
        A("")
    A("/-- **`(S1)`, `(S2)` and re-centering.**  `zeta1 ^ %d = %d δ + 1` with `%d ∤ mu δ`,"
      % (f, p, p))
    A("and `%d ∤ mu (zeta1 ^ r * δ)` for each surviving class `r`, so no such class holds two" % p)
    A("solutions. -/")
    concl = ["zeta1 ^ %d = pS * δ + 1" % f, "¬ ((pS : ℤ) ∣ mu δ)"]
    for r in surv:
        concl.append("¬ ((pS : ℤ) ∣ mu (zeta1 ^ %d * δ))" % r)
    A("theorem zeta1_pow_%d : ∃ δ : O, %s := by" % (f, " ∧ ".join(concl)))
    A("  obtain ⟨δ, hδ, hc⟩ := exists_delta_of_coordMod (b := timesTableO.basis) (by norm_num)")
    A("    (i₀ := 0) B_one hC%d eDelta (by decide)" % f)
    A("  refine ⟨δ, hδ, (not_dvd_muOfBasis_iff dvd_rfl hc kMu).mpr (by decide), ?_⟩" if len(surv) == 0
      else "  refine ⟨δ, hδ, (not_dvd_muOfBasis_iff dvd_rfl hc kMu).mpr (by decide), %s⟩"
      % ", ".join("?_" for _ in surv))
    for r in surv:
        prod = _coord_mul(c, [ZZ(t) % p for t in chain[r]], delta, p)
        A("  · exact (not_dvd_muOfBasis_iff dvd_rfl (coordMod_mul timesTableT_eq_Table")
        A("      hTModP hP%d hc (c := %s) (by decide)) kMu).mpr (by decide)" % (r, _vec(prod)))
    A("")
    A("end")
    A("")
    A("end %s" % ns)
    A("")

    if not os.path.isdir(out_dir):
        os.makedirs(out_dir)
    path = os.path.join(out_dir, "UnitPowMod%s.lean" % num)
    with open(path, "w") as fh:
        fh.write("\n".join(L))
    print("wrote %s   (p = %d, f = %d, surviving classes %s)" % (path, p, f, surv))
    return d
