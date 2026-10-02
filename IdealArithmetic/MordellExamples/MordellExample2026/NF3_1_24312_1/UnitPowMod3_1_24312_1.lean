import IdealArithmetic.MordellThueProject.SkolemTimesTable
import IdealArithmetic.MordellExamples.MordellExample2026.NF3_1_24312_1.UnitsData3_1_24312_1

/-!
# The Skolem certificate at `p = 83` for `K = ℚ(θ)`, `θ³ + 3θ - 90 = 0`

`mu` is the `θ²/3`-coordinate, i.e. the third coordinate for the integral basis
`1, θ, θ²/3` recorded in `RI3_1_24312_1`.  This file verifies, by iterated multiplication of
coordinate vectors modulo `83 ^ 2 = 6889`, the certificate `(S1)(S2)(S3)` of the elementary
Skolem method:

* `hC1 … hC82` : the coordinate vectors of `zeta1 ^ r` mod `6889`, one multiplication per
  step (`coordMod_pow_succ`);
* `zeta1_pow_82` : `(S1)` and `(S2)` -- `zeta1 ^ 82 = 83 * δ + 1` with `83 ∤ mu δ`
  (indeed `mu δ ≡ 46 mod 83`), read off from `hC82` by `exists_delta_not_dvd_mu`;
* `not_dvd_mu_zeta1_pow` : `(S3)` -- `83 ∤ mu (zeta1 ^ r)` for every `0 < r < 82`.

Working modulo `83 ^ 2` rather than `83` costs nothing and does both jobs at once: the
third coordinate reduced mod `83` gives the sieve table, and the whole vector mod `83 ^ 2`
gives `δ`.

Opus 5
-/

set_option linter.all false

open Module

abbrev p83 : ℕ := 83
abbrev m83 : ℕ := p83 ^ 2

/-- The weights picking out the `θ²/3`-coordinate of the integral basis `1, θ, θ²/3`. -/
def kMu : Fin 3 → ℤ := ![0, 0, 1]

/-- `mu`: the `θ²/3`-coordinate. -/
noncomputable abbrev mu : O →ₗ[ℤ] ℤ := muOfBasis timesTableO.basis kMu

lemma mu_one : mu 1 = 0 := by
  have h : mu (B 0) = kMu 0 := muOfBasis_basis (b := timesTableO.basis) kMu 0
  rwa [B_one] at h

/-- The times table of `O`, reduced modulo `83 ^ 2`. -/
def TMod : Fin 3 → Fin 3 → List (ZMod m83) :=
 ![ ![[1, 0, 0], [0, 1, 0], [0, 0, 1]],
 ![[0, 1, 0], [0, 0, 3], [30, 6888, 0]],
 ![[0, 0, 1], [30, 6888, 0], [0, 10, 6888]]]

lemma hTMod : ∀ i j, List.map (algebraMap ℤ (ZMod m83)) (Table i j) = TMod i j := by decide

/-! ### The coordinate vector of `zeta1` modulo `83 ^ 2` -/

lemma hbase : coordMod timesTableO.basis m83 zeta1 = ![5531, 2925, 783] := by
  have hv : timesTableO.basis.equivFun zeta1 =
      ![178361260665498855294599509801, 35938665342336427911821503300,
        25318107466978248199411982702] := by
    rw [zeta1]; exact B.equivFun.apply_symm_apply _
  funext i
  simp only [coordMod, Function.comp_apply, hv]
  fin_cases i <;> decide

/-! ### The chain `zeta1 ^ 1, …, zeta1 ^ 82`, one multiplication per step -/

lemma hC1 : coordMod timesTableO.basis m83 (zeta1 ^ 1) = ![5531, 2925, 783] := by
  rw [pow_one]; exact hbase

lemma hC2 : coordMod timesTableO.basis m83 (zeta1 ^ 2) = ![6418, 5921, 566] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC1 (by decide)

lemma hC3 : coordMod timesTableO.basis m83 (zeta1 ^ 3) = ![4909, 5876, 3808] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC2 (by decide)

lemma hC4 : coordMod timesTableO.basis m83 (zeta1 ^ 4) = ![2421, 3108, 1068] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC3 (by decide)

lemma hC5 : coordMod timesTableO.basis m83 (zeta1 ^ 5) = ![1566, 2979, 877] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC4 (by decide)

lemma hC6 : coordMod timesTableO.basis m83 (zeta1 ^ 6) = ![52, 3489, 6835] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC5 (by decide)

lemma hC7 : coordMod timesTableO.basis m83 (zeta1 ^ 7) = ![4472, 2070, 6031] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC6 (by decide)

lemma hC8 : coordMod timesTableO.basis m83 (zeta1 ^ 8) = ![5241, 3724, 4425] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC7 (by decide)

lemma hC9 : coordMod timesTableO.basis m83 (zeta1 ^ 9) = ![1451, 3664, 6771] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC8 (by decide)

lemma hC10 : coordMod timesTableO.basis m83 (zeta1 ^ 10) = ![2546, 2384, 4719] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC9 (by decide)

lemma hC11 : coordMod timesTableO.basis m83 (zeta1 ^ 11) = ![1638, 301, 3088] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC10 (by decide)

lemma hC12 : coordMod timesTableO.basis m83 (zeta1 ^ 12) = ![3193, 4149, 6020] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC11 (by decide)

lemma hC13 : coordMod timesTableO.basis m83 (zeta1 ^ 13) = ![4894, 3688, 5910] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC12 (by decide)

lemma hC14 : coordMod timesTableO.basis m83 (zeta1 ^ 14) = ![2358, 4921, 1179] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC13 (by decide)

lemma hC15 : coordMod timesTableO.basis m83 (zeta1 ^ 15) = ![3228, 1805, 5609] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC14 (by decide)

lemma hC16 : coordMod timesTableO.basis m83 (zeta1 ^ 16) = ![580, 1673, 5872] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC15 (by decide)

lemma hC17 : coordMod timesTableO.basis m83 (zeta1 ^ 17) = ![6865, 1444, 55] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC16 (by decide)

lemma hC18 : coordMod timesTableO.basis m83 (zeta1 ^ 18) = ![221, 1351, 3462] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC17 (by decide)

lemma hC19 : coordMod timesTableO.basis m83 (zeta1 ^ 19) = ![6632, 6362, 296] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC18 (by decide)

lemma hC20 : coordMod timesTableO.basis m83 (zeta1 ^ 20) = ![440, 2877, 3585] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC19 (by decide)

lemma hC21 : coordMod timesTableO.basis m83 (zeta1 ^ 21) = ![5917, 1563, 3310] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC20 (by decide)

lemma hC22 : coordMod timesTableO.basis m83 (zeta1 ^ 22) = ![6048, 1905, 5000] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC21 (by decide)

lemma hC23 : coordMod timesTableO.basis m83 (zeta1 ^ 23) = ![6267, 6180, 119] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC22 (by decide)

lemma hC24 : coordMod timesTableO.basis m83 (zeta1 ^ 24) = ![5936, 6754, 1499] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC23 (by decide)

lemma hC25 : coordMod timesTableO.basis m83 (zeta1 ^ 25) = ![2405, 4249, 5900] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC24 (by decide)

lemma hC26 : coordMod timesTableO.basis m83 (zeta1 ^ 26) = ![3446, 3027, 6651] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC25 (by decide)

lemma hC27 : coordMod timesTableO.basis m83 (zeta1 ^ 27) = ![3772, 6425, 2332] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC26 (by decide)

lemma hC28 : coordMod timesTableO.basis m83 (zeta1 ^ 28) = ![4222, 1050, 6496] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC27 (by decide)

lemma hC29 : coordMod timesTableO.basis m83 (zeta1 ^ 29) = ![636, 3281, 3218] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC28 (by decide)

lemma hC30 : coordMod timesTableO.basis m83 (zeta1 ^ 30) = ![274, 4020, 2886] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC29 (by decide)

lemma hC31 : coordMod timesTableO.basis m83 (zeta1 ^ 31) = ![2162, 5691, 5310] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC30 (by decide)

lemma hC32 : coordMod timesTableO.basis m83 (zeta1 ^ 32) = ![470, 199, 3345] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC31 (by decide)

lemma hC33 : coordMod timesTableO.basis m83 (zeta1 ^ 33) = ![3423, 2525, 2227] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC32 (by decide)

lemma hC34 : coordMod timesTableO.basis m83 (zeta1 ^ 34) = ![5477, 1879, 1420] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC33 (by decide)

lemma hC35 : coordMod timesTableO.basis m83 (zeta1 ^ 35) = ![5898, 3858, 4210] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC34 (by decide)

lemma hC36 : coordMod timesTableO.basis m83 (zeta1 ^ 36) = ![34, 5244, 1110] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC35 (by decide)

lemma hC37 : coordMod timesTableO.basis m83 (zeta1 ^ 37) = ![331, 21, 3730] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC36 (by decide)

lemma hC38 : coordMod timesTableO.basis m83 (zeta1 ^ 38) = ![6679, 5443, 973] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC37 (by decide)

lemma hC39 : coordMod timesTableO.basis m83 (zeta1 ^ 39) = ![4334, 84, 5968] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC38 (by decide)

lemma hC40 : coordMod timesTableO.basis m83 (zeta1 ^ 40) = ![4538, 2139, 5718] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC39 (by decide)

lemma hC41 : coordMod timesTableO.basis m83 (zeta1 ^ 41) = ![869, 1804, 2134] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC40 (by decide)

lemma hC42 : coordMod timesTableO.basis m83 (zeta1 ^ 42) = ![1340, 5028, 2996] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC41 (by decide)

lemma hC43 : coordMod timesTableO.basis m83 (zeta1 ^ 43) = ![2662, 3361, 4859] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC42 (by decide)

lemma hC44 : coordMod timesTableO.basis m83 (zeta1 ^ 44) = ![52, 2339, 4105] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC43 (by decide)

lemma hC45 : coordMod timesTableO.basis m83 (zeta1 ^ 45) = ![3327, 6413, 3335] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC44 (by decide)

lemma hC46 : coordMod timesTableO.basis m83 (zeta1 ^ 46) = ![2255, 551, 2491] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC45 (by decide)

lemma hC47 : coordMod timesTableO.basis m83 (zeta1 ^ 47) = ![6043, 5588, 6772] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC46 (by decide)

lemma hC48 : coordMod timesTableO.basis m83 (zeta1 ^ 48) = ![2268, 5677, 217] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC47 (by decide)

lemma hC49 : coordMod timesTableO.basis m83 (zeta1 ^ 49) = ![2350, 1011, 3653] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC48 (by decide)

lemma hC50 : coordMod timesTableO.basis m83 (zeta1 ^ 50) = ![5894, 3688, 4011] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC49 (by decide)

lemma hC51 : coordMod timesTableO.basis m83 (zeta1 ^ 51) = ![2262, 1429, 82] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC50 (by decide)

lemma hC52 : coordMod timesTableO.basis m83 (zeta1 ^ 52) = ![1195, 4785, 5720] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC51 (by decide)

lemma hC53 : coordMod timesTableO.basis m83 (zeta1 ^ 53) = ![6069, 6502, 823] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC52 (by decide)

lemma hC54 : coordMod timesTableO.basis m83 (zeta1 ^ 54) = ![1255, 620, 510] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC53 (by decide)

lemma hC55 : coordMod timesTableO.basis m83 (zeta1 ^ 55) = ![6192, 2038, 6058] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC54 (by decide)

lemma hC56 : coordMod timesTableO.basis m83 (zeta1 ^ 56) = ![3507, 31, 6784] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC55 (by decide)

lemma hC57 : coordMod timesTableO.basis m83 (zeta1 ^ 57) = ![6370, 4423, 4981] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC56 (by decide)

lemma hC58 : coordMod timesTableO.basis m83 (zeta1 ^ 58) = ![1752, 3648, 6013] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC57 (by decide)

lemma hC59 : coordMod timesTableO.basis m83 (zeta1 ^ 59) = ![2089, 2898, 630] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC58 (by decide)

lemma hC60 : coordMod timesTableO.basis m83 (zeta1 ^ 60) = ![3492, 6031, 170] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC59 (by decide)

lemma hC61 : coordMod timesTableO.basis m83 (zeta1 ^ 61) = ![3105, 2498, 1177] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC60 (by decide)

lemma hC62 : coordMod timesTableO.basis m83 (zeta1 ^ 62) = ![5747, 272, 6856] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC61 (by decide)

lemma hC63 : coordMod timesTableO.basis m83 (zeta1 ^ 63) = ![1618, 610, 6353] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC62 (by decide)

lemma hC64 : coordMod timesTableO.basis m83 (zeta1 ^ 64) = ![4219, 5325, 3317] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC63 (by decide)

lemma hC65 : coordMod timesTableO.basis m83 (zeta1 ^ 65) = ![2534, 913, 3296] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC64 (by decide)

lemma hC66 : coordMod timesTableO.basis m83 (zeta1 ^ 66) = ![465, 6415, 4247] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC65 (by decide)

lemma hC67 : coordMod timesTableO.basis m83 (zeta1 ^ 67) = ![699, 4342, 1237] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC66 (by decide)

lemma hC68 : coordMod timesTableO.basis m83 (zeta1 ^ 68) = ![152, 746, 4925] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC67 (by decide)

lemma hC69 : coordMod timesTableO.basis m83 (zeta1 ^ 69) = ![6180, 2168, 6137] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC68 (by decide)

lemma hC70 : coordMod timesTableO.basis m83 (zeta1 ^ 70) = ![2925, 5206, 4539] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC69 (by decide)

lemma hC71 : coordMod timesTableO.basis m83 (zeta1 ^ 71) = ![1041, 5279, 309] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC70 (by decide)

lemma hC72 : coordMod timesTableO.basis m83 (zeta1 ^ 72) = ![6812, 2562, 3565] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC71 (by decide)

lemma hC73 : coordMod timesTableO.basis m83 (zeta1 ^ 73) = ![6456, 2557, 4800] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC72 (by decide)

lemma hC74 : coordMod timesTableO.basis m83 (zeta1 ^ 74) = ![839, 667, 312] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC73 (by decide)

lemma hC75 : coordMod timesTableO.basis m83 (zeta1 ^ 75) = ![681, 569, 6887] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC74 (by decide)

lemma hC76 : coordMod timesTableO.basis m83 (zeta1 ^ 76) = ![3092, 6096, 5502] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC75 (by decide)

lemma hC77 : coordMod timesTableO.basis m83 (zeta1 ^ 77) = ![2353, 5059, 2720] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC76 (by decide)

lemma hC78 : coordMod timesTableO.basis m83 (zeta1 ^ 78) = ![5488, 3099, 730] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC77 (by decide)

lemma hC79 : coordMod timesTableO.basis m83 (zeta1 ^ 79) = ![4219, 5437, 2083] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC78 (by decide)

lemma hC80 : coordMod timesTableO.basis m83 (zeta1 ^ 80) = ![6507, 4897, 4476] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC79 (by decide)

lemma hC81 : coordMod timesTableO.basis m83 (zeta1 ^ 81) = ![6532, 5675, 1086] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC80 (by decide)

lemma hC82 : coordMod timesTableO.basis m83 (zeta1 ^ 82) = ![250, 6557, 3818] :=
  coordMod_pow_succ timesTableT_eq_Table hTMod hbase hC81 (by decide)


/-! ### `(S1)` and `(S2)`: `zeta1 ^ 82 = 1 + 83 δ`, and `mu δ ≡ 46 (mod 83)` -/

/-- The coordinates of `δ = (zeta1 ^ 82 - 1) / 83` modulo `83`; the last entry is `mu δ`. -/
def eDelta : Fin 3 → ZMod p83 := ![3, 79, 46]

theorem zeta1_pow_82 : ∃ δ : O, zeta1 ^ 82 = 83 * δ + 1 ∧ ¬ ((83 : ℤ) ∣ mu δ) :=
  exists_delta_not_dvd_mu (by norm_num) (i₀ := 0) B_one kMu hC82 eDelta (by decide) (by decide)

/-! ### `(S3)`: the sieve table -/

lemma hS1 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 1)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC1 kMu).mpr (by decide)

lemma hS2 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 2)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC2 kMu).mpr (by decide)

lemma hS3 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 3)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC3 kMu).mpr (by decide)

lemma hS4 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 4)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC4 kMu).mpr (by decide)

lemma hS5 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 5)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC5 kMu).mpr (by decide)

lemma hS6 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 6)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC6 kMu).mpr (by decide)

lemma hS7 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 7)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC7 kMu).mpr (by decide)

lemma hS8 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 8)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC8 kMu).mpr (by decide)

lemma hS9 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 9)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC9 kMu).mpr (by decide)

lemma hS10 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 10)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC10 kMu).mpr (by decide)

lemma hS11 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 11)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC11 kMu).mpr (by decide)

lemma hS12 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 12)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC12 kMu).mpr (by decide)

lemma hS13 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 13)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC13 kMu).mpr (by decide)

lemma hS14 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 14)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC14 kMu).mpr (by decide)

lemma hS15 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 15)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC15 kMu).mpr (by decide)

lemma hS16 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 16)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC16 kMu).mpr (by decide)

lemma hS17 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 17)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC17 kMu).mpr (by decide)

lemma hS18 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 18)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC18 kMu).mpr (by decide)

lemma hS19 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 19)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC19 kMu).mpr (by decide)

lemma hS20 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 20)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC20 kMu).mpr (by decide)

lemma hS21 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 21)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC21 kMu).mpr (by decide)

lemma hS22 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 22)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC22 kMu).mpr (by decide)

lemma hS23 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 23)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC23 kMu).mpr (by decide)

lemma hS24 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 24)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC24 kMu).mpr (by decide)

lemma hS25 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 25)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC25 kMu).mpr (by decide)

lemma hS26 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 26)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC26 kMu).mpr (by decide)

lemma hS27 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 27)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC27 kMu).mpr (by decide)

lemma hS28 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 28)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC28 kMu).mpr (by decide)

lemma hS29 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 29)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC29 kMu).mpr (by decide)

lemma hS30 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 30)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC30 kMu).mpr (by decide)

lemma hS31 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 31)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC31 kMu).mpr (by decide)

lemma hS32 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 32)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC32 kMu).mpr (by decide)

lemma hS33 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 33)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC33 kMu).mpr (by decide)

lemma hS34 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 34)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC34 kMu).mpr (by decide)

lemma hS35 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 35)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC35 kMu).mpr (by decide)

lemma hS36 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 36)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC36 kMu).mpr (by decide)

lemma hS37 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 37)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC37 kMu).mpr (by decide)

lemma hS38 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 38)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC38 kMu).mpr (by decide)

lemma hS39 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 39)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC39 kMu).mpr (by decide)

lemma hS40 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 40)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC40 kMu).mpr (by decide)

lemma hS41 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 41)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC41 kMu).mpr (by decide)

lemma hS42 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 42)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC42 kMu).mpr (by decide)

lemma hS43 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 43)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC43 kMu).mpr (by decide)

lemma hS44 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 44)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC44 kMu).mpr (by decide)

lemma hS45 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 45)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC45 kMu).mpr (by decide)

lemma hS46 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 46)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC46 kMu).mpr (by decide)

lemma hS47 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 47)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC47 kMu).mpr (by decide)

lemma hS48 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 48)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC48 kMu).mpr (by decide)

lemma hS49 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 49)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC49 kMu).mpr (by decide)

lemma hS50 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 50)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC50 kMu).mpr (by decide)

lemma hS51 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 51)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC51 kMu).mpr (by decide)

lemma hS52 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 52)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC52 kMu).mpr (by decide)

lemma hS53 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 53)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC53 kMu).mpr (by decide)

lemma hS54 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 54)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC54 kMu).mpr (by decide)

lemma hS55 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 55)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC55 kMu).mpr (by decide)

lemma hS56 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 56)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC56 kMu).mpr (by decide)

lemma hS57 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 57)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC57 kMu).mpr (by decide)

lemma hS58 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 58)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC58 kMu).mpr (by decide)

lemma hS59 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 59)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC59 kMu).mpr (by decide)

lemma hS60 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 60)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC60 kMu).mpr (by decide)

lemma hS61 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 61)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC61 kMu).mpr (by decide)

lemma hS62 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 62)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC62 kMu).mpr (by decide)

lemma hS63 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 63)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC63 kMu).mpr (by decide)

lemma hS64 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 64)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC64 kMu).mpr (by decide)

lemma hS65 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 65)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC65 kMu).mpr (by decide)

lemma hS66 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 66)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC66 kMu).mpr (by decide)

lemma hS67 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 67)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC67 kMu).mpr (by decide)

lemma hS68 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 68)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC68 kMu).mpr (by decide)

lemma hS69 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 69)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC69 kMu).mpr (by decide)

lemma hS70 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 70)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC70 kMu).mpr (by decide)

lemma hS71 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 71)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC71 kMu).mpr (by decide)

lemma hS72 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 72)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC72 kMu).mpr (by decide)

lemma hS73 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 73)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC73 kMu).mpr (by decide)

lemma hS74 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 74)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC74 kMu).mpr (by decide)

lemma hS75 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 75)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC75 kMu).mpr (by decide)

lemma hS76 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 76)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC76 kMu).mpr (by decide)

lemma hS77 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 77)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC77 kMu).mpr (by decide)

lemma hS78 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 78)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC78 kMu).mpr (by decide)

lemma hS79 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 79)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC79 kMu).mpr (by decide)

lemma hS80 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 80)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC80 kMu).mpr (by decide)

lemma hS81 : ¬ ((83 : ℤ) ∣ mu (zeta1 ^ 81)) :=
  (not_dvd_muOfBasis_iff (by norm_num) hC81 kMu).mpr (by decide)


/-- **`(S3)`.**  `83 ∤ mu (zeta1 ^ r)` for every `0 < r < 82`; only `r = 0` survives the
sieve.  (In particular this covers `0 < r < 81`.) -/
theorem not_dvd_mu_zeta1_pow : ∀ r : ℕ, 0 < r → r < 82 → ¬ ((83 : ℤ) ∣ mu (zeta1 ^ r)) := by
  intro r h0 h82
  interval_cases r
  exacts [hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, hS10, hS11, hS12, hS13, hS14, hS15, hS16, hS17, hS18, hS19, hS20, hS21, hS22, hS23, hS24, hS25, hS26, hS27, hS28, hS29, hS30, hS31, hS32, hS33, hS34, hS35, hS36, hS37, hS38, hS39, hS40, hS41, hS42, hS43, hS44, hS45, hS46, hS47, hS48, hS49, hS50, hS51, hS52, hS53, hS54, hS55, hS56, hS57, hS58, hS59, hS60, hS61, hS62, hS63, hS64, hS65, hS66, hS67, hS68, hS69, hS70, hS71, hS72, hS73, hS74, hS75, hS76, hS77, hS78, hS79, hS80, hS81]
