import IdealArithmetic.Examples.NF5_1_1240312500_5.PrimesBelow5_1_1240312500_5F36
import IdealArithmetic.PrimeSieve
noncomputable section

lemma PB2193I0_primes :
  ∀ (p : ℕ), p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 59 := by
  simp_rw [← List.mem_ofFn']
  convert PrimeSieve_mem_of_primesBelow _ 10000 _ ?_ _ _ primes_below_100_proof
  decide ; omega ; omega

def PB2193I0 : PrimesBelowBoundCertificateInterval O 1 59 2193 where
  m := 17
  g := ![5, 4, 5, 4, 1, 2, 2, 1, 2, 1, 3, 4, 3, 2, 2, 2, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59]
  hP := PB2193I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N2, I2N2, I2N2]
    · exact ![I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1, I7N1, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0]
    · exact ![I23N0, I23N1]
    · exact ![I29N0]
    · exact ![I31N0, I31N1, I31N2]
    · exact ![I37N0, I37N1, I37N2, I37N3]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
    · exact PBC29
    · exact PBC31
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2, 2, 2]
    · exact ![9, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![49, 7, 7, 7]
    · exact ![161051]
    · exact ![2197, 169]
    · exact ![83521, 17]
    · exact ![2476099]
    · exact ![12167, 529]
    · exact ![20511149]
    · exact ![29791, 31, 31]
    · exact ![1369, 37, 37, 37]
    · exact ![1681, 1681, 41]
    · exact ![3418801, 43]
    · exact ![103823, 2209]
    · exact ![7890481, 53]
    · exact ![205379, 59, 59]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
      exact NI2N2
      exact NI2N2
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
      exact NI3N1
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
      exact NI7N1
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
      exact NI37N3
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
  Il := ![[I2N0, I2N1, I2N2, I2N2, I2N2], [I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1, I7N1, I7N1], [], [I13N1], [I17N1], [], [I23N1], [], [I31N1, I31N2], [I37N0, I37N1, I37N2, I37N3], [I41N0, I41N1, I41N2], [I43N1], [], [I53N1], [I59N1, I59N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

lemma PB2193I1_primes :
  ∀ (p : ℕ), p ∈ Set.range ![61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139] ↔ Nat.Prime p ∧ 59 < p ∧ p ≤ 139 := by
  simp_rw [← List.mem_ofFn']
  convert PrimeSieve_mem_of_primesBelow _ 10000 _ ?_ _ _ primes_below_100_proof
  decide ; omega ; omega

def PB2193I1 : PrimesBelowBoundCertificateInterval O 59 139 2193 where
  m := 17
  g := ![3, 2, 3, 4, 3, 2, 3, 2, 1, 2, 2, 3, 2, 2, 5, 2, 3]
  P := ![61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139]
  hP := PB2193I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1, I73N2, I73N3]
    · exact ![I79N0, I79N1, I79N2]
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1, I131N2, I131N3, I131N4]
    · exact ![I137N0, I137N1]
    · exact ![I139N0, I139N1, I139N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
    · exact PBC139
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![226981, 61, 61]
    · exact ![20151121, 67]
    · exact ![357911, 71, 71]
    · exact ![5329, 73, 73, 73]
    · exact ![493039, 79, 79]
    · exact ![47458321, 83]
    · exact ![7921, 7921, 89]
    · exact ![912673, 9409]
    · exact ![10510100501]
    · exact ![1092727, 10609]
    · exact ![131079601, 107]
    · exact ![1295029, 109, 109]
    · exact ![163047361, 113]
    · exact ![260144641, 127]
    · exact ![131, 131, 131, 131, 131]
    · exact ![352275361, 137]
    · exact ![2685619, 139, 139]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
      exact NI73N2
      exact NI73N3
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
      exact NI89N2
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
      exact NI109N2
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N2
      exact NI131N3
      exact NI131N4
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
      exact NI139N2
  Il := ![[I61N1, I61N2], [I67N1], [I71N1, I71N2], [I73N1, I73N2, I73N3], [I79N1, I79N2], [I83N1], [I89N2], [], [], [], [I107N1], [I109N1, I109N2], [I113N1], [I127N1], [I131N0, I131N1, I131N2, I131N3, I131N4], [I137N1], [I139N1, I139N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

lemma PB2193I2_primes :
  ∀ (p : ℕ), p ∈ Set.range ![149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233] ↔ Nat.Prime p ∧ 139 < p ∧ p ≤ 233 := by
  simp_rw [← List.mem_ofFn']
  convert PrimeSieve_mem_of_primesBelow _ 10000 _ ?_ _ _ primes_below_100_proof
  decide ; omega ; omega

def PB2193I2 : PrimesBelowBoundCertificateInterval O 139 233 2193 where
  m := 17
  g := ![3, 3, 4, 2, 2, 2, 3, 3, 3, 2, 4, 1, 1, 2, 2, 1, 2]
  P := ![149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233]
  hP := PB2193I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0, I157N1, I157N2, I157N3]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1, I179N2]
    · exact ![I181N0, I181N1, I181N2]
    · exact ![I191N0, I191N1, I191N2]
    · exact ![I193N0, I193N1]
    · exact ![I197N0, I197N1, I197N2, I197N3]
    · exact ![I199N0]
    · exact ![I211N0]
    · exact ![I223N0, I223N1]
    · exact ![I227N0, I227N1]
    · exact ![I229N0]
    · exact ![I233N0, I233N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC149
    · exact PBC151
    · exact PBC157
    · exact PBC163
    · exact PBC167
    · exact PBC173
    · exact PBC179
    · exact PBC181
    · exact PBC191
    · exact PBC193
    · exact PBC197
    · exact PBC199
    · exact PBC211
    · exact PBC223
    · exact PBC227
    · exact PBC229
    · exact PBC233
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![3307949, 149, 149]
    · exact ![3442951, 151, 151]
    · exact ![24649, 157, 157, 157]
    · exact ![705911761, 163]
    · exact ![777796321, 167]
    · exact ![895745041, 173]
    · exact ![32041, 32041, 179]
    · exact ![5929741, 181, 181]
    · exact ![36481, 36481, 191]
    · exact ![7189057, 37249]
    · exact ![38809, 197, 197, 197]
    · exact ![312079600999]
    · exact ![418227202051]
    · exact ![11089567, 49729]
    · exact ![2655237841, 227]
    · exact ![629763392149]
    · exact ![12649337, 54289]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
      exact NI149N2
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
      exact NI157N2
      exact NI157N3
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
      exact NI179N2
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
      exact NI181N2
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
      exact NI191N2
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
      exact NI197N2
      exact NI197N3
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
  Il := ![[I149N1, I149N2], [I151N1, I151N2], [I157N1, I157N2, I157N3], [I163N1], [I167N1], [I173N1], [I179N2], [I181N1, I181N2], [I191N2], [], [I197N1, I197N2, I197N3], [], [], [], [I227N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

lemma PB2193I3_primes :
  ∀ (p : ℕ), p ∈ Set.range ![239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337] ↔ Nat.Prime p ∧ 233 < p ∧ p ≤ 337 := by
  simp_rw [← List.mem_ofFn']
  convert PrimeSieve_mem_of_primesBelow _ 10000 _ ?_ _ _ primes_below_100_proof
  decide ; omega ; omega

def PB2193I3 : PrimesBelowBoundCertificateInterval O 233 337 2193 where
  m := 17
  g := ![3, 3, 3, 2, 2, 3, 3, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2]
  P := ![239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337]
  hP := PB2193I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I239N0, I239N1, I239N2]
    · exact ![I241N0, I241N1, I241N2]
    · exact ![I251N0, I251N1, I251N2]
    · exact ![I257N0, I257N1]
    · exact ![I263N0, I263N1]
    · exact ![I269N0, I269N1, I269N2]
    · exact ![I271N0, I271N1, I271N2]
    · exact ![I277N0, I277N1]
    · exact ![I281N0]
    · exact ![I283N0, I283N1]
    · exact ![I293N0, I293N1]
    · exact ![I307N0, I307N1]
    · exact ![I311N0]
    · exact ![I313N0, I313N1]
    · exact ![I317N0, I317N1]
    · exact ![I331N0]
    · exact ![I337N0, I337N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC239
    · exact PBC241
    · exact PBC251
    · exact PBC257
    · exact PBC263
    · exact PBC269
    · exact PBC271
    · exact PBC277
    · exact PBC281
    · exact PBC283
    · exact PBC293
    · exact PBC307
    · exact PBC311
    · exact PBC313
    · exact PBC317
    · exact PBC331
    · exact PBC337
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![57121, 57121, 239]
    · exact ![58081, 58081, 241]
    · exact ![15813251, 251, 251]
    · exact ![4362470401, 257]
    · exact ![18191447, 69169]
    · exact ![72361, 72361, 269]
    · exact ![73441, 73441, 271]
    · exact ![21253933, 76729]
    · exact ![1751989905401]
    · exact ![22665187, 80089]
    · exact ![7370050801, 293]
    · exact ![28934443, 94249]
    · exact ![2909390022551]
    · exact ![30664297, 97969]
    · exact ![10098039121, 317]
    · exact ![3973195810651]
    · exact ![38272753, 113569]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
      exact NI239N2
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
      exact NI241N1
      exact NI241N2
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
      exact NI251N2
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
      exact NI257N1
    · dsimp ; intro j
      fin_cases j
      exact NI263N0
      exact NI263N1
    · dsimp ; intro j
      fin_cases j
      exact NI269N0
      exact NI269N1
      exact NI269N2
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
      exact NI271N1
      exact NI271N2
    · dsimp ; intro j
      fin_cases j
      exact NI277N0
      exact NI277N1
    · dsimp ; intro j
      fin_cases j
      exact NI281N0
    · dsimp ; intro j
      fin_cases j
      exact NI283N0
      exact NI283N1
    · dsimp ; intro j
      fin_cases j
      exact NI293N0
      exact NI293N1
    · dsimp ; intro j
      fin_cases j
      exact NI307N0
      exact NI307N1
    · dsimp ; intro j
      fin_cases j
      exact NI311N0
    · dsimp ; intro j
      fin_cases j
      exact NI313N0
      exact NI313N1
    · dsimp ; intro j
      fin_cases j
      exact NI317N0
      exact NI317N1
    · dsimp ; intro j
      fin_cases j
      exact NI331N0
    · dsimp ; intro j
      fin_cases j
      exact NI337N0
      exact NI337N1
  Il := ![[I239N2], [I241N2], [I251N1, I251N2], [I257N1], [], [I269N2], [I271N2], [], [], [], [I293N1], [], [], [], [I317N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

lemma PB2193I4_primes :
  ∀ (p : ℕ), p ∈ Set.range ![347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439] ↔ Nat.Prime p ∧ 337 < p ∧ p ≤ 439 := by
  simp_rw [← List.mem_ofFn']
  convert PrimeSieve_mem_of_primesBelow _ 10000 _ ?_ _ _ primes_below_100_proof
  decide ; omega ; omega

def PB2193I4 : PrimesBelowBoundCertificateInterval O 337 439 2193 where
  m := 17
  g := ![4, 3, 2, 3, 2, 2, 3, 2, 3, 2, 1, 3, 3, 1, 3, 2, 3]
  P := ![347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439]
  hP := PB2193I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I347N0, I347N1, I347N2, I347N3]
    · exact ![I349N0, I349N1, I349N2]
    · exact ![I353N0, I353N1]
    · exact ![I359N0, I359N1, I359N2]
    · exact ![I367N0, I367N1]
    · exact ![I373N0, I373N1]
    · exact ![I379N0, I379N1, I379N2]
    · exact ![I383N0, I383N1]
    · exact ![I389N0, I389N1, I389N2]
    · exact ![I397N0, I397N1]
    · exact ![I401N0]
    · exact ![I409N0, I409N1, I409N2]
    · exact ![I419N0, I419N1, I419N2]
    · exact ![I421N0]
    · exact ![I431N0, I431N1, I431N2]
    · exact ![I433N0, I433N1]
    · exact ![I439N0, I439N1, I439N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC347
    · exact PBC349
    · exact PBC353
    · exact PBC359
    · exact PBC367
    · exact PBC373
    · exact PBC379
    · exact PBC383
    · exact PBC389
    · exact PBC397
    · exact PBC401
    · exact PBC409
    · exact PBC419
    · exact PBC421
    · exact PBC431
    · exact PBC433
    · exact PBC439
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![120409, 347, 347, 347]
    · exact ![42508549, 349, 349]
    · exact ![43986977, 124609]
    · exact ![46268279, 359, 359]
    · exact ![49430863, 134689]
    · exact ![19356878641, 373]
    · exact ![143641, 143641, 379]
    · exact ![56181887, 146689]
    · exact ![58863869, 389, 389]
    · exact ![62570773, 157609]
    · exact ![10368641602001]
    · exact ![68417929, 409, 409]
    · exact ![175561, 175561, 419]
    · exact ![13225450646101]
    · exact ![185761, 185761, 431]
    · exact ![35152125121, 433]
    · exact ![192721, 192721, 439]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI347N0
      exact NI347N1
      exact NI347N2
      exact NI347N3
    · dsimp ; intro j
      fin_cases j
      exact NI349N0
      exact NI349N1
      exact NI349N2
    · dsimp ; intro j
      fin_cases j
      exact NI353N0
      exact NI353N1
    · dsimp ; intro j
      fin_cases j
      exact NI359N0
      exact NI359N1
      exact NI359N2
    · dsimp ; intro j
      fin_cases j
      exact NI367N0
      exact NI367N1
    · dsimp ; intro j
      fin_cases j
      exact NI373N0
      exact NI373N1
    · dsimp ; intro j
      fin_cases j
      exact NI379N0
      exact NI379N1
      exact NI379N2
    · dsimp ; intro j
      fin_cases j
      exact NI383N0
      exact NI383N1
    · dsimp ; intro j
      fin_cases j
      exact NI389N0
      exact NI389N1
      exact NI389N2
    · dsimp ; intro j
      fin_cases j
      exact NI397N0
      exact NI397N1
    · dsimp ; intro j
      fin_cases j
      exact NI401N0
    · dsimp ; intro j
      fin_cases j
      exact NI409N0
      exact NI409N1
      exact NI409N2
    · dsimp ; intro j
      fin_cases j
      exact NI419N0
      exact NI419N1
      exact NI419N2
    · dsimp ; intro j
      fin_cases j
      exact NI421N0
    · dsimp ; intro j
      fin_cases j
      exact NI431N0
      exact NI431N1
      exact NI431N2
    · dsimp ; intro j
      fin_cases j
      exact NI433N0
      exact NI433N1
    · dsimp ; intro j
      fin_cases j
      exact NI439N0
      exact NI439N1
      exact NI439N2
  Il := ![[I347N1, I347N2, I347N3], [I349N1, I349N2], [], [I359N1, I359N2], [], [I373N1], [I379N2], [], [I389N1, I389N2], [], [], [I409N1, I409N2], [I419N2], [], [I431N2], [I433N1], [I439N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

lemma PB2193I5_primes :
  ∀ (p : ℕ), p ∈ Set.range ![443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557] ↔ Nat.Prime p ∧ 439 < p ∧ p ≤ 557 := by
  simp_rw [← List.mem_ofFn']
  convert PrimeSieve_mem_of_primesBelow _ 10000 _ ?_ _ _ primes_below_100_proof
  decide ; omega ; omega

def PB2193I5 : PrimesBelowBoundCertificateInterval O 439 557 2193 where
  m := 17
  g := ![2, 3, 2, 1, 2, 4, 3, 2, 1, 1, 2, 1, 3, 2, 3, 2, 4]
  P := ![443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557]
  hP := PB2193I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I443N0, I443N1]
    · exact ![I449N0, I449N1, I449N2]
    · exact ![I457N0, I457N1]
    · exact ![I461N0]
    · exact ![I463N0, I463N1]
    · exact ![I467N0, I467N1, I467N2, I467N3]
    · exact ![I479N0, I479N1, I479N2]
    · exact ![I487N0, I487N1]
    · exact ![I491N0]
    · exact ![I499N0]
    · exact ![I503N0, I503N1]
    · exact ![I509N0]
    · exact ![I521N0, I521N1, I521N2]
    · exact ![I523N0, I523N1]
    · exact ![I541N0, I541N1, I541N2]
    · exact ![I547N0, I547N1]
    · exact ![I557N0, I557N1, I557N2, I557N3]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC443
    · exact PBC449
    · exact PBC457
    · exact PBC461
    · exact PBC463
    · exact PBC467
    · exact PBC479
    · exact PBC487
    · exact PBC491
    · exact PBC499
    · exact PBC503
    · exact PBC509
    · exact PBC521
    · exact PBC523
    · exact PBC541
    · exact PBC547
    · exact PBC557
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![38513670001, 443]
    · exact ![90518849, 449, 449]
    · exact ![43617904801, 457]
    · exact ![20821145878301]
    · exact ![45954068161, 463]
    · exact ![218089, 467, 467, 467]
    · exact ![109902239, 479, 479]
    · exact ![115501303, 237169]
    · exact ![28536943843451]
    · exact ![30938747502499]
    · exact ![64013554081, 503]
    · exact ![34165588961549]
    · exact ![141420761, 521, 521]
    · exact ![143055667, 273529]
    · exact ![158340421, 541, 541]
    · exact ![89526025681, 547]
    · exact ![310249, 557, 557, 557]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI443N0
      exact NI443N1
    · dsimp ; intro j
      fin_cases j
      exact NI449N0
      exact NI449N1
      exact NI449N2
    · dsimp ; intro j
      fin_cases j
      exact NI457N0
      exact NI457N1
    · dsimp ; intro j
      fin_cases j
      exact NI461N0
    · dsimp ; intro j
      fin_cases j
      exact NI463N0
      exact NI463N1
    · dsimp ; intro j
      fin_cases j
      exact NI467N0
      exact NI467N1
      exact NI467N2
      exact NI467N3
    · dsimp ; intro j
      fin_cases j
      exact NI479N0
      exact NI479N1
      exact NI479N2
    · dsimp ; intro j
      fin_cases j
      exact NI487N0
      exact NI487N1
    · dsimp ; intro j
      fin_cases j
      exact NI491N0
    · dsimp ; intro j
      fin_cases j
      exact NI499N0
    · dsimp ; intro j
      fin_cases j
      exact NI503N0
      exact NI503N1
    · dsimp ; intro j
      fin_cases j
      exact NI509N0
    · dsimp ; intro j
      fin_cases j
      exact NI521N0
      exact NI521N1
      exact NI521N2
    · dsimp ; intro j
      fin_cases j
      exact NI523N0
      exact NI523N1
    · dsimp ; intro j
      fin_cases j
      exact NI541N0
      exact NI541N1
      exact NI541N2
    · dsimp ; intro j
      fin_cases j
      exact NI547N0
      exact NI547N1
    · dsimp ; intro j
      fin_cases j
      exact NI557N0
      exact NI557N1
      exact NI557N2
      exact NI557N3
  Il := ![[I443N1], [I449N1, I449N2], [I457N1], [], [I463N1], [I467N1, I467N2, I467N3], [I479N1, I479N2], [], [], [], [I503N1], [], [I521N1, I521N2], [], [I541N1, I541N2], [I547N1], [I557N1, I557N2, I557N3]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

lemma PB2193I6_primes :
  ∀ (p : ℕ), p ∈ Set.range ![563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653] ↔ Nat.Prime p ∧ 557 < p ∧ p ≤ 653 := by
  simp_rw [← List.mem_ofFn']
  convert PrimeSieve_mem_of_primesBelow _ 10000 _ ?_ _ _ primes_below_100_proof
  decide ; omega ; omega

def PB2193I6 : PrimesBelowBoundCertificateInterval O 557 653 2193 where
  m := 17
  g := ![2, 1, 3, 2, 2, 2, 3, 1, 2, 2, 2, 3, 3, 3, 2, 2, 2]
  P := ![563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653]
  hP := PB2193I6_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I563N0, I563N1]
    · exact ![I569N0]
    · exact ![I571N0, I571N1, I571N2]
    · exact ![I577N0, I577N1]
    · exact ![I587N0, I587N1]
    · exact ![I593N0, I593N1]
    · exact ![I599N0, I599N1, I599N2]
    · exact ![I601N0]
    · exact ![I607N0, I607N1]
    · exact ![I613N0, I613N1]
    · exact ![I617N0, I617N1]
    · exact ![I619N0, I619N1, I619N2]
    · exact ![I631N0, I631N1, I631N2]
    · exact ![I641N0, I641N1, I641N2]
    · exact ![I643N0, I643N1]
    · exact ![I647N0, I647N1]
    · exact ![I653N0, I653N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC563
    · exact PBC569
    · exact PBC571
    · exact PBC577
    · exact PBC587
    · exact PBC593
    · exact PBC599
    · exact PBC601
    · exact PBC607
    · exact PBC613
    · exact PBC617
    · exact PBC619
    · exact PBC631
    · exact PBC641
    · exact PBC643
    · exact PBC647
    · exact PBC653
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![178453547, 316969]
    · exact ![59643254333849]
    · exact ![186169411, 571, 571]
    · exact ![110841719041, 577]
    · exact ![202262003, 344569]
    · exact ![123657019201, 593]
    · exact ![214921799, 599, 599]
    · exact ![78410163603001]
    · exact ![135754665601, 607]
    · exact ![230346397, 375769]
    · exact ![144924114721, 617]
    · exact ![383161, 383161, 619]
    · exact ![251239591, 631, 631]
    · exact ![263374721, 641, 641]
    · exact ![170940075601, 643]
    · exact ![270840023, 418609]
    · exact ![181824635281, 653]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI563N0
      exact NI563N1
    · dsimp ; intro j
      fin_cases j
      exact NI569N0
    · dsimp ; intro j
      fin_cases j
      exact NI571N0
      exact NI571N1
      exact NI571N2
    · dsimp ; intro j
      fin_cases j
      exact NI577N0
      exact NI577N1
    · dsimp ; intro j
      fin_cases j
      exact NI587N0
      exact NI587N1
    · dsimp ; intro j
      fin_cases j
      exact NI593N0
      exact NI593N1
    · dsimp ; intro j
      fin_cases j
      exact NI599N0
      exact NI599N1
      exact NI599N2
    · dsimp ; intro j
      fin_cases j
      exact NI601N0
    · dsimp ; intro j
      fin_cases j
      exact NI607N0
      exact NI607N1
    · dsimp ; intro j
      fin_cases j
      exact NI613N0
      exact NI613N1
    · dsimp ; intro j
      fin_cases j
      exact NI617N0
      exact NI617N1
    · dsimp ; intro j
      fin_cases j
      exact NI619N0
      exact NI619N1
      exact NI619N2
    · dsimp ; intro j
      fin_cases j
      exact NI631N0
      exact NI631N1
      exact NI631N2
    · dsimp ; intro j
      fin_cases j
      exact NI641N0
      exact NI641N1
      exact NI641N2
    · dsimp ; intro j
      fin_cases j
      exact NI643N0
      exact NI643N1
    · dsimp ; intro j
      fin_cases j
      exact NI647N0
      exact NI647N1
    · dsimp ; intro j
      fin_cases j
      exact NI653N0
      exact NI653N1
  Il := ![[], [], [I571N1, I571N2], [I577N1], [], [I593N1], [I599N1, I599N2], [], [I607N1], [], [I617N1], [I619N2], [I631N1, I631N2], [I641N1, I641N2], [I643N1], [], [I653N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

lemma PB2193I7_primes :
  ∀ (p : ℕ), p ∈ Set.range ![659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769] ↔ Nat.Prime p ∧ 653 < p ∧ p ≤ 769 := by
  simp_rw [← List.mem_ofFn']
  convert PrimeSieve_mem_of_primesBelow _ 10000 _ ?_ _ _ primes_below_100_proof
  decide ; omega ; omega

def PB2193I7 : PrimesBelowBoundCertificateInterval O 653 769 2193 where
  m := 17
  g := ![5, 1, 2, 2, 2, 1, 1, 3, 3, 2, 4, 1, 2, 1, 4, 1, 1]
  P := ![659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769]
  hP := PB2193I7_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I659N0, I659N1, I659N2, I659N3, I659N4]
    · exact ![I661N0]
    · exact ![I673N0, I673N1]
    · exact ![I677N0, I677N1]
    · exact ![I683N0, I683N1]
    · exact ![I691N0]
    · exact ![I701N0]
    · exact ![I709N0, I709N1, I709N2]
    · exact ![I719N0, I719N1, I719N2]
    · exact ![I727N0, I727N1]
    · exact ![I733N0, I733N1, I733N2, I733N3]
    · exact ![I739N0]
    · exact ![I743N0, I743N1]
    · exact ![I751N0]
    · exact ![I757N0, I757N1, I757N2, I757N3]
    · exact ![I761N0]
    · exact ![I769N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC659
    · exact PBC661
    · exact PBC673
    · exact PBC677
    · exact PBC683
    · exact PBC691
    · exact PBC701
    · exact PBC709
    · exact PBC719
    · exact PBC727
    · exact PBC733
    · exact PBC739
    · exact PBC743
    · exact PBC751
    · exact PBC757
    · exact PBC761
    · exact PBC769
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![659, 659, 659, 659, 659]
    · exact ![126184873719301]
    · exact ![205144679041, 673]
    · exact ![310288733, 458329]
    · exact ![217611987121, 683]
    · exact ![157539780804451]
    · exact ![169273934903501]
    · exact ![356400829, 709, 709]
    · exact ![516961, 516961, 719]
    · exact ![279342903841, 727]
    · exact ![537289, 733, 733, 733]
    · exact ![220405380367699]
    · exact ![304758098401, 743]
    · exact ![238890943128751]
    · exact ![573049, 757, 757, 757]
    · exact ![255225041939801]
    · exact ![268925323054849]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI659N0
      exact NI659N1
      exact NI659N2
      exact NI659N3
      exact NI659N4
    · dsimp ; intro j
      fin_cases j
      exact NI661N0
    · dsimp ; intro j
      fin_cases j
      exact NI673N0
      exact NI673N1
    · dsimp ; intro j
      fin_cases j
      exact NI677N0
      exact NI677N1
    · dsimp ; intro j
      fin_cases j
      exact NI683N0
      exact NI683N1
    · dsimp ; intro j
      fin_cases j
      exact NI691N0
    · dsimp ; intro j
      fin_cases j
      exact NI701N0
    · dsimp ; intro j
      fin_cases j
      exact NI709N0
      exact NI709N1
      exact NI709N2
    · dsimp ; intro j
      fin_cases j
      exact NI719N0
      exact NI719N1
      exact NI719N2
    · dsimp ; intro j
      fin_cases j
      exact NI727N0
      exact NI727N1
    · dsimp ; intro j
      fin_cases j
      exact NI733N0
      exact NI733N1
      exact NI733N2
      exact NI733N3
    · dsimp ; intro j
      fin_cases j
      exact NI739N0
    · dsimp ; intro j
      fin_cases j
      exact NI743N0
      exact NI743N1
    · dsimp ; intro j
      fin_cases j
      exact NI751N0
    · dsimp ; intro j
      fin_cases j
      exact NI757N0
      exact NI757N1
      exact NI757N2
      exact NI757N3
    · dsimp ; intro j
      fin_cases j
      exact NI761N0
    · dsimp ; intro j
      fin_cases j
      exact NI769N0
  Il := ![[I659N0, I659N1, I659N2, I659N3, I659N4], [], [I673N1], [], [I683N1], [], [], [I709N1, I709N2], [I719N2], [I727N1], [I733N1, I733N2, I733N3], [], [I743N1], [], [I757N1, I757N2, I757N3], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

lemma PB2193I8_primes :
  ∀ (p : ℕ), p ∈ Set.range ![773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883] ↔ Nat.Prime p ∧ 769 < p ∧ p ≤ 883 := by
  simp_rw [← List.mem_ofFn']
  convert PrimeSieve_mem_of_primesBelow _ 10000 _ ?_ _ _ primes_below_100_proof
  decide ; omega ; omega

def PB2193I8 : PrimesBelowBoundCertificateInterval O 769 883 2193 where
  m := 17
  g := ![2, 2, 2, 3, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 2, 3, 2]
  P := ![773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883]
  hP := PB2193I8_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I773N0, I773N1]
    · exact ![I787N0, I787N1]
    · exact ![I797N0, I797N1]
    · exact ![I809N0, I809N1, I809N2]
    · exact ![I811N0]
    · exact ![I821N0]
    · exact ![I823N0, I823N1]
    · exact ![I827N0, I827N1]
    · exact ![I829N0, I829N1, I829N2]
    · exact ![I839N0]
    · exact ![I853N0, I853N1]
    · exact ![I857N0, I857N1, I857N2, I857N3]
    · exact ![I859N0]
    · exact ![I863N0, I863N1]
    · exact ![I877N0, I877N1]
    · exact ![I881N0, I881N1, I881N2]
    · exact ![I883N0, I883N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC773
    · exact PBC787
    · exact PBC797
    · exact PBC809
    · exact PBC811
    · exact PBC821
    · exact PBC823
    · exact PBC827
    · exact PBC829
    · exact PBC839
    · exact PBC853
    · exact PBC857
    · exact PBC859
    · exact PBC863
    · exact PBC877
    · exact PBC881
    · exact PBC883
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![357040905841, 773]
    · exact ![383617958161, 787]
    · exact ![506261573, 635209]
    · exact ![654481, 654481, 809]
    · exact ![350836097125051]
    · exact ![373005972408101]
    · exact ![557441767, 677329]
    · exact ![565609283, 683929]
    · exact ![569722789, 829, 829]
    · exact ![415728505588199]
    · exact ![529414856881, 853]
    · exact ![734449, 857, 857, 857]
    · exact ![467698329968299]
    · exact ![642735647, 744769]
    · exact ![674526133, 769129]
    · exact ![776161, 776161, 881]
    · exact ![607914936721, 883]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI773N0
      exact NI773N1
    · dsimp ; intro j
      fin_cases j
      exact NI787N0
      exact NI787N1
    · dsimp ; intro j
      fin_cases j
      exact NI797N0
      exact NI797N1
    · dsimp ; intro j
      fin_cases j
      exact NI809N0
      exact NI809N1
      exact NI809N2
    · dsimp ; intro j
      fin_cases j
      exact NI811N0
    · dsimp ; intro j
      fin_cases j
      exact NI821N0
    · dsimp ; intro j
      fin_cases j
      exact NI823N0
      exact NI823N1
    · dsimp ; intro j
      fin_cases j
      exact NI827N0
      exact NI827N1
    · dsimp ; intro j
      fin_cases j
      exact NI829N0
      exact NI829N1
      exact NI829N2
    · dsimp ; intro j
      fin_cases j
      exact NI839N0
    · dsimp ; intro j
      fin_cases j
      exact NI853N0
      exact NI853N1
    · dsimp ; intro j
      fin_cases j
      exact NI857N0
      exact NI857N1
      exact NI857N2
      exact NI857N3
    · dsimp ; intro j
      fin_cases j
      exact NI859N0
    · dsimp ; intro j
      fin_cases j
      exact NI863N0
      exact NI863N1
    · dsimp ; intro j
      fin_cases j
      exact NI877N0
      exact NI877N1
    · dsimp ; intro j
      fin_cases j
      exact NI881N0
      exact NI881N1
      exact NI881N2
    · dsimp ; intro j
      fin_cases j
      exact NI883N0
      exact NI883N1
  Il := ![[I773N1], [I787N1], [], [I809N2], [], [], [], [], [I829N1, I829N2], [], [I853N1], [I857N1, I857N2, I857N3], [], [], [], [I881N2], [I883N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

lemma PB2193I9_primes :
  ∀ (p : ℕ), p ∈ Set.range ![887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013] ↔ Nat.Prime p ∧ 883 < p ∧ p ≤ 1013 := by
  simp_rw [← List.mem_ofFn']
  convert PrimeSieve_mem_of_primesBelow _ 10000 _ ?_ _ _ primes_below_100_proof
  decide ; omega ; omega

def PB2193I9 : PrimesBelowBoundCertificateInterval O 883 1013 2193 where
  m := 17
  g := ![2, 2, 3, 3, 3, 2, 1, 2, 2, 2, 1, 4, 2, 3, 2, 1, 2]
  P := ![887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013]
  hP := PB2193I9_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I887N0, I887N1]
    · exact ![I907N0, I907N1]
    · exact ![I911N0, I911N1, I911N2]
    · exact ![I919N0, I919N1, I919N2]
    · exact ![I929N0, I929N1, I929N2]
    · exact ![I937N0, I937N1]
    · exact ![I941N0]
    · exact ![I947N0, I947N1]
    · exact ![I953N0, I953N1]
    · exact ![I967N0, I967N1]
    · exact ![I971N0]
    · exact ![I977N0, I977N1, I977N2, I977N3]
    · exact ![I983N0, I983N1]
    · exact ![I991N0, I991N1, I991N2]
    · exact ![I997N0, I997N1]
    · exact ![I1009N0]
    · exact ![I1013N0, I1013N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC887
    · exact PBC907
    · exact PBC911
    · exact PBC919
    · exact PBC929
    · exact PBC937
    · exact PBC941
    · exact PBC947
    · exact PBC953
    · exact PBC967
    · exact PBC971
    · exact PBC977
    · exact PBC983
    · exact PBC991
    · exact PBC997
    · exact PBC1009
    · exact PBC1013
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![619005459361, 887]
    · exact ![746142643, 822649]
    · exact ![829921, 829921, 911]
    · exact ![844561, 844561, 919]
    · exact ![863041, 863041, 929]
    · exact ![822656953, 877969]
    · exact ![737816081880701]
    · exact ![804266382481, 947]
    · exact ![865523177, 908209]
    · exact ![904231063, 935089]
    · exact ![863169625893851]
    · exact ![954529, 977, 977, 977]
    · exact ![933714431521, 983]
    · exact ![973242271, 991, 991]
    · exact ![988053892081, 997]
    · exact ![1045817322864049]
    · exact ![1053022816561, 1013]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI887N0
      exact NI887N1
    · dsimp ; intro j
      fin_cases j
      exact NI907N0
      exact NI907N1
    · dsimp ; intro j
      fin_cases j
      exact NI911N0
      exact NI911N1
      exact NI911N2
    · dsimp ; intro j
      fin_cases j
      exact NI919N0
      exact NI919N1
      exact NI919N2
    · dsimp ; intro j
      fin_cases j
      exact NI929N0
      exact NI929N1
      exact NI929N2
    · dsimp ; intro j
      fin_cases j
      exact NI937N0
      exact NI937N1
    · dsimp ; intro j
      fin_cases j
      exact NI941N0
    · dsimp ; intro j
      fin_cases j
      exact NI947N0
      exact NI947N1
    · dsimp ; intro j
      fin_cases j
      exact NI953N0
      exact NI953N1
    · dsimp ; intro j
      fin_cases j
      exact NI967N0
      exact NI967N1
    · dsimp ; intro j
      fin_cases j
      exact NI971N0
    · dsimp ; intro j
      fin_cases j
      exact NI977N0
      exact NI977N1
      exact NI977N2
      exact NI977N3
    · dsimp ; intro j
      fin_cases j
      exact NI983N0
      exact NI983N1
    · dsimp ; intro j
      fin_cases j
      exact NI991N0
      exact NI991N1
      exact NI991N2
    · dsimp ; intro j
      fin_cases j
      exact NI997N0
      exact NI997N1
    · dsimp ; intro j
      fin_cases j
      exact NI1009N0
    · dsimp ; intro j
      fin_cases j
      exact NI1013N0
      exact NI1013N1
  Il := ![[I887N1], [], [I911N2], [I919N2], [I929N2], [], [], [I947N1], [], [], [], [I977N1, I977N2, I977N3], [I983N1], [I991N1, I991N2], [I997N1], [], [I1013N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

lemma PB2193I10_primes :
  ∀ (p : ℕ), p ∈ Set.range ![1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117] ↔ Nat.Prime p ∧ 1013 < p ∧ p ≤ 1117 := by
  simp_rw [← List.mem_ofFn']
  convert PrimeSieve_mem_of_primesBelow _ 10000 _ ?_ _ _ primes_below_100_proof
  decide ; omega ; omega

def PB2193I10 : PrimesBelowBoundCertificateInterval O 1013 1117 2193 where
  m := 17
  g := ![3, 3, 3, 2, 3, 3, 3, 3, 2, 1, 2, 3, 2, 2, 4, 1, 2]
  P := ![1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117]
  hP := PB2193I10_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I1019N0, I1019N1, I1019N2]
    · exact ![I1021N0, I1021N1, I1021N2]
    · exact ![I1031N0, I1031N1, I1031N2]
    · exact ![I1033N0, I1033N1]
    · exact ![I1039N0, I1039N1, I1039N2]
    · exact ![I1049N0, I1049N1, I1049N2]
    · exact ![I1051N0, I1051N1, I1051N2]
    · exact ![I1061N0, I1061N1, I1061N2]
    · exact ![I1063N0, I1063N1]
    · exact ![I1069N0]
    · exact ![I1087N0, I1087N1]
    · exact ![I1091N0, I1091N1, I1091N2]
    · exact ![I1093N0, I1093N1]
    · exact ![I1097N0, I1097N1]
    · exact ![I1103N0, I1103N1, I1103N2, I1103N3]
    · exact ![I1109N0]
    · exact ![I1117N0, I1117N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC1019
    · exact PBC1021
    · exact PBC1031
    · exact PBC1033
    · exact PBC1039
    · exact PBC1049
    · exact PBC1051
    · exact PBC1061
    · exact PBC1063
    · exact PBC1069
    · exact PBC1087
    · exact PBC1091
    · exact PBC1093
    · exact PBC1097
    · exact PBC1103
    · exact PBC1109
    · exact PBC1117
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1038361, 1038361, 1019]
    · exact ![1064332261, 1021, 1021]
    · exact ![1062961, 1062961, 1031]
    · exact ![1102302937, 1067089]
    · exact ![1121622319, 1039, 1039]
    · exact ![1154320649, 1049, 1049]
    · exact ![1104601, 1104601, 1051]
    · exact ![1125721, 1125721, 1061]
    · exact ![1201157047, 1129969]
    · exact ![1396009989636349]
    · exact ![1396105301761, 1087]
    · exact ![1298596571, 1091, 1091]
    · exact ![1427186233201, 1093]
    · exact ![1320139673, 1203409]
    · exact ![1216609, 1103, 1103, 1103]
    · exact ![1677481467044549]
    · exact ![1556727840721, 1117]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI1019N0
      exact NI1019N1
      exact NI1019N2
    · dsimp ; intro j
      fin_cases j
      exact NI1021N0
      exact NI1021N1
      exact NI1021N2
    · dsimp ; intro j
      fin_cases j
      exact NI1031N0
      exact NI1031N1
      exact NI1031N2
    · dsimp ; intro j
      fin_cases j
      exact NI1033N0
      exact NI1033N1
    · dsimp ; intro j
      fin_cases j
      exact NI1039N0
      exact NI1039N1
      exact NI1039N2
    · dsimp ; intro j
      fin_cases j
      exact NI1049N0
      exact NI1049N1
      exact NI1049N2
    · dsimp ; intro j
      fin_cases j
      exact NI1051N0
      exact NI1051N1
      exact NI1051N2
    · dsimp ; intro j
      fin_cases j
      exact NI1061N0
      exact NI1061N1
      exact NI1061N2
    · dsimp ; intro j
      fin_cases j
      exact NI1063N0
      exact NI1063N1
    · dsimp ; intro j
      fin_cases j
      exact NI1069N0
    · dsimp ; intro j
      fin_cases j
      exact NI1087N0
      exact NI1087N1
    · dsimp ; intro j
      fin_cases j
      exact NI1091N0
      exact NI1091N1
      exact NI1091N2
    · dsimp ; intro j
      fin_cases j
      exact NI1093N0
      exact NI1093N1
    · dsimp ; intro j
      fin_cases j
      exact NI1097N0
      exact NI1097N1
    · dsimp ; intro j
      fin_cases j
      exact NI1103N0
      exact NI1103N1
      exact NI1103N2
      exact NI1103N3
    · dsimp ; intro j
      fin_cases j
      exact NI1109N0
    · dsimp ; intro j
      fin_cases j
      exact NI1117N0
      exact NI1117N1
  Il := ![[I1019N2], [I1021N1, I1021N2], [I1031N2], [], [I1039N1, I1039N2], [I1049N1, I1049N2], [I1051N2], [I1061N2], [], [], [I1087N1], [I1091N1, I1091N2], [I1093N1], [], [I1103N1, I1103N2, I1103N3], [], [I1117N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

lemma PB2193I11_primes :
  ∀ (p : ℕ), p ∈ Set.range ![1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249] ↔ Nat.Prime p ∧ 1117 < p ∧ p ≤ 1249 := by
  simp_rw [← List.mem_ofFn']
  convert PrimeSieve_mem_of_primesBelow _ 10000 _ ?_ _ _ primes_below_100_proof
  decide ; omega ; omega

def PB2193I11 : PrimesBelowBoundCertificateInterval O 1117 1249 2193 where
  m := 17
  g := ![2, 3, 3, 2, 4, 3, 3, 2, 2, 1, 2, 4, 4, 3, 1, 4, 3]
  P := ![1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249]
  hP := PB2193I11_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I1123N0, I1123N1]
    · exact ![I1129N0, I1129N1, I1129N2]
    · exact ![I1151N0, I1151N1, I1151N2]
    · exact ![I1153N0, I1153N1]
    · exact ![I1163N0, I1163N1, I1163N2, I1163N3]
    · exact ![I1171N0, I1171N1, I1171N2]
    · exact ![I1181N0, I1181N1, I1181N2]
    · exact ![I1187N0, I1187N1]
    · exact ![I1193N0, I1193N1]
    · exact ![I1201N0]
    · exact ![I1213N0, I1213N1]
    · exact ![I1217N0, I1217N1, I1217N2, I1217N3]
    · exact ![I1223N0, I1223N1, I1223N2, I1223N3]
    · exact ![I1229N0, I1229N1, I1229N2]
    · exact ![I1231N0]
    · exact ![I1237N0, I1237N1, I1237N2, I1237N3]
    · exact ![I1249N0, I1249N1, I1249N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC1123
    · exact PBC1129
    · exact PBC1151
    · exact PBC1153
    · exact PBC1163
    · exact PBC1171
    · exact PBC1181
    · exact PBC1187
    · exact PBC1193
    · exact PBC1201
    · exact PBC1213
    · exact PBC1217
    · exact PBC1223
    · exact PBC1229
    · exact PBC1231
    · exact PBC1237
    · exact PBC1249
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1590446354641, 1123]
    · exact ![1439069689, 1129, 1129]
    · exact ![1524845951, 1151, 1151]
    · exact ![1767328289281, 1153]
    · exact ![1352569, 1163, 1163, 1163]
    · exact ![1371241, 1371241, 1171]
    · exact ![1394761, 1394761, 1181]
    · exact ![1672446203, 1408969]
    · exact ![1697936057, 1423249]
    · exact ![2498705294406001]
    · exact ![2164926734161, 1213]
    · exact ![1481089, 1217, 1217, 1217]
    · exact ![1495729, 1223, 1223, 1223]
    · exact ![1856331989, 1229, 1229]
    · exact ![2826768640155151]
    · exact ![1530169, 1237, 1237, 1237]
    · exact ![1948441249, 1249, 1249]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI1123N0
      exact NI1123N1
    · dsimp ; intro j
      fin_cases j
      exact NI1129N0
      exact NI1129N1
      exact NI1129N2
    · dsimp ; intro j
      fin_cases j
      exact NI1151N0
      exact NI1151N1
      exact NI1151N2
    · dsimp ; intro j
      fin_cases j
      exact NI1153N0
      exact NI1153N1
    · dsimp ; intro j
      fin_cases j
      exact NI1163N0
      exact NI1163N1
      exact NI1163N2
      exact NI1163N3
    · dsimp ; intro j
      fin_cases j
      exact NI1171N0
      exact NI1171N1
      exact NI1171N2
    · dsimp ; intro j
      fin_cases j
      exact NI1181N0
      exact NI1181N1
      exact NI1181N2
    · dsimp ; intro j
      fin_cases j
      exact NI1187N0
      exact NI1187N1
    · dsimp ; intro j
      fin_cases j
      exact NI1193N0
      exact NI1193N1
    · dsimp ; intro j
      fin_cases j
      exact NI1201N0
    · dsimp ; intro j
      fin_cases j
      exact NI1213N0
      exact NI1213N1
    · dsimp ; intro j
      fin_cases j
      exact NI1217N0
      exact NI1217N1
      exact NI1217N2
      exact NI1217N3
    · dsimp ; intro j
      fin_cases j
      exact NI1223N0
      exact NI1223N1
      exact NI1223N2
      exact NI1223N3
    · dsimp ; intro j
      fin_cases j
      exact NI1229N0
      exact NI1229N1
      exact NI1229N2
    · dsimp ; intro j
      fin_cases j
      exact NI1231N0
    · dsimp ; intro j
      fin_cases j
      exact NI1237N0
      exact NI1237N1
      exact NI1237N2
      exact NI1237N3
    · dsimp ; intro j
      fin_cases j
      exact NI1249N0
      exact NI1249N1
      exact NI1249N2
  Il := ![[I1123N1], [I1129N1, I1129N2], [I1151N1, I1151N2], [I1153N1], [I1163N1, I1163N2, I1163N3], [I1171N2], [I1181N2], [], [], [], [I1213N1], [I1217N1, I1217N2, I1217N3], [I1223N1, I1223N2, I1223N3], [I1229N1, I1229N2], [], [I1237N1, I1237N2, I1237N3], [I1249N1, I1249N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

lemma PB2193I12_primes :
  ∀ (p : ℕ), p ∈ Set.range ![1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381] ↔ Nat.Prime p ∧ 1249 < p ∧ p ≤ 1381 := by
  simp_rw [← List.mem_ofFn']
  convert PrimeSieve_mem_of_primesBelow _ 10000 _ ?_ _ _ primes_below_100_proof
  decide ; omega ; omega

def PB2193I12 : PrimesBelowBoundCertificateInterval O 1249 1381 2193 where
  m := 17
  g := ![3, 2, 3, 2, 1, 3, 2, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1]
  P := ![1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381]
  hP := PB2193I12_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I1259N0, I1259N1, I1259N2]
    · exact ![I1277N0, I1277N1]
    · exact ![I1279N0, I1279N1, I1279N2]
    · exact ![I1283N0, I1283N1]
    · exact ![I1289N0]
    · exact ![I1291N0, I1291N1, I1291N2]
    · exact ![I1297N0, I1297N1]
    · exact ![I1301N0]
    · exact ![I1303N0, I1303N1]
    · exact ![I1307N0, I1307N1]
    · exact ![I1319N0]
    · exact ![I1321N0]
    · exact ![I1327N0, I1327N1]
    · exact ![I1361N0, I1361N1, I1361N2]
    · exact ![I1367N0, I1367N1]
    · exact ![I1373N0, I1373N1]
    · exact ![I1381N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC1259
    · exact PBC1277
    · exact PBC1279
    · exact PBC1283
    · exact PBC1289
    · exact PBC1291
    · exact PBC1297
    · exact PBC1301
    · exact PBC1303
    · exact PBC1307
    · exact PBC1319
    · exact PBC1321
    · exact PBC1327
    · exact PBC1361
    · exact PBC1367
    · exact PBC1373
    · exact PBC1381
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1995616979, 1259, 1259]
    · exact ![2659277071441, 1277]
    · exact ![2092240639, 1279, 1279]
    · exact ![2111932187, 1646089]
    · exact ![3558480471105449]
    · exact ![1666681, 1666681, 1291]
    · exact ![2829827119681, 1297]
    · exact ![3727232486906501]
    · exact ![2882555400481, 1303]
    · exact ![2232681443, 1708249]
    · exact ![3992307436662599]
    · exact ![4022667049110601]
    · exact ![2336752783, 1760929]
    · exact ![2521008881, 1361, 1361]
    · exact ![3491998578721, 1367]
    · exact ![3553711346641, 1373]
    · exact ![5023060313370901]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI1259N0
      exact NI1259N1
      exact NI1259N2
    · dsimp ; intro j
      fin_cases j
      exact NI1277N0
      exact NI1277N1
    · dsimp ; intro j
      fin_cases j
      exact NI1279N0
      exact NI1279N1
      exact NI1279N2
    · dsimp ; intro j
      fin_cases j
      exact NI1283N0
      exact NI1283N1
    · dsimp ; intro j
      fin_cases j
      exact NI1289N0
    · dsimp ; intro j
      fin_cases j
      exact NI1291N0
      exact NI1291N1
      exact NI1291N2
    · dsimp ; intro j
      fin_cases j
      exact NI1297N0
      exact NI1297N1
    · dsimp ; intro j
      fin_cases j
      exact NI1301N0
    · dsimp ; intro j
      fin_cases j
      exact NI1303N0
      exact NI1303N1
    · dsimp ; intro j
      fin_cases j
      exact NI1307N0
      exact NI1307N1
    · dsimp ; intro j
      fin_cases j
      exact NI1319N0
    · dsimp ; intro j
      fin_cases j
      exact NI1321N0
    · dsimp ; intro j
      fin_cases j
      exact NI1327N0
      exact NI1327N1
    · dsimp ; intro j
      fin_cases j
      exact NI1361N0
      exact NI1361N1
      exact NI1361N2
    · dsimp ; intro j
      fin_cases j
      exact NI1367N0
      exact NI1367N1
    · dsimp ; intro j
      fin_cases j
      exact NI1373N0
      exact NI1373N1
    · dsimp ; intro j
      fin_cases j
      exact NI1381N0
  Il := ![[I1259N1, I1259N2], [I1277N1], [I1279N1, I1279N2], [], [], [I1291N2], [I1297N1], [], [I1303N1], [], [], [], [], [I1361N1, I1361N2], [I1367N1], [I1373N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

lemma PB2193I13_primes :
  ∀ (p : ℕ), p ∈ Set.range ![1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493] ↔ Nat.Prime p ∧ 1381 < p ∧ p ≤ 1493 := by
  simp_rw [← List.mem_ofFn']
  convert PrimeSieve_mem_of_primesBelow _ 10000 _ ?_ _ _ primes_below_100_proof
  decide ; omega ; omega

def PB2193I13 : PrimesBelowBoundCertificateInterval O 1381 1493 2193 where
  m := 17
  g := ![1, 3, 2, 2, 1, 2, 3, 2, 3, 2, 1, 3, 1, 2, 2, 1, 4]
  P := ![1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493]
  hP := PB2193I13_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I1399N0]
    · exact ![I1409N0, I1409N1, I1409N2]
    · exact ![I1423N0, I1423N1]
    · exact ![I1427N0, I1427N1]
    · exact ![I1429N0]
    · exact ![I1433N0, I1433N1]
    · exact ![I1439N0, I1439N1, I1439N2]
    · exact ![I1447N0, I1447N1]
    · exact ![I1451N0, I1451N1, I1451N2]
    · exact ![I1453N0, I1453N1]
    · exact ![I1459N0]
    · exact ![I1471N0, I1471N1, I1471N2]
    · exact ![I1481N0]
    · exact ![I1483N0, I1483N1]
    · exact ![I1487N0, I1487N1]
    · exact ![I1489N0]
    · exact ![I1493N0, I1493N1, I1493N2, I1493N3]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC1399
    · exact PBC1409
    · exact PBC1423
    · exact PBC1427
    · exact PBC1429
    · exact PBC1433
    · exact PBC1439
    · exact PBC1447
    · exact PBC1451
    · exact PBC1453
    · exact PBC1459
    · exact PBC1471
    · exact PBC1481
    · exact PBC1483
    · exact PBC1487
    · exact PBC1489
    · exact PBC1493
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![5359059420406999]
    · exact ![1985281, 1985281, 1409]
    · exact ![2881473967, 2024929]
    · exact ![4146635796241, 1427]
    · exact ![5958832035878149]
    · exact ![2942649737, 2053489]
    · exact ![2979767519, 1439, 1439]
    · exact ![4384036128481, 1447]
    · exact ![2105401, 2105401, 1451]
    · exact ![4457203441681, 1453]
    · exact ![6611141604851299]
    · exact ![3183010111, 1471, 1471]
    · exact ![7124842897431401]
    · exact ![3261545587, 2199289]
    · exact ![3288008303, 2211169]
    · exact ![7319366412146449]
    · exact ![2229049, 1493, 1493, 1493]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI1399N0
    · dsimp ; intro j
      fin_cases j
      exact NI1409N0
      exact NI1409N1
      exact NI1409N2
    · dsimp ; intro j
      fin_cases j
      exact NI1423N0
      exact NI1423N1
    · dsimp ; intro j
      fin_cases j
      exact NI1427N0
      exact NI1427N1
    · dsimp ; intro j
      fin_cases j
      exact NI1429N0
    · dsimp ; intro j
      fin_cases j
      exact NI1433N0
      exact NI1433N1
    · dsimp ; intro j
      fin_cases j
      exact NI1439N0
      exact NI1439N1
      exact NI1439N2
    · dsimp ; intro j
      fin_cases j
      exact NI1447N0
      exact NI1447N1
    · dsimp ; intro j
      fin_cases j
      exact NI1451N0
      exact NI1451N1
      exact NI1451N2
    · dsimp ; intro j
      fin_cases j
      exact NI1453N0
      exact NI1453N1
    · dsimp ; intro j
      fin_cases j
      exact NI1459N0
    · dsimp ; intro j
      fin_cases j
      exact NI1471N0
      exact NI1471N1
      exact NI1471N2
    · dsimp ; intro j
      fin_cases j
      exact NI1481N0
    · dsimp ; intro j
      fin_cases j
      exact NI1483N0
      exact NI1483N1
    · dsimp ; intro j
      fin_cases j
      exact NI1487N0
      exact NI1487N1
    · dsimp ; intro j
      fin_cases j
      exact NI1489N0
    · dsimp ; intro j
      fin_cases j
      exact NI1493N0
      exact NI1493N1
      exact NI1493N2
      exact NI1493N3
  Il := ![[], [I1409N2], [], [I1427N1], [], [], [I1439N1, I1439N2], [I1447N1], [I1451N2], [I1453N1], [], [I1471N1, I1471N2], [], [], [], [], [I1493N1, I1493N2, I1493N3]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

lemma PB2193I14_primes :
  ∀ (p : ℕ), p ∈ Set.range ![1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613] ↔ Nat.Prime p ∧ 1493 < p ∧ p ≤ 1613 := by
  simp_rw [← List.mem_ofFn']
  convert PrimeSieve_mem_of_primesBelow _ 10000 _ ?_ _ _ primes_below_100_proof
  decide ; omega ; omega

def PB2193I14 : PrimesBelowBoundCertificateInterval O 1493 1613 2193 where
  m := 17
  g := ![3, 3, 2, 3, 2, 1, 2, 3, 2, 1, 5, 2, 2, 1, 2, 1, 4]
  P := ![1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613]
  hP := PB2193I14_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I1499N0, I1499N1, I1499N2]
    · exact ![I1511N0, I1511N1, I1511N2]
    · exact ![I1523N0, I1523N1]
    · exact ![I1531N0, I1531N1, I1531N2]
    · exact ![I1543N0, I1543N1]
    · exact ![I1549N0]
    · exact ![I1553N0, I1553N1]
    · exact ![I1559N0, I1559N1, I1559N2]
    · exact ![I1567N0, I1567N1]
    · exact ![I1571N0]
    · exact ![I1579N0, I1579N1, I1579N2, I1579N3, I1579N4]
    · exact ![I1583N0, I1583N1]
    · exact ![I1597N0, I1597N1]
    · exact ![I1601N0]
    · exact ![I1607N0, I1607N1]
    · exact ![I1609N0]
    · exact ![I1613N0, I1613N1, I1613N2, I1613N3]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC1499
    · exact PBC1511
    · exact PBC1523
    · exact PBC1531
    · exact PBC1543
    · exact PBC1549
    · exact PBC1553
    · exact PBC1559
    · exact PBC1567
    · exact PBC1571
    · exact PBC1579
    · exact PBC1583
    · exact PBC1597
    · exact PBC1601
    · exact PBC1607
    · exact PBC1609
    · exact PBC1613
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2247001, 2247001, 1499]
    · exact ![3449795831, 1511, 1511]
    · exact ![3532642667, 2319529]
    · exact ![3588604291, 1531, 1531]
    · exact ![5668441960801, 1543]
    · exact ![8917786870982749]
    · exact ![5816822652481, 1553]
    · exact ![2430481, 2430481, 1559]
    · exact ![6029426229121, 1567]
    · exact ![9569316639336851]
    · exact ![1579, 1579, 1579, 1579, 1579]
    · exact ![6279479680321, 1583]
    · exact ![4073003173, 2550409]
    · exact ![10518568985608001]
    · exact ![4149995543, 2582449]
    · exact ![10784008474947049]
    · exact ![2601769, 1613, 1613, 1613]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI1499N0
      exact NI1499N1
      exact NI1499N2
    · dsimp ; intro j
      fin_cases j
      exact NI1511N0
      exact NI1511N1
      exact NI1511N2
    · dsimp ; intro j
      fin_cases j
      exact NI1523N0
      exact NI1523N1
    · dsimp ; intro j
      fin_cases j
      exact NI1531N0
      exact NI1531N1
      exact NI1531N2
    · dsimp ; intro j
      fin_cases j
      exact NI1543N0
      exact NI1543N1
    · dsimp ; intro j
      fin_cases j
      exact NI1549N0
    · dsimp ; intro j
      fin_cases j
      exact NI1553N0
      exact NI1553N1
    · dsimp ; intro j
      fin_cases j
      exact NI1559N0
      exact NI1559N1
      exact NI1559N2
    · dsimp ; intro j
      fin_cases j
      exact NI1567N0
      exact NI1567N1
    · dsimp ; intro j
      fin_cases j
      exact NI1571N0
    · dsimp ; intro j
      fin_cases j
      exact NI1579N0
      exact NI1579N1
      exact NI1579N2
      exact NI1579N3
      exact NI1579N4
    · dsimp ; intro j
      fin_cases j
      exact NI1583N0
      exact NI1583N1
    · dsimp ; intro j
      fin_cases j
      exact NI1597N0
      exact NI1597N1
    · dsimp ; intro j
      fin_cases j
      exact NI1601N0
    · dsimp ; intro j
      fin_cases j
      exact NI1607N0
      exact NI1607N1
    · dsimp ; intro j
      fin_cases j
      exact NI1609N0
    · dsimp ; intro j
      fin_cases j
      exact NI1613N0
      exact NI1613N1
      exact NI1613N2
      exact NI1613N3
  Il := ![[I1499N2], [I1511N1, I1511N2], [], [I1531N1, I1531N2], [I1543N1], [], [I1553N1], [I1559N2], [I1567N1], [], [I1579N0, I1579N1, I1579N2, I1579N3, I1579N4], [I1583N1], [], [], [], [], [I1613N1, I1613N2, I1613N3]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

lemma PB2193I15_primes :
  ∀ (p : ℕ), p ∈ Set.range ![1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747] ↔ Nat.Prime p ∧ 1613 < p ∧ p ≤ 1747 := by
  simp_rw [← List.mem_ofFn']
  convert PrimeSieve_mem_of_primesBelow _ 10000 _ ?_ _ _ primes_below_100_proof
  decide ; omega ; omega

def PB2193I15 : PrimesBelowBoundCertificateInterval O 1613 1747 2193 where
  m := 17
  g := ![3, 3, 4, 4, 2, 2, 2, 1, 2, 2, 3, 1, 1, 2, 2, 3, 2]
  P := ![1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747]
  hP := PB2193I15_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I1619N0, I1619N1, I1619N2]
    · exact ![I1621N0, I1621N1, I1621N2]
    · exact ![I1627N0, I1627N1, I1627N2, I1627N3]
    · exact ![I1637N0, I1637N1, I1637N2, I1637N3]
    · exact ![I1657N0, I1657N1]
    · exact ![I1663N0, I1663N1]
    · exact ![I1667N0, I1667N1]
    · exact ![I1669N0]
    · exact ![I1693N0, I1693N1]
    · exact ![I1697N0, I1697N1]
    · exact ![I1699N0, I1699N1, I1699N2]
    · exact ![I1709N0]
    · exact ![I1721N0]
    · exact ![I1723N0, I1723N1]
    · exact ![I1733N0, I1733N1]
    · exact ![I1741N0, I1741N1, I1741N2]
    · exact ![I1747N0, I1747N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC1619
    · exact PBC1621
    · exact PBC1627
    · exact PBC1637
    · exact PBC1657
    · exact PBC1663
    · exact PBC1667
    · exact PBC1669
    · exact PBC1693
    · exact PBC1697
    · exact PBC1699
    · exact PBC1709
    · exact PBC1721
    · exact PBC1723
    · exact PBC1733
    · exact PBC1741
    · exact PBC1747
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2621161, 2621161, 1619]
    · exact ![4259406061, 1621, 1621]
    · exact ![2647129, 1627, 1627, 1627]
    · exact ![2679769, 1637, 1637, 1637]
    · exact ![7538588431201, 1657]
    · exact ![7648371893761, 1663]
    · exact ![4632407963, 2778889]
    · exact ![12950355291399349]
    · exact ![4852559557, 2866249]
    · exact ![4887035873, 2879809]
    · exact ![4904335099, 1699, 1699]
    · exact ![14578415153927549]
    · exact ![15097476130072601]
    · exact ![8813351875441, 1723]
    · exact ![9019744817521, 1733]
    · exact ![5277112021, 1741, 1741]
    · exact ![9314758936081, 1747]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI1619N0
      exact NI1619N1
      exact NI1619N2
    · dsimp ; intro j
      fin_cases j
      exact NI1621N0
      exact NI1621N1
      exact NI1621N2
    · dsimp ; intro j
      fin_cases j
      exact NI1627N0
      exact NI1627N1
      exact NI1627N2
      exact NI1627N3
    · dsimp ; intro j
      fin_cases j
      exact NI1637N0
      exact NI1637N1
      exact NI1637N2
      exact NI1637N3
    · dsimp ; intro j
      fin_cases j
      exact NI1657N0
      exact NI1657N1
    · dsimp ; intro j
      fin_cases j
      exact NI1663N0
      exact NI1663N1
    · dsimp ; intro j
      fin_cases j
      exact NI1667N0
      exact NI1667N1
    · dsimp ; intro j
      fin_cases j
      exact NI1669N0
    · dsimp ; intro j
      fin_cases j
      exact NI1693N0
      exact NI1693N1
    · dsimp ; intro j
      fin_cases j
      exact NI1697N0
      exact NI1697N1
    · dsimp ; intro j
      fin_cases j
      exact NI1699N0
      exact NI1699N1
      exact NI1699N2
    · dsimp ; intro j
      fin_cases j
      exact NI1709N0
    · dsimp ; intro j
      fin_cases j
      exact NI1721N0
    · dsimp ; intro j
      fin_cases j
      exact NI1723N0
      exact NI1723N1
    · dsimp ; intro j
      fin_cases j
      exact NI1733N0
      exact NI1733N1
    · dsimp ; intro j
      fin_cases j
      exact NI1741N0
      exact NI1741N1
      exact NI1741N2
    · dsimp ; intro j
      fin_cases j
      exact NI1747N0
      exact NI1747N1
  Il := ![[I1619N2], [I1621N1, I1621N2], [I1627N1, I1627N2, I1627N3], [I1637N1, I1637N2, I1637N3], [I1657N1], [I1663N1], [], [], [], [], [I1699N1, I1699N2], [], [], [I1723N1], [I1733N1], [I1741N1, I1741N2], [I1747N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

lemma PB2193I16_primes :
  ∀ (p : ℕ), p ∈ Set.range ![1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879] ↔ Nat.Prime p ∧ 1747 < p ∧ p ≤ 1879 := by
  simp_rw [← List.mem_ofFn']
  convert PrimeSieve_mem_of_primesBelow _ 10000 _ ?_ _ _ primes_below_100_proof
  decide ; omega ; omega

def PB2193I16 : PrimesBelowBoundCertificateInterval O 1747 1879 2193 where
  m := 17
  g := ![2, 3, 4, 4, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 3]
  P := ![1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879]
  hP := PB2193I16_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I1753N0, I1753N1]
    · exact ![I1759N0, I1759N1, I1759N2]
    · exact ![I1777N0, I1777N1, I1777N2, I1777N3]
    · exact ![I1783N0, I1783N1, I1783N2, I1783N3]
    · exact ![I1787N0, I1787N1]
    · exact ![I1789N0]
    · exact ![I1801N0]
    · exact ![I1811N0]
    · exact ![I1823N0, I1823N1]
    · exact ![I1831N0, I1831N1, I1831N2]
    · exact ![I1847N0, I1847N1]
    · exact ![I1861N0, I1861N1, I1861N2]
    · exact ![I1867N0, I1867N1]
    · exact ![I1871N0]
    · exact ![I1873N0, I1873N1]
    · exact ![I1877N0, I1877N1]
    · exact ![I1879N0, I1879N1, I1879N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC1753
    · exact PBC1759
    · exact PBC1777
    · exact PBC1783
    · exact PBC1787
    · exact PBC1789
    · exact PBC1801
    · exact PBC1811
    · exact PBC1823
    · exact PBC1831
    · exact PBC1847
    · exact PBC1861
    · exact PBC1867
    · exact PBC1871
    · exact PBC1873
    · exact PBC1877
    · exact PBC1879
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![5386984777, 3073009]
    · exact ![5442488479, 1759, 1759]
    · exact ![3157729, 1777, 1777, 1777]
    · exact ![3179089, 1783, 1783, 1783]
    · exact ![10197605570161, 1787]
    · exact ![18325325727207949]
    · exact ![18948226352409001]
    · exact ![19480147976330051]
    · exact ![11044515642241, 1823]
    · exact ![6138539191, 1831, 1831]
    · exact ![11637711365281, 1847]
    · exact ![6445240381, 1861, 1861]
    · exact ![6507781363, 3485689]
    · exact ![22928145945758351]
    · exact ![6570725617, 3508129]
    · exact ![12412437950641, 1877]
    · exact ![6634074439, 1879, 1879]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI1753N0
      exact NI1753N1
    · dsimp ; intro j
      fin_cases j
      exact NI1759N0
      exact NI1759N1
      exact NI1759N2
    · dsimp ; intro j
      fin_cases j
      exact NI1777N0
      exact NI1777N1
      exact NI1777N2
      exact NI1777N3
    · dsimp ; intro j
      fin_cases j
      exact NI1783N0
      exact NI1783N1
      exact NI1783N2
      exact NI1783N3
    · dsimp ; intro j
      fin_cases j
      exact NI1787N0
      exact NI1787N1
    · dsimp ; intro j
      fin_cases j
      exact NI1789N0
    · dsimp ; intro j
      fin_cases j
      exact NI1801N0
    · dsimp ; intro j
      fin_cases j
      exact NI1811N0
    · dsimp ; intro j
      fin_cases j
      exact NI1823N0
      exact NI1823N1
    · dsimp ; intro j
      fin_cases j
      exact NI1831N0
      exact NI1831N1
      exact NI1831N2
    · dsimp ; intro j
      fin_cases j
      exact NI1847N0
      exact NI1847N1
    · dsimp ; intro j
      fin_cases j
      exact NI1861N0
      exact NI1861N1
      exact NI1861N2
    · dsimp ; intro j
      fin_cases j
      exact NI1867N0
      exact NI1867N1
    · dsimp ; intro j
      fin_cases j
      exact NI1871N0
    · dsimp ; intro j
      fin_cases j
      exact NI1873N0
      exact NI1873N1
    · dsimp ; intro j
      fin_cases j
      exact NI1877N0
      exact NI1877N1
    · dsimp ; intro j
      fin_cases j
      exact NI1879N0
      exact NI1879N1
      exact NI1879N2
  Il := ![[], [I1759N1, I1759N2], [I1777N1, I1777N2, I1777N3], [I1783N1, I1783N2, I1783N3], [I1787N1], [], [], [], [I1823N1], [I1831N1, I1831N2], [I1847N1], [I1861N1, I1861N2], [], [], [], [I1877N1], [I1879N1, I1879N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

lemma PB2193I17_primes :
  ∀ (p : ℕ), p ∈ Set.range ![1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017] ↔ Nat.Prime p ∧ 1879 < p ∧ p ≤ 2017 := by
  simp_rw [← List.mem_ofFn']
  convert PrimeSieve_mem_of_primesBelow _ 10000 _ ?_ _ _ primes_below_100_proof
  decide ; omega ; omega

def PB2193I17 : PrimesBelowBoundCertificateInterval O 1879 2017 2193 where
  m := 17
  g := ![3, 3, 2, 2, 3, 2, 3, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2]
  P := ![1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017]
  hP := PB2193I17_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I1889N0, I1889N1, I1889N2]
    · exact ![I1901N0, I1901N1, I1901N2]
    · exact ![I1907N0, I1907N1]
    · exact ![I1913N0, I1913N1]
    · exact ![I1931N0, I1931N1, I1931N2]
    · exact ![I1933N0, I1933N1]
    · exact ![I1949N0, I1949N1, I1949N2]
    · exact ![I1951N0]
    · exact ![I1973N0, I1973N1]
    · exact ![I1979N0]
    · exact ![I1987N0, I1987N1]
    · exact ![I1993N0, I1993N1]
    · exact ![I1997N0, I1997N1]
    · exact ![I1999N0]
    · exact ![I2003N0, I2003N1]
    · exact ![I2011N0]
    · exact ![I2017N0, I2017N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC1889
    · exact PBC1901
    · exact PBC1907
    · exact PBC1913
    · exact PBC1931
    · exact PBC1933
    · exact PBC1949
    · exact PBC1951
    · exact PBC1973
    · exact PBC1979
    · exact PBC1987
    · exact PBC1993
    · exact PBC1997
    · exact PBC1999
    · exact PBC2003
    · exact PBC2011
    · exact PBC2017
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![6740558369, 1889, 1889]
    · exact ![3613801, 3613801, 1901]
    · exact ![6935089643, 3636649]
    · exact ![13392445265761, 1913]
    · exact ![7200237491, 1931, 1931]
    · exact ![13961350047121, 1933]
    · exact ![3798601, 3798601, 1949]
    · exact ![28267431405534751]
    · exact ![15153339067441, 1973]
    · exact ![30354911500725899]
    · exact ![15588038452561, 1987]
    · exact ![7916293657, 3972049]
    · exact ![7964053973, 3988009]
    · exact ![31920079960009999]
    · exact ![16096216216081, 2003]
    · exact ![32889733386571051]
    · exact ![16550975387521, 2017]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI1889N0
      exact NI1889N1
      exact NI1889N2
    · dsimp ; intro j
      fin_cases j
      exact NI1901N0
      exact NI1901N1
      exact NI1901N2
    · dsimp ; intro j
      fin_cases j
      exact NI1907N0
      exact NI1907N1
    · dsimp ; intro j
      fin_cases j
      exact NI1913N0
      exact NI1913N1
    · dsimp ; intro j
      fin_cases j
      exact NI1931N0
      exact NI1931N1
      exact NI1931N2
    · dsimp ; intro j
      fin_cases j
      exact NI1933N0
      exact NI1933N1
    · dsimp ; intro j
      fin_cases j
      exact NI1949N0
      exact NI1949N1
      exact NI1949N2
    · dsimp ; intro j
      fin_cases j
      exact NI1951N0
    · dsimp ; intro j
      fin_cases j
      exact NI1973N0
      exact NI1973N1
    · dsimp ; intro j
      fin_cases j
      exact NI1979N0
    · dsimp ; intro j
      fin_cases j
      exact NI1987N0
      exact NI1987N1
    · dsimp ; intro j
      fin_cases j
      exact NI1993N0
      exact NI1993N1
    · dsimp ; intro j
      fin_cases j
      exact NI1997N0
      exact NI1997N1
    · dsimp ; intro j
      fin_cases j
      exact NI1999N0
    · dsimp ; intro j
      fin_cases j
      exact NI2003N0
      exact NI2003N1
    · dsimp ; intro j
      fin_cases j
      exact NI2011N0
    · dsimp ; intro j
      fin_cases j
      exact NI2017N0
      exact NI2017N1
  Il := ![[I1889N1, I1889N2], [I1901N2], [], [I1913N1], [I1931N1, I1931N2], [I1933N1], [I1949N2], [], [I1973N1], [], [I1987N1], [], [], [], [I2003N1], [], [I2017N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

lemma PB2193I18_primes :
  ∀ (p : ℕ), p ∈ Set.range ![2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179] ↔ Nat.Prime p ∧ 2017 < p ∧ p ≤ 2192 := by
  simp_rw [← List.mem_ofFn']
  convert PrimeSieve_mem_of_primesBelow _ 10000 _ ?_ _ _ primes_below_100_proof
  decide ; omega ; omega

def PB2193I18 : PrimesBelowBoundCertificateInterval O 2017 2192 2193 where
  m := 21
  g := ![2, 1, 3, 4, 2, 3, 1, 2, 4, 3, 1, 3, 2, 1, 1, 2, 1, 2, 2, 5, 3]
  P := ![2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179]
  hP := PB2193I18_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2027N0, I2027N1]
    · exact ![I2029N0]
    · exact ![I2039N0, I2039N1, I2039N2]
    · exact ![I2053N0, I2053N1, I2053N2, I2053N3]
    · exact ![I2063N0, I2063N1]
    · exact ![I2069N0, I2069N1, I2069N2]
    · exact ![I2081N0]
    · exact ![I2083N0, I2083N1]
    · exact ![I2087N0, I2087N1, I2087N2, I2087N3]
    · exact ![I2089N0, I2089N1, I2089N2]
    · exact ![I2099N0]
    · exact ![I2111N0, I2111N1, I2111N2]
    · exact ![I2113N0, I2113N1]
    · exact ![I2129N0]
    · exact ![I2131N0]
    · exact ![I2137N0, I2137N1]
    · exact ![I2141N0]
    · exact ![I2143N0, I2143N1]
    · exact ![I2153N0, I2153N1]
    · exact ![I2161N0, I2161N1, I2161N2, I2161N3, I2161N4]
    · exact ![I2179N0, I2179N1, I2179N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2027
    · exact PBC2029
    · exact PBC2039
    · exact PBC2053
    · exact PBC2063
    · exact PBC2069
    · exact PBC2081
    · exact PBC2083
    · exact PBC2087
    · exact PBC2089
    · exact PBC2099
    · exact PBC2111
    · exact PBC2113
    · exact PBC2129
    · exact PBC2131
    · exact PBC2137
    · exact PBC2141
    · exact PBC2143
    · exact PBC2153
    · exact PBC2161
    · exact PBC2179
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![16881653995441, 2027]
    · exact ![34388262653321149]
    · exact ![4157521, 4157521, 2039]
    · exact ![4214809, 2053, 2053, 2053]
    · exact ![18113272128961, 2063]
    · exact ![4280761, 4280761, 2069]
    · exact ![39026571593994401]
    · exact ![9037905787, 4338889]
    · exact ![4355569, 2087, 2087, 2087]
    · exact ![9116230969, 2089, 2089]
    · exact ![40743862065910499]
    · exact ![9407293631, 2111, 2111]
    · exact ![19934162223361, 2113]
    · exact ![43739952511861649]
    · exact ![43945787218699651]
    · exact ![20855379099361, 2137]
    · exact ![44986617112446701]
    · exact ![21090587817601, 2143]
    · exact ![21487016597281, 2153]
    · exact ![2161, 2161, 2161, 2161, 2161]
    · exact ![10345981339, 2179, 2179]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2027N0
      exact NI2027N1
    · dsimp ; intro j
      fin_cases j
      exact NI2029N0
    · dsimp ; intro j
      fin_cases j
      exact NI2039N0
      exact NI2039N1
      exact NI2039N2
    · dsimp ; intro j
      fin_cases j
      exact NI2053N0
      exact NI2053N1
      exact NI2053N2
      exact NI2053N3
    · dsimp ; intro j
      fin_cases j
      exact NI2063N0
      exact NI2063N1
    · dsimp ; intro j
      fin_cases j
      exact NI2069N0
      exact NI2069N1
      exact NI2069N2
    · dsimp ; intro j
      fin_cases j
      exact NI2081N0
    · dsimp ; intro j
      fin_cases j
      exact NI2083N0
      exact NI2083N1
    · dsimp ; intro j
      fin_cases j
      exact NI2087N0
      exact NI2087N1
      exact NI2087N2
      exact NI2087N3
    · dsimp ; intro j
      fin_cases j
      exact NI2089N0
      exact NI2089N1
      exact NI2089N2
    · dsimp ; intro j
      fin_cases j
      exact NI2099N0
    · dsimp ; intro j
      fin_cases j
      exact NI2111N0
      exact NI2111N1
      exact NI2111N2
    · dsimp ; intro j
      fin_cases j
      exact NI2113N0
      exact NI2113N1
    · dsimp ; intro j
      fin_cases j
      exact NI2129N0
    · dsimp ; intro j
      fin_cases j
      exact NI2131N0
    · dsimp ; intro j
      fin_cases j
      exact NI2137N0
      exact NI2137N1
    · dsimp ; intro j
      fin_cases j
      exact NI2141N0
    · dsimp ; intro j
      fin_cases j
      exact NI2143N0
      exact NI2143N1
    · dsimp ; intro j
      fin_cases j
      exact NI2153N0
      exact NI2153N1
    · dsimp ; intro j
      fin_cases j
      exact NI2161N0
      exact NI2161N1
      exact NI2161N2
      exact NI2161N3
      exact NI2161N4
    · dsimp ; intro j
      fin_cases j
      exact NI2179N0
      exact NI2179N1
      exact NI2179N2
  Il := ![[I2027N1], [], [I2039N2], [I2053N1, I2053N2, I2053N3], [I2063N1], [I2069N2], [], [], [I2087N1, I2087N2, I2087N3], [I2089N1, I2089N2], [], [I2111N1, I2111N2], [I2113N1], [], [], [I2137N1], [], [I2143N1], [I2153N1], [I2161N0, I2161N1, I2161N2, I2161N3, I2161N4], [I2179N1, I2179N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

def PB2193 : PrimesBelowBoundCertificate O 2193 := by
  refine primesBelowBoundCertificate_of_Interval O ![1, 59, 139, 233, 337, 439, 557, 653, 769, 883, 1013, 1117, 1249, 1381, 1493, 1613, 1747, 1879, 2017, 2192] 2192 rfl rfl ?_ ?_
  · decide
  · intro i
    match i with 
    | 0 => exact PB2193I0
    | 1 => exact PB2193I1
    | 2 => exact PB2193I2
    | 3 => exact PB2193I3
    | 4 => exact PB2193I4
    | 5 => exact PB2193I5
    | 6 => exact PB2193I6
    | 7 => exact PB2193I7
    | 8 => exact PB2193I8
    | 9 => exact PB2193I9
    | 10 => exact PB2193I10
    | 11 => exact PB2193I11
    | 12 => exact PB2193I12
    | 13 => exact PB2193I13
    | 14 => exact PB2193I14
    | 15 => exact PB2193I15
    | 16 => exact PB2193I16
    | 17 => exact PB2193I17
    | 18 => exact PB2193I18
