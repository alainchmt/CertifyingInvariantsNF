import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F0
import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F1
import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F2
import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F3
import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F4
import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F5
import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F6
import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F7
import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F8
import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F9
import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F10
import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F11
import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F12
import IdealArithmetic.Computation.PrimeSieve

noncomputable section

lemma PB692I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 59 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 59 (by omega)

def PB692I0 : PrimesBelowBoundCertificateInterval O 1 59 692 where
  m := 17
  g := ![1, 3, 3, 2, 2, 2, 3, 2, 2, 2, 2, 2, 1, 3, 2, 3, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59]
  hP := PB692I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0]
    · exact ![I3N0, I3N1, I3N2]
    · exact ![I5N0, I5N1, I5N2]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1]
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1]
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0]
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
    · exact ![16]
    · exact ![9, 3, 3]
    · exact ![25, 5, 5]
    · exact ![49, 49]
    · exact ![121, 121]
    · exact ![169, 169]
    · exact ![289, 17, 17]
    · exact ![361, 361]
    · exact ![529, 529]
    · exact ![841, 841]
    · exact ![961, 961]
    · exact ![1369, 1369]
    · exact ![2825761]
    · exact ![1849, 43, 43]
    · exact ![2209, 2209]
    · exact ![2809, 53, 53]
    · exact ![12117361]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
      exact NI3N2
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
      exact NI5N2
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
  Il := ![[I2N0], [I3N0, I3N1, I3N2], [I5N0, I5N1, I5N2], [I7N0, I7N1], [I11N0, I11N1], [I13N0, I13N1], [I17N0, I17N1, I17N1], [I19N0, I19N1], [I23N0, I23N1], [], [], [], [], [I43N1, I43N2], [], [I53N1, I53N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

lemma PB692I1_primes (p : ℕ) :
  p ∈ Set.range ![61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139] ↔ Nat.Prime p ∧ 59 < p ∧ p ≤ 139 := by
  rw [← List.mem_ofFn']
  convert primes_range 59 139 (by omega)

def PB692I1 : PrimesBelowBoundCertificateInterval O 59 139 692 where
  m := 17
  g := ![3, 1, 2, 1, 2, 2, 1, 3, 1, 2, 1, 1, 1, 2, 1, 2, 2]
  P := ![61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139]
  hP := PB692I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I61N0, I61N1, I61N1]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
    · exact ![I79N0, I79N1]
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0]
    · exact ![I113N0]
    · exact ![I127N0, I127N1]
    · exact ![I131N0]
    · exact ![I137N0, I137N1]
    · exact ![I139N0, I139N1]
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
    · exact ![3721, 61, 61]
    · exact ![20151121]
    · exact ![5041, 5041]
    · exact ![28398241]
    · exact ![6241, 6241]
    · exact ![6889, 6889]
    · exact ![62742241]
    · exact ![9409, 97, 97]
    · exact ![104060401]
    · exact ![10609, 10609]
    · exact ![131079601]
    · exact ![141158161]
    · exact ![163047361]
    · exact ![16129, 16129]
    · exact ![294499921]
    · exact ![18769, 18769]
    · exact ![19321, 19321]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
  Il := ![[I61N1, I61N1], [], [], [], [], [], [], [I97N1, I97N2], [], [], [], [], [], [], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

lemma PB692I2_primes (p : ℕ) :
  p ∈ Set.range ![149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233] ↔ Nat.Prime p ∧ 139 < p ∧ p ≤ 233 := by
  rw [← List.mem_ofFn']
  convert primes_range 139 233 (by omega)

def PB692I2 : PrimesBelowBoundCertificateInterval O 139 233 692 where
  m := 17
  g := ![4, 3, 1, 1, 3, 4, 2, 4, 1, 4, 1, 1, 2, 1, 2, 4, 2]
  P := ![149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233]
  hP := PB692I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I149N0, I149N1, I149N2, I149N3]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0]
    · exact ![I163N0]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0, I173N1, I173N2, I173N3]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1, I181N2, I181N3]
    · exact ![I191N0]
    · exact ![I193N0, I193N1, I193N2, I193N3]
    · exact ![I197N0]
    · exact ![I199N0]
    · exact ![I211N0, I211N1]
    · exact ![I223N0]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N0, I229N1, I229N1]
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
    · exact ![149, 149, 149, 149]
    · exact ![22801, 151, 151]
    · exact ![607573201]
    · exact ![705911761]
    · exact ![27889, 167, 167]
    · exact ![173, 173, 173, 173]
    · exact ![32041, 32041]
    · exact ![181, 181, 181, 181]
    · exact ![1330863361]
    · exact ![193, 193, 193, 193]
    · exact ![1506138481]
    · exact ![1568239201]
    · exact ![44521, 44521]
    · exact ![2472973441]
    · exact ![51529, 51529]
    · exact ![229, 229, 229, 229]
    · exact ![54289, 54289]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
      exact NI149N2
      exact NI149N3
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
      exact NI167N2
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
      exact NI173N2
      exact NI173N3
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
      exact NI181N2
      exact NI181N3
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
      exact NI193N2
      exact NI193N3
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N0
      exact NI229N1
      exact NI229N1
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
  Il := ![[I149N0, I149N1, I149N2, I149N3], [I151N1, I151N2], [], [], [I167N1, I167N2], [I173N0, I173N1, I173N2, I173N3], [], [I181N0, I181N1, I181N2, I181N3], [], [I193N0, I193N1, I193N2, I193N3], [], [], [], [], [], [I229N0, I229N0, I229N1, I229N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

lemma PB692I3_primes (p : ℕ) :
  p ∈ Set.range ![239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337] ↔ Nat.Prime p ∧ 233 < p ∧ p ≤ 337 := by
  rw [← List.mem_ofFn']
  convert primes_range 233 337 (by omega)

def PB692I3 : PrimesBelowBoundCertificateInterval O 233 337 692 where
  m := 17
  g := ![2, 3, 1, 2, 2, 1, 2, 4, 1, 1, 2, 3, 4, 2, 1, 1, 2]
  P := ![239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337]
  hP := PB692I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I239N0, I239N1]
    · exact ![I241N0, I241N1, I241N2]
    · exact ![I251N0]
    · exact ![I257N0, I257N1]
    · exact ![I263N0, I263N1]
    · exact ![I269N0]
    · exact ![I271N0, I271N1]
    · exact ![I277N0, I277N1, I277N2, I277N3]
    · exact ![I281N0]
    · exact ![I283N0]
    · exact ![I293N0, I293N1]
    · exact ![I307N0, I307N1, I307N2]
    · exact ![I311N0, I311N1, I311N2, I311N3]
    · exact ![I313N0, I313N1]
    · exact ![I317N0]
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
    · exact ![57121, 57121]
    · exact ![58081, 241, 241]
    · exact ![3969126001]
    · exact ![66049, 66049]
    · exact ![69169, 69169]
    · exact ![5236114321]
    · exact ![73441, 73441]
    · exact ![277, 277, 277, 277]
    · exact ![6234839521]
    · exact ![6414247921]
    · exact ![85849, 85849]
    · exact ![94249, 307, 307]
    · exact ![311, 311, 311, 311]
    · exact ![97969, 97969]
    · exact ![10098039121]
    · exact ![12003612721]
    · exact ![113569, 113569]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
      exact NI241N1
      exact NI241N2
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
      exact NI271N1
    · dsimp ; intro j
      fin_cases j
      exact NI277N0
      exact NI277N1
      exact NI277N2
      exact NI277N3
    · dsimp ; intro j
      fin_cases j
      exact NI281N0
    · dsimp ; intro j
      fin_cases j
      exact NI283N0
    · dsimp ; intro j
      fin_cases j
      exact NI293N0
      exact NI293N1
    · dsimp ; intro j
      fin_cases j
      exact NI307N0
      exact NI307N1
      exact NI307N2
    · dsimp ; intro j
      fin_cases j
      exact NI311N0
      exact NI311N1
      exact NI311N2
      exact NI311N3
    · dsimp ; intro j
      fin_cases j
      exact NI313N0
      exact NI313N1
    · dsimp ; intro j
      fin_cases j
      exact NI317N0
    · dsimp ; intro j
      fin_cases j
      exact NI331N0
    · dsimp ; intro j
      fin_cases j
      exact NI337N0
      exact NI337N1
  Il := ![[], [I241N1, I241N2], [], [], [], [], [], [I277N0, I277N1, I277N2, I277N3], [], [], [], [I307N1, I307N2], [I311N0, I311N1, I311N2, I311N3], [], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

lemma PB692I4_primes (p : ℕ) :
  p ∈ Set.range ![347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439] ↔ Nat.Prime p ∧ 337 < p ∧ p ≤ 439 := by
  rw [← List.mem_ofFn']
  convert primes_range 337 439 (by omega)

def PB692I4 : PrimesBelowBoundCertificateInterval O 337 439 692 where
  m := 17
  g := ![3, 1, 2, 3, 3, 3, 1, 3, 1, 2, 4, 3, 2, 3, 3, 3, 3]
  P := ![347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439]
  hP := PB692I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I347N0, I347N1, I347N2]
    · exact ![I349N0]
    · exact ![I353N0, I353N1]
    · exact ![I359N0, I359N1, I359N2]
    · exact ![I367N0, I367N1, I367N2]
    · exact ![I373N0, I373N1, I373N2]
    · exact ![I379N0]
    · exact ![I383N0, I383N1, I383N2]
    · exact ![I389N0]
    · exact ![I397N0, I397N1]
    · exact ![I401N0, I401N1, I401N2, I401N3]
    · exact ![I409N0, I409N1, I409N2]
    · exact ![I419N0, I419N1]
    · exact ![I421N0, I421N1, I421N2]
    · exact ![I431N0, I431N1, I431N2]
    · exact ![I433N0, I433N1, I433N2]
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
    · exact ![120409, 347, 347]
    · exact ![14835483601]
    · exact ![124609, 124609]
    · exact ![128881, 359, 359]
    · exact ![134689, 367, 367]
    · exact ![139129, 373, 373]
    · exact ![20632736881]
    · exact ![383, 146689, 383]
    · exact ![22898045041]
    · exact ![157609, 157609]
    · exact ![401, 401, 401, 401]
    · exact ![167281, 409, 409]
    · exact ![175561, 175561]
    · exact ![177241, 421, 421]
    · exact ![185761, 431, 431]
    · exact ![187489, 433, 433]
    · exact ![192721, 439, 439]
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI347N0
      exact NI347N1
      exact NI347N2
    · dsimp ; intro j
      fin_cases j
      exact NI349N0
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
      exact NI367N2
    · dsimp ; intro j
      fin_cases j
      exact NI373N0
      exact NI373N1
      exact NI373N2
    · dsimp ; intro j
      fin_cases j
      exact NI379N0
    · dsimp ; intro j
      fin_cases j
      exact NI383N0
      exact NI383N1
      exact NI383N2
    · dsimp ; intro j
      fin_cases j
      exact NI389N0
    · dsimp ; intro j
      fin_cases j
      exact NI397N0
      exact NI397N1
    · dsimp ; intro j
      fin_cases j
      exact NI401N0
      exact NI401N1
      exact NI401N2
      exact NI401N3
    · dsimp ; intro j
      fin_cases j
      exact NI409N0
      exact NI409N1
      exact NI409N2
    · dsimp ; intro j
      fin_cases j
      exact NI419N0
      exact NI419N1
    · dsimp ; intro j
      fin_cases j
      exact NI421N0
      exact NI421N1
      exact NI421N2
    · dsimp ; intro j
      fin_cases j
      exact NI431N0
      exact NI431N1
      exact NI431N2
    · dsimp ; intro j
      fin_cases j
      exact NI433N0
      exact NI433N1
      exact NI433N2
    · dsimp ; intro j
      fin_cases j
      exact NI439N0
      exact NI439N1
      exact NI439N2
  Il := ![[I347N1, I347N2], [], [], [I359N1, I359N2], [I367N1, I367N2], [I373N1, I373N2], [], [I383N0, I383N2], [], [], [I401N0, I401N1, I401N2, I401N3], [I409N1, I409N2], [], [I421N1, I421N2], [I431N1, I431N2], [I433N1, I433N2], [I439N1, I439N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

lemma PB692I5_primes (p : ℕ) :
  p ∈ Set.range ![443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557] ↔ Nat.Prime p ∧ 439 < p ∧ p ≤ 557 := by
  rw [← List.mem_ofFn']
  convert primes_range 439 557 (by omega)

def PB692I5 : PrimesBelowBoundCertificateInterval O 439 557 692 where
  m := 17
  g := ![2, 3, 3, 2, 4, 3, 1, 1, 4, 2, 3, 3, 2, 1, 4, 2, 3]
  P := ![443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557]
  hP := PB692I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I443N0, I443N1]
    · exact ![I449N0, I449N1, I449N2]
    · exact ![I457N0, I457N1, I457N2]
    · exact ![I461N0, I461N1]
    · exact ![I463N0, I463N1, I463N2, I463N3]
    · exact ![I467N0, I467N1, I467N2]
    · exact ![I479N0]
    · exact ![I487N0]
    · exact ![I491N0, I491N1, I491N2, I491N3]
    · exact ![I499N0, I499N1]
    · exact ![I503N0, I503N1, I503N2]
    · exact ![I509N0, I509N1, I509N2]
    · exact ![I521N0, I521N1]
    · exact ![I523N0]
    · exact ![I541N0, I541N1, I541N2, I541N3]
    · exact ![I547N0, I547N1]
    · exact ![I557N0, I557N1, I557N2]
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
    · exact ![196249, 196249]
    · exact ![201601, 449, 449]
    · exact ![208849, 457, 457]
    · exact ![212521, 212521]
    · exact ![463, 463, 463, 463]
    · exact ![218089, 467, 467]
    · exact ![52643172481]
    · exact ![56249134561]
    · exact ![491, 491, 491, 491]
    · exact ![249001, 249001]
    · exact ![253009, 503, 503]
    · exact ![259081, 509, 509]
    · exact ![271441, 271441]
    · exact ![74818113841]
    · exact ![541, 541, 541, 541]
    · exact ![299209, 299209]
    · exact ![310249, 557, 557]
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
      exact NI457N2
    · dsimp ; intro j
      fin_cases j
      exact NI461N0
      exact NI461N1
    · dsimp ; intro j
      fin_cases j
      exact NI463N0
      exact NI463N1
      exact NI463N2
      exact NI463N3
    · dsimp ; intro j
      fin_cases j
      exact NI467N0
      exact NI467N1
      exact NI467N2
    · dsimp ; intro j
      fin_cases j
      exact NI479N0
    · dsimp ; intro j
      fin_cases j
      exact NI487N0
    · dsimp ; intro j
      fin_cases j
      exact NI491N0
      exact NI491N1
      exact NI491N2
      exact NI491N3
    · dsimp ; intro j
      fin_cases j
      exact NI499N0
      exact NI499N1
    · dsimp ; intro j
      fin_cases j
      exact NI503N0
      exact NI503N1
      exact NI503N2
    · dsimp ; intro j
      fin_cases j
      exact NI509N0
      exact NI509N1
      exact NI509N2
    · dsimp ; intro j
      fin_cases j
      exact NI521N0
      exact NI521N1
    · dsimp ; intro j
      fin_cases j
      exact NI523N0
    · dsimp ; intro j
      fin_cases j
      exact NI541N0
      exact NI541N1
      exact NI541N2
      exact NI541N3
    · dsimp ; intro j
      fin_cases j
      exact NI547N0
      exact NI547N1
    · dsimp ; intro j
      fin_cases j
      exact NI557N0
      exact NI557N1
      exact NI557N2
  Il := ![[], [I449N1, I449N2], [I457N1, I457N2], [], [I463N0, I463N1, I463N2, I463N3], [I467N1, I467N2], [], [], [I491N0, I491N1, I491N2, I491N3], [], [I503N1, I503N2], [I509N1, I509N2], [], [], [I541N0, I541N1, I541N2, I541N3], [], [I557N1, I557N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

lemma PB692I6_primes (p : ℕ) :
  p ∈ Set.range ![563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691] ↔ Nat.Prime p ∧ 557 < p ∧ p ≤ 691 := by
  rw [← List.mem_ofFn']
  convert primes_range 557 691 (by omega)

def PB692I6 : PrimesBelowBoundCertificateInterval O 557 691 692 where
  m := 23
  g := ![2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 4, 3, 3, 2, 2, 1, 2, 2, 3, 4, 2, 3, 3]
  P := ![563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691]
  hP := PB692I6_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I563N0, I563N1]
    · exact ![I569N0, I569N1]
    · exact ![I571N0]
    · exact ![I577N0]
    · exact ![I587N0, I587N1, I587N2]
    · exact ![I593N0, I593N1, I593N2]
    · exact ![I599N0]
    · exact ![I601N0]
    · exact ![I607N0, I607N1, I607N2]
    · exact ![I613N0, I613N1]
    · exact ![I617N0, I617N1, I617N2, I617N3]
    · exact ![I619N0, I619N1, I619N2]
    · exact ![I631N0, I631N1, I631N2]
    · exact ![I641N0, I641N1]
    · exact ![I643N0, I643N1]
    · exact ![I647N0]
    · exact ![I653N0, I653N1]
    · exact ![I659N0, I659N1]
    · exact ![I661N0, I661N1, I661N2]
    · exact ![I673N0, I673N1, I673N2, I673N3]
    · exact ![I677N0, I677N1]
    · exact ![I683N0, I683N1, I683N2]
    · exact ![I691N0, I691N1, I691N2]
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
    · exact PBC659
    · exact PBC661
    · exact PBC673
    · exact PBC677
    · exact PBC683
    · exact PBC691
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![316969, 316969]
    · exact ![323761, 323761]
    · exact ![106302733681]
    · exact ![110841719041]
    · exact ![344569, 587, 587]
    · exact ![351649, 593, 593]
    · exact ![128738157601]
    · exact ![130466162401]
    · exact ![368449, 607, 607]
    · exact ![375769, 375769]
    · exact ![617, 617, 617, 617]
    · exact ![383161, 619, 619]
    · exact ![398161, 631, 631]
    · exact ![410881, 410881]
    · exact ![413449, 413449]
    · exact ![175233494881]
    · exact ![426409, 426409]
    · exact ![434281, 434281]
    · exact ![436921, 661, 661]
    · exact ![673, 673, 673, 673]
    · exact ![458329, 458329]
    · exact ![466489, 683, 683]
    · exact ![477481, 691, 691]
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
      exact NI569N1
    · dsimp ; intro j
      fin_cases j
      exact NI571N0
    · dsimp ; intro j
      fin_cases j
      exact NI577N0
    · dsimp ; intro j
      fin_cases j
      exact NI587N0
      exact NI587N1
      exact NI587N2
    · dsimp ; intro j
      fin_cases j
      exact NI593N0
      exact NI593N1
      exact NI593N2
    · dsimp ; intro j
      fin_cases j
      exact NI599N0
    · dsimp ; intro j
      fin_cases j
      exact NI601N0
    · dsimp ; intro j
      fin_cases j
      exact NI607N0
      exact NI607N1
      exact NI607N2
    · dsimp ; intro j
      fin_cases j
      exact NI613N0
      exact NI613N1
    · dsimp ; intro j
      fin_cases j
      exact NI617N0
      exact NI617N1
      exact NI617N2
      exact NI617N3
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
    · dsimp ; intro j
      fin_cases j
      exact NI643N0
      exact NI643N1
    · dsimp ; intro j
      fin_cases j
      exact NI647N0
    · dsimp ; intro j
      fin_cases j
      exact NI653N0
      exact NI653N1
    · dsimp ; intro j
      fin_cases j
      exact NI659N0
      exact NI659N1
    · dsimp ; intro j
      fin_cases j
      exact NI661N0
      exact NI661N1
      exact NI661N2
    · dsimp ; intro j
      fin_cases j
      exact NI673N0
      exact NI673N1
      exact NI673N2
      exact NI673N3
    · dsimp ; intro j
      fin_cases j
      exact NI677N0
      exact NI677N1
    · dsimp ; intro j
      fin_cases j
      exact NI683N0
      exact NI683N1
      exact NI683N2
    · dsimp ; intro j
      fin_cases j
      exact NI691N0
      exact NI691N1
      exact NI691N2
  Il := ![[], [], [], [], [I587N1, I587N2], [I593N1, I593N2], [], [], [I607N1, I607N2], [], [I617N0, I617N1, I617N2, I617N3], [I619N1, I619N2], [I631N1, I631N2], [], [], [], [], [], [I661N1, I661N2], [I673N0, I673N1, I673N2, I673N3], [], [I683N1, I683N2], [I691N1, I691N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl

def PB692 : PrimesBelowBoundCertificate O 692 := by
  refine primesBelowBoundCertificate_of_Interval O ![1, 59, 139, 233, 337, 439, 557, 691] 691 rfl rfl ?_ ?_
  · decide
  · rintro ⟨i,hi⟩
    interval_cases i 
    exact PB692I0
    exact PB692I1
    exact PB692I2
    exact PB692I3
    exact PB692I4
    exact PB692I5
    exact PB692I6
