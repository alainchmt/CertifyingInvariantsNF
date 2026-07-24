
import IdealArithmetic.Examples.NF3_1_273239_1.RI3_1_273239_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39972, 1560, 4051]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![39972, 1560, 4051]] 
 ![![37, 0, 0], ![0, 37, 0], ![13, 25, 1]] where
  M :=![![![39972, 1560, 4051], ![409151, 15968, 41466], ![566711, 22117, 57434]]]
  hmulB := by decide  
  f := ![![![70, -29, 16]], ![![1616, 151, -223]], ![![1081, 98, -147]]]
  g := ![![![-343, -2695, 4051], ![-3511, -27586, 41466], ![-4863, -38209, 57434]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [7, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 36], [0, 1]]
 g := ![![[15, 16], [12], [3, 34], [36], [1]], ![[0, 21], [12], [22, 3], [36], [1]]]
 h' := ![![[6, 36], [24, 33], [16, 30], [19, 21], [30, 6], [0, 1]], ![[0, 1], [0, 4], [11, 7], [34, 16], [29, 31], [6, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [10, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [7, 31, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4047, 4114, -1089]
  a := ![0, 9, -20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![492, 847, -1089]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-70, 29, -16]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-70, 29, -16]] 
 ![![37, 0, 0], ![15, 1, 0], ![20, 0, 1]] where
  M :=![![![-70, 29, -16], ![-1616, -151, 223], ![1313, -228, 72]]]
  hmulB := by decide  
  f := ![![![-39972, -1560, -4051]], ![![-27263, -1064, -2763]], ![![-36923, -1441, -3742]]]
  g := ![![![-5, 29, -16], ![-103, -151, 223], ![89, -228, 72]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![39972, 1560, 4051]] ![![-70, 29, -16]]
  ![![37, 0, 0]] where
 M := ![![![-37, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-675, 5, 44]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-675, 5, 44]] 
 ![![41, 0, 0], ![0, 41, 0], ![21, 29, 1]] where
  M :=![![![-675, 5, 44], ![4444, -876, 319], ![4949, 288, -557]]]
  hmulB := by decide  
  f := ![![![-9660, -377, -979]], ![![-98879, -3859, -10021]], ![![-78227, -3053, -7928]]]
  g := ![![![-39, -31, 44], ![-55, -247, 319], ![406, 401, -557]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [17, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 40], [0, 1]]
 g := ![![[23, 16], [33], [37], [22, 33], [1]], ![[40, 25], [33], [37], [34, 8], [1]]]
 h' := ![![[19, 40], [11, 4], [11, 22], [36, 23], [24, 19], [0, 1]], ![[0, 1], [5, 37], [19, 19], [22, 18], [16, 22], [19, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [10, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [17, 22, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1511, 2030, 29]
  a := ![-1, -7, 15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![22, 29, 29]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9660, 377, 979]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![9660, 377, 979]] 
 ![![41, 0, 0], ![3, 1, 0], ![8, 0, 1]] where
  M :=![![![9660, 377, 979], ![98879, 3859, 10021], ![136956, 5345, 13880]]]
  hmulB := by decide  
  f := ![![![675, -5, -44]], ![![-59, 21, -11]], ![![11, -8, 5]]]
  g := ![![![17, 377, 979], ![174, 3859, 10021], ![241, 5345, 13880]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-675, 5, 44]] ![![9660, 377, 979]]
  ![![41, 0, 0]] where
 M := ![![![-41, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![68650, -10157, 2491]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![68650, -10157, 2491]] 
 ![![43, 0, 0], ![0, 43, 0], ![7, 3, 1]] where
  M :=![![![68650, -10157, 2491], ![251591, 109471, -96781], ![-774266, 58065, 12690]]]
  hmulB := by decide  
  f := ![![![162994785, 6361215, 16518892]], ![![1668408092, 65113142, 169086717]], ![![196676246, 7675705, 19932378]]]
  g := ![![![1191, -410, 2491], ![21606, 9298, -96781], ![-20072, 465, 12690]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [8, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 42], [0, 1]]
 g := ![![[35, 35], [40, 23], [6], [24, 11], [1]], ![[39, 8], [7, 20], [6], [40, 32], [1]]]
 h' := ![![[21, 42], [24, 32], [8, 18], [23, 7], [35, 21], [0, 1]], ![[0, 1], [8, 11], [42, 25], [41, 36], [3, 22], [21, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [42, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [8, 22, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2696, -67, 207]
  a := ![-64, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![29, -16, 207]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![162994785, 6361215, 16518892]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![162994785, 6361215, 16518892]] 
 ![![43, 0, 0], ![4, 1, 0], ![16, 0, 1]] where
  M :=![![![162994785, 6361215, 16518892], ![1668408092, 65113142, 169086717], ![2310890807, 90187384, 234199859]]]
  hmulB := by decide  
  f := ![![![68650, -10157, 2491]], ![![12237, 1601, -2019]], ![![7538, -2429, 1222]]]
  g := ![![![-2947729, 6361215, 16518892], ![-30172836, 65113142, 169086717], ![-41792011, 90187384, 234199859]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![68650, -10157, 2491]] ![![162994785, 6361215, 16518892]]
  ![![43, 0, 0]] where
 M := ![![![43, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3305, -129, -335]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-3305, -129, -335]] 
 ![![47, 0, 0], ![0, 47, 0], ![26, 45, 1]] where
  M :=![![![-3305, -129, -335], ![-33835, -1320, -3429], ![-46864, -1829, -4749]]]
  hmulB := by decide  
  f := ![![![63, -2, -3]], ![![-303, 85, -40]], ![![-266, 80, -39]]]
  g := ![![![115, 318, -335], ![1177, 3255, -3429], ![1630, 4508, -4749]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [15, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 46], [0, 1]]
 g := ![![[15, 8], [41, 9], [24, 34], [42, 6], [1]], ![[1, 39], [37, 38], [35, 13], [8, 41], [1]]]
 h' := ![![[10, 46], [43, 14], [16, 44], [28, 38], [32, 10], [0, 1]], ![[0, 1], [42, 33], [33, 3], [32, 9], [38, 37], [10, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [12, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [15, 37, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4901, 5968, -1621]
  a := ![1, 11, -24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1001, 1679, -1621]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![63, -2, -3]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![63, -2, -3]] 
 ![![47, 0, 0], ![16, 1, 0], ![31, 0, 1]] where
  M :=![![![63, -2, -3], ![-303, 85, -40], ![-505, -13, 45]]]
  hmulB := by decide  
  f := ![![![-3305, -129, -335]], ![![-1845, -72, -187]], ![![-3177, -124, -322]]]
  g := ![![![4, -2, -3], ![-9, 85, -40], ![-36, -13, 45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-3305, -129, -335]] ![![63, -2, -3]]
  ![![47, 0, 0]] where
 M := ![![![47, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-524, -61, 81]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-524, -61, 81]] 
 ![![53, 0, 0], ![24, 1, 0], ![26, 0, 1]] where
  M :=![![![-524, -61, 81], ![8181, -543, -185], ![2020, 811, -728]]]
  hmulB := by decide  
  f := ![![![-545339, -21283, -55268]], ![![-352268, -13748, -35701]], ![![-413405, -16134, -41897]]]
  g := ![![![-22, -61, 81], ![491, -543, -185], ![28, 811, -728]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![129, -50, 27]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![129, -50, 27]] 
 ![![53, 0, 0], ![32, 1, 0], ![13, 0, 1]] where
  M :=![![![129, -50, 27], ![2727, 271, -388], ![-2323, 389, -117]]]
  hmulB := by decide  
  f := ![![![-119225, -4653, -12083]], ![![-95011, -3708, -9629]], ![![-61137, -2386, -6196]]]
  g := ![![![26, -50, 27], ![-17, 271, -388], ![-250, 389, -117]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7538, 2429, -1222]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![-7538, 2429, -1222]] 
 ![![53, 0, 0], ![49, 1, 0], ![16, 0, 1]] where
  M :=![![![-7538, 2429, -1222], ![-123422, -14795, 19387], ![121907, -18270, 4592]]]
  hmulB := by decide  
  f := ![![![-286261850, -11171972, -29011533]], ![![-319943311, -12486462, -32425019]], ![![-162994785, -6361215, -16518892]]]
  g := ![![![-2019, 2429, -1222], ![5497, -14795, 19387], ![17805, -18270, 4592]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-524, -61, 81]] ![![129, -50, 27]]
  ![![-422106, 41178, 43]] where
 M := ![![![-422106, 41178, 43]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![-422106, 41178, 43]] ![![-7538, 2429, -1222]]
  ![![53, 0, 0]] where
 M := ![![![-1895194087, -1635309594, 1314328874]]]
 hmul := by decide  
 g := ![![![![-35758379, -30854898, 24798658]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [44, 11, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 35, 19], [56, 23, 40], [0, 1]]
 g := ![![[31, 3, 9], [24, 4, 46], [], [31, 46, 41], [1]], ![[23, 16, 45, 48], [1, 5, 39, 9], [7, 22], [29, 56, 17, 41], [42, 2, 54, 15]], ![[15, 17, 55, 55], [46, 49, 38, 33], [0, 22], [33, 29, 25, 38], [58, 22, 43, 44]]]
 h' := ![![[52, 35, 19], [6, 14, 56], [49, 47, 20], [52, 43], [15, 48, 49], [0, 1]], ![[56, 23, 40], [55, 37, 20], [38, 4, 55], [46, 30, 50], [51, 52, 33], [52, 35, 19]], ![[0, 1], [55, 8, 42], [29, 8, 43], [41, 45, 9], [17, 18, 36], [56, 23, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 47], []]
 b := ![[], [8, 35, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [44, 11, 10, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7185197, 291578, -172811]
  a := ![0, 9, -20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-121783, 4942, -2929]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [36, 2, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 38, 18], [28, 22, 43], [0, 1]]
 g := ![![[30, 6, 20], [52, 42], [37, 52, 36], [34, 40, 42], [1]], ![[32, 12, 36, 33], [10, 25], [3, 57, 16, 17], [38, 43], [36, 46, 25, 37]], ![[55, 33, 0, 35], [35, 39], [0, 21, 20, 18], [28, 26, 44, 37], [14, 5, 40, 24]]]
 h' := ![![[18, 38, 18], [58, 44, 52], [10, 22, 46], [57, 32, 55], [25, 59, 46], [0, 1]], ![[28, 22, 43], [28, 4, 45], [12, 8, 5], [24, 43, 17], [22, 11], [18, 38, 18]], ![[0, 1], [1, 13, 25], [23, 31, 10], [53, 47, 50], [37, 52, 15], [28, 22, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57, 9], []]
 b := ![[], [25, 9, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [36, 2, 15, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5441107707, -187965400, 134636089]
  a := ![1, -81, 182]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![89198487, -3081400, 2207149]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀

instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [10, 40, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 32, 42], [52, 34, 25], [0, 1]]
 g := ![![[63, 62, 55], [50, 51, 35], [41, 10], [39, 56], [25, 1], []], ![[58, 24, 60, 57], [29, 65, 58, 7], [59, 64], [31, 56], [9, 17], [22, 22]], ![[13, 26, 44, 22], [42, 31, 40, 39], [40, 16], [6, 23], [31, 19], [39, 22]]]
 h' := ![![[40, 32, 42], [36, 18, 51], [60, 25, 13], [1, 45, 55], [18, 62, 49], [0, 0, 1], [0, 1]], ![[52, 34, 25], [49, 63, 11], [39, 15, 18], [48, 0, 8], [36, 25, 49], [40, 53, 34], [40, 32, 42]], ![[0, 1], [61, 53, 5], [19, 27, 36], [33, 22, 4], [48, 47, 36], [36, 14, 32], [52, 34, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 2], []]
 b := ![[], [2, 36, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [10, 40, 42, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3807610, -38927, 88976]
  a := ![-1, -7, 16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![56830, -581, 1328]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def PBC67 : ContainsPrimesAboveP 67 ![I67N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![67, 0, 0]]) timesTableT_eq_Table B_one_repr 67 (by decide) 𝕀

instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6486, -1214, 419]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![6486, -1214, 419]] 
 ![![71, 0, 0], ![23, 1, 0], ![14, 0, 1]] where
  M :=![![![6486, -1214, 419], ![42319, 10880, -10840], ![-80295, 7789, 40]]]
  hmulB := by decide  
  f := ![![![-84867960, -3312151, -8601040]], ![![-39727720, -1550458, -4026251]], ![![-33681461, -1314490, -3413486]]]
  g := ![![![402, -1214, 419], ![-791, 10880, -10840], ![-3662, 7789, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![359671031, 14036920, 36451270]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![359671031, 14036920, 36451270]] 
 ![![71, 0, 0], ![57, 1, 0], ![21, 0, 1]] where
  M :=![![![359671031, 14036920, 36451270], ![3681578270, 143681351, 373113740], ![5099307190, 199011210, 516795091]]]
  hmulB := by decide  
  f := ![![![22541, -23020, 15030]], ![![39477, -17389, 9770]], ![![-4699, -4030, 3241]]]
  g := ![![![-16984649, 14036920, 36451270], ![-173854187, 143681351, 373113740], ![-240803221, 199011210, 516795091]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10, 1, 0]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![-10, 1, 0]] 
 ![![71, 0, 0], ![61, 1, 0], ![38, 0, 1]] where
  M :=![![![-10, 1, 0], ![0, -15, 11], ![101, -4, -4]]]
  hmulB := by decide  
  f := ![![![104, 4, 11]], ![![105, 4, 11]], ![![77, 3, 8]]]
  g := ![![![-1, 1, 0], ![7, -15, 11], ![7, -4, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![6486, -1214, 419]] ![![359671031, 14036920, 36451270]]
  ![![-104, -4, -11]] where
 M := ![![![-104, -4, -11]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![-104, -4, -11]] ![![-10, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![-71, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1052, -1215, 803]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![1052, -1215, 803]] 
 ![![73, 0, 0], ![18, 1, 0], ![65, 0, 1]] where
  M :=![![![1052, -1215, 803], ![81103, 3915, -8547], ![-41612, 10481, -4632]]]
  hmulB := by decide  
  f := ![![![71446827, 2788363, 7240860]], ![![27635202, 1078522, 2800721]], ![![77493086, 3024331, 7853625]]]
  g := ![![![-401, -1215, 803], ![7756, 3915, -8547], ![970, 10481, -4632]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15, -11, 9]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-15, -11, 9]] 
 ![![73, 0, 0], ![36, 1, 0], ![18, 0, 1]] where
  M :=![![![-15, -11, 9], ![909, 4, -67], ![-202, 107, -63]]]
  hmulB := by decide  
  f := ![![![6917, 270, 701]], ![![4381, 171, 444]], ![![3049, 119, 309]]]
  g := ![![![3, -11, 9], ![27, 4, -67], ![-40, 107, -63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![1052, -1215, 803]] ![![1052, -1215, 803]]
  ![![-130847877, 2381338, 7509865]] where
 M := ![![![-130847877, 2381338, 7509865]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI73N1 : IdealMulLeCertificate' Table 
  ![![-130847877, 2381338, 7509865]] ![![-15, -11, 9]]
  ![![73, 0, 0]] where
 M := ![![![2610361667, 2252407554, -1810302034]]]
 hmul := by decide  
 g := ![![![![35758379, 30854898, -24798658]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [40, 44, 76, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 73, 9], [75, 5, 70], [0, 1]]
 g := ![![[65, 30, 67], [10, 70, 45], [13, 58, 26], [24, 73, 40], [3, 1], []], ![[3, 25], [0, 65, 39, 62], [19, 41, 12, 13], [9, 40, 73, 50], [23, 25], [56, 2]], ![[70, 5, 41, 29], [24, 3, 57, 37], [62, 14, 54, 60], [16, 29, 76, 34], [14, 36], [74, 2]]]
 h' := ![![[7, 73, 9], [74, 61, 64], [33, 17, 19], [67, 75, 42], [38, 65, 44], [0, 0, 1], [0, 1]], ![[75, 5, 70], [28, 28], [77, 52, 11], [52, 11, 16], [74, 29, 15], [21, 58, 5], [7, 73, 9]], ![[0, 1], [66, 69, 15], [40, 10, 49], [70, 72, 21], [39, 64, 20], [58, 21, 73], [75, 5, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 63], []]
 b := ![[], [10, 66, 72], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [40, 44, 76, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![27638387, -237790, 526535]
  a := ![0, -14, 31]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![349853, -3010, 6665]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀



lemma PB148I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB148I1 : PrimesBelowBoundCertificateInterval O 31 79 148 where
  m := 11
  g := ![2, 2, 2, 2, 3, 1, 1, 1, 3, 3, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB148I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0]
    · exact ![I61N0]
    · exact ![I67N0]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N0, I73N1]
    · exact ![I79N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1369, 37]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![53, 53, 53]
    · exact ![205379]
    · exact ![226981]
    · exact ![300763]
    · exact ![71, 71, 71]
    · exact ![73, 73, 73]
    · exact ![493039]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
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
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N1, I41N1, I43N1, I47N1, I53N0, I53N1, I53N2, I71N0, I71N1, I71N2, I73N0, I73N1]
  Il := ![[I37N1], [I41N1], [I43N1], [I47N1], [I53N0, I53N1, I53N2], [], [], [], [I71N0, I71N1, I71N2], [I73N0, I73N0, I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
