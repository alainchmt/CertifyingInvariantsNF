
import IdealArithmetic.Examples.NF3_1_903756_2.RI3_1_903756_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-227961207, -44309970, 40076074]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-227961207, -44309970, 40076074]] 
 ![![83, 0, 0], ![5, 1, 0], ![82, 0, 1]] where
  M :=![![![-227961207, -44309970, 40076074], ![7156681662, 61039103, -367181448], ![-4702258220, 499819482, -120434673]]]
  hmulB := by decide  
  f := ![![![-176173216729351617, -14694345799683858, -13823591336714938]], ![![-41799526282702737, -3486436274843107, -3279837764942674]], ![![-220605714659876486, -18400394320883910, -17310027611558045]]]
  g := ![![![-39670475, -44309970, 40076074], ![445305601, 61039103, -367181448], ![32220332, 499819482, -120434673]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-87243686, -7276866, -6845655]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-87243686, -7276866, -6845655]] 
 ![![83, 0, 0], ![22, 1, 0], ![66, 0, 1]] where
  M :=![![![-87243686, -7276866, -6845655], ![-1281862329, -106918229, -100582491], ![-1913547153, -159606120, -150148214]]]
  hmulB := by decide  
  f := ![![![51914, 8724, -8211]], ![![-3923, 2233, -1317]], ![![52107, 5682, -6182]]]
  g := ![![![6321212, -7276866, -6845655], ![92876905, -106918229, -100582491], ![138645417, -159606120, -150148214]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-511670154, -42677646, -40148663]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![-511670154, -42677646, -40148663]] 
 ![![83, 0, 0], ![55, 1, 0], ![7, 0, 1]] where
  M :=![![![-511670154, -42677646, -40148663], ![-7517915913, -627058177, -589900095], ![-11222645573, -936064164, -880595070]]]
  hmulB := by decide  
  f := ![![![308190, -7512, -9019]], ![![183975, -1627, -7298]], ![![193, -3042, 2029]]]
  g := ![![![25501699, -42677646, -40148663], ![374693789, -627058177, -589900095], ![559337939, -936064164, -880595070]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-227961207, -44309970, 40076074]] ![![-87243686, -7276866, -6845655]]
  ![![-308190, 7512, 9019]] where
 M := ![![![-308190, 7512, 9019]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![-308190, 7512, 9019]] ![![-511670154, -42677646, -40148663]]
  ![![83, 0, 0]] where
 M := ![![![-83, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1, I83N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
    exact isPrimeI83N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [30, 53, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 18, 36], [11, 70, 53], [0, 1]]
 g := ![![[73, 73, 1], [74, 67], [65, 5], [62, 53, 79], [16, 46, 1], []], ![[40, 43, 74, 69], [39, 40], [21, 55], [86, 5, 8, 85], [79, 20, 44, 2], [36, 50]], ![[31, 57, 67, 2], [11, 78], [35, 71], [15, 68, 39, 16], [62, 5, 45, 84], [19, 50]]]
 h' := ![![[35, 18, 36], [5, 31, 88], [0, 18, 45], [9, 87, 19], [54, 86, 48], [0, 0, 1], [0, 1]], ![[11, 70, 53], [55, 36, 67], [35, 51, 60], [24, 3, 12], [56, 82, 48], [56, 77, 70], [35, 18, 36]], ![[0, 1], [83, 22, 23], [18, 20, 73], [0, 88, 58], [7, 10, 82], [85, 12, 18], [11, 70, 53]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 88], []]
 b := ![[], [21, 55, 47], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [30, 53, 43, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4460591, -177199, -133144]
  a := ![-4, 1, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-50119, -1991, -1496]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def PBC89 : ContainsPrimesAboveP 89 ![I89N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![89, 0, 0]]) timesTableT_eq_Table B_one_repr 89 (by decide) 𝕀

instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![586331, 48905, 46007]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![586331, 48905, 46007]] 
 ![![97, 0, 0], ![0, 97, 0], ![49, 24, 1]] where
  M :=![![![586331, 48905, 46007], ![8614901, 718556, 675976], ![12860210, 1072651, 1009088]]]
  hmulB := by decide  
  f := ![![![-984, 61, 4]], ![![976, -1086, 683]], ![![-137, -234, 163]]]
  g := ![![![-17196, -10879, 46007], ![-252659, -159844, 675976], ![-377166, -238613, 1009088]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [9, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 96], [0, 1]]
 g := ![![[81, 54], [36], [48], [1], [88], [47, 1]], ![[0, 43], [36], [48], [1], [88], [94, 96]]]
 h' := ![![[47, 96], [48, 32], [9, 91], [76, 40], [45, 1], [62, 66], [0, 1]], ![[0, 1], [0, 65], [18, 6], [16, 57], [92, 96], [60, 31], [47, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [41, 87]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [9, 50, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10189, 8926, 4939]
  a := ![9, -7, 25]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2600, -1130, 4939]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![984, -61, -4]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![984, -61, -4]] 
 ![![97, 0, 0], ![24, 1, 0], ![67, 0, 1]] where
  M :=![![![984, -61, -4], ![-976, 1086, -683], ![-11503, -377, 777]]]
  hmulB := by decide  
  f := ![![![-586331, -48905, -46007]], ![![-233885, -19508, -18352]], ![![-537571, -44838, -42181]]]
  g := ![![![28, -61, -4], ![193, 1086, -683], ![-562, -377, 777]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![586331, 48905, 46007]] ![![984, -61, -4]]
  ![![97, 0, 0]] where
 M := ![![![-97, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-50, 20, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-50, 20, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![51, 20, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-50, 20, 1], ![263, -85, 223], ![3745, 118, 16]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-51, -20, 101]], ![![-1, 0, 1], ![-110, -45, 223], ![29, -2, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [27, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [75, 100], [0, 1]]
 g := ![![[87, 84], [95], [74, 30], [71], [31], [75, 1]], ![[24, 17], [95], [1, 71], [71], [31], [49, 100]]]
 h' := ![![[75, 100], [40, 65], [22, 14], [18, 63], [97, 77], [96, 43], [0, 1]], ![[0, 1], [67, 36], [62, 87], [97, 38], [14, 24], [89, 58], [75, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [6, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [27, 26, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10476262, 4539612, 1671725]
  a := ![-196, 67, -523]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-740413, -286088, 1671725]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-21, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-21, 1, 0]] 
 ![![101, 0, 0], ![80, 1, 0], ![85, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-21, 1, 0], ![4, -23, 11], ![183, 5, -18]]]
  hmulB := by decide  
  f := ![![![2563, -15450, 7392], ![-606, -67872, 0]], ![![2024, -12231, 5852], ![-504, -53732, 0]], ![![2147, -13002, 6221], ![-558, -57120, 0]]]
  g := ![![![1, 0, 0], ![-80, 101, 0], ![-85, 0, 101]], ![![-1, 1, 0], ![9, -23, 11], ![13, 5, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-50, 20, 1]] ![![101, 0, 0], ![-21, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-2121, 101, 0]], ![![-5050, 2020, 101], ![1313, -505, 202]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-21, 1, 0]]], ![![![-50, 20, 1]], ![![13, -5, 2]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![12, 10, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![12, 10, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![12, 10, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![12, 10, 1], ![223, -3, 113], ![1915, 68, 48]]]
  hmulB := by decide  
  f := ![![![-11, -10, -1], ![103, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-12, -10, 103]], ![![0, 0, 1], ![-11, -11, 113], ![13, -4, 48]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [60, 74, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 102], [0, 1]]
 g := ![![[39, 91], [59, 34], [], [13], [98], [29, 1]], ![[0, 12], [15, 69], [], [13], [98], [58, 102]]]
 h' := ![![[29, 102], [65, 83], [0, 72], [22], [9, 42], [11, 60], [0, 1]], ![[0, 1], [0, 20], [28, 31], [22], [94, 61], [0, 43], [29, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [71, 91]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [60, 74, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2156, 10014, 1846]
  a := ![-9, 6, -25]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-236, -82, 1846]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-10, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-10, 1, 0]] 
 ![![103, 0, 0], ![93, 1, 0], ![55, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-10, 1, 0], ![4, -12, 11], ![183, 5, -7]]]
  hmulB := by decide  
  f := ![![![6545, -19864, 18216], ![-824, -170568, 0]], ![![5911, -17933, 16445], ![-720, -153985, 0]], ![![3495, -10607, 9727], ![-439, -91080, 0]]]
  g := ![![![1, 0, 0], ![-93, 103, 0], ![-55, 0, 103]], ![![-1, 1, 0], ![5, -12, 11], ![1, 5, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![12, 10, 1]] ![![103, 0, 0], ![-10, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-1030, 103, 0]], ![![1236, 1030, 103], ![103, -103, 103]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-10, 1, 0]]], ![![![12, 10, 1]], ![![1, -1, 1]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-14, -17, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-14, -17, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![93, 90, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-14, -17, 1], ![115, 25, -184], ![-3026, -67, -59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-93, -90, 107]], ![![-1, -1, 1], ![161, 155, -184], ![23, 49, -59]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [70, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 106], [0, 1]]
 g := ![![[10, 99], [105, 53], [64], [102, 3], [101], [49, 1]], ![[46, 8], [27, 54], [64], [35, 104], [101], [98, 106]]]
 h' := ![![[49, 106], [33, 45], [106, 69], [29, 8], [28, 89], [101, 84], [0, 1]], ![[0, 1], [98, 62], [63, 38], [100, 99], [2, 18], [44, 23], [49, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [65, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [70, 58, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6117, 2116, 121]
  a := ![-4, 1, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-48, -82, 121]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-30, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-30, 1, 0]] 
 ![![107, 0, 0], ![77, 1, 0], ![59, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-30, 1, 0], ![4, -32, 11], ![183, 5, -27]]]
  hmulB := by decide  
  f := ![![![28609, -251808, 86592], ![-10272, -842304, 0]], ![![20587, -181179, 62304], ![-7382, -606048, 0]], ![![15763, -138847, 47747], ![-5707, -464448, 0]]]
  g := ![![![1, 0, 0], ![-77, 107, 0], ![-59, 0, 107]], ![![-1, 1, 0], ![17, -32, 11], ![13, 5, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-14, -17, 1]] ![![107, 0, 0], ![-30, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-3210, 107, 0]], ![![-1498, -1819, 107], ![535, 535, -214]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-30, 1, 0]]], ![![![-14, -17, 1]], ![![5, 5, -2]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![45, -13, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![45, -13, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![45, 96, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![45, -13, 1], ![131, 76, -140], ![-2294, -47, 12]]]
  hmulB := by decide  
  f := ![![![-44, 13, -1], ![109, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-45, -96, 109]], ![![0, -1, 1], ![59, 124, -140], ![-26, -11, 12]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [15, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [71, 108], [0, 1]]
 g := ![![[97, 80], [1], [13, 89], [98, 108], [35], [71, 1]], ![[0, 29], [1], [10, 20], [27, 1], [35], [33, 108]]]
 h' := ![![[71, 108], [78, 25], [23, 108], [56, 78], [100, 33], [25, 12], [0, 1]], ![[0, 1], [0, 84], [61, 1], [35, 31], [45, 76], [5, 97], [71, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [54, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [15, 38, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![143303, 9858, 7794]
  a := ![7, 16, 19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1903, -6774, 7794]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![31, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![31, 1, 0]] 
 ![![109, 0, 0], ![31, 1, 0], ![97, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![31, 1, 0], ![4, 29, 11], ![183, 5, 34]]]
  hmulB := by decide  
  f := ![![![16279, 130098, 49368], ![5886, -489192, 0]], ![![4608, 36988, 14036], ![1745, -139084, 0]], ![![14478, 115775, 43933], ![5269, -435336, 0]]]
  g := ![![![1, 0, 0], ![-31, 109, 0], ![-97, 0, 109]], ![![0, 1, 0], ![-18, 29, 11], ![-30, 5, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![45, -13, 1]] ![![109, 0, 0], ![31, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![3379, 109, 0]], ![![4905, -1417, 109], ![1526, -327, -109]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![31, 1, 0]]], ![![![45, -13, 1]], ![![14, -3, -1]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8522283, -172970, 504424]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-8522283, -172970, 504424]] 
 ![![113, 0, 0], ![64, 1, 0], ![30, 0, 1]] where
  M :=![![![-8522283, -172970, 504424], ![91617712, -5654223, -389398], ![11222530, 8214782, -6014649]]]
  hmulB := by decide  
  f := ![![![-37206986393963, -3103379358038, -2919479954612]], ![![-25910844941060, -2161185012083, -2033117963694]], ![![-17099856729928, -1426273599242, -1341755777293]]]
  g := ![![![-111371, -172970, 504424], ![4116548, -5654223, -389398], ![-2956496, 8214782, -6014649]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-193350303, -16127061, -15171407]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-193350303, -16127061, -15171407]] 
 ![![113, 0, 0], ![77, 1, 0], ![102, 0, 1]] where
  M :=![![![-193350303, -16127061, -15171407], ![-2840875725, -236953216, -222911892], ![-4240821758, -353720631, -332759928]]]
  hmulB := by decide  
  f := ![![![115404, 13791, -14500]], ![![55644, 9533, -8923]], ![![115597, 10749, -12471]]]
  g := ![![![22972716, -16127061, -15171407], ![337535707, -236953216, -222911892], ![503868845, -353720631, -332759928]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-48760, -4067, -3826]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![-48760, -4067, -3826]] 
 ![![113, 0, 0], ![84, 1, 0], ![83, 0, 1]] where
  M :=![![![-48760, -4067, -3826], ![-716426, -59756, -56215], ![-1069471, -89203, -83917]]]
  hmulB := by decide  
  f := ![![![2393, -239, 51]], ![![1853, -150, 16]], ![![1409, -178, 55]]]
  g := ![![![5402, -4067, -3826], ![79371, -59756, -56215], ![118484, -89203, -83917]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-8522283, -172970, 504424]] ![![-193350303, -16127061, -15171407]]
  ![![-2393, 239, -51]] where
 M := ![![![-2393, 239, -51]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![-2393, 239, -51]] ![![-48760, -4067, -3826]]
  ![![113, 0, 0]] where
 M := ![![![-113, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [43, 40, 97, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 116, 124], [106, 10, 3], [0, 1]]
 g := ![![[114, 125, 62], [72, 71, 68], [12, 36, 124], [49, 14, 87], [107, 89, 11], [1]], ![[2, 39, 69, 4], [30, 45, 118, 81], [49, 66, 117, 82], [4, 126, 19, 47], [115, 81, 61, 9], [13, 35, 36, 100]], ![[1, 59, 103, 86], [22, 98, 62, 80], [103, 119, 125, 119], [123, 94, 80, 96], [95, 32, 23, 59], [114, 30, 64, 27]]]
 h' := ![![[51, 116, 124], [79, 100, 58], [119, 41, 24], [52, 57, 88], [98, 92, 77], [84, 87, 30], [0, 1]], ![[106, 10, 3], [43, 30, 26], [76, 56, 117], [45, 89, 74], [113, 59, 113], [12, 26, 39], [51, 116, 124]], ![[0, 1], [2, 124, 43], [117, 30, 113], [15, 108, 92], [70, 103, 64], [61, 14, 58], [106, 10, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 84], []]
 b := ![[], [52, 72, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [43, 40, 97, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-20047331, -822198, 239268]
  a := ![-7, 6, -19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-157853, -6474, 1884]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def PBC127 : ContainsPrimesAboveP 127 ![I127N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![127, 0, 0]]) timesTableT_eq_Table B_one_repr 127 (by decide) 𝕀

instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [63, 88, 130, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 77, 119], [115, 53, 12], [0, 1]]
 g := ![![[33, 82, 7], [129, 24, 62], [60, 15], [130, 89], [45, 102], [1, 1], []], ![[129, 110, 35, 118], [0, 98, 70, 92], [110, 35], [12, 121], [25, 77], [43, 58], [130, 13]], ![[120, 34, 60, 35], [68, 52, 62, 100], [121, 52], [59, 113], [128, 16], [125, 34], [106, 13]]]
 h' := ![![[17, 77, 119], [126, 51, 20], [83, 79, 18], [123, 130, 43], [86, 125, 73], [68, 111, 44], [0, 0, 1], [0, 1]], ![[115, 53, 12], [42, 9, 55], [33, 94, 6], [46, 106, 64], [4, 1, 11], [20, 6, 83], [90, 53, 53], [17, 77, 119]], ![[0, 1], [36, 71, 56], [75, 89, 107], [10, 26, 24], [94, 5, 47], [125, 14, 4], [128, 78, 77], [115, 53, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [112, 60], []]
 b := ![[], [109, 36, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [63, 88, 130, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![38323002, 3104307, 1413621]
  a := ![8, -3, 22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![292542, 23697, 10791]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def PBC131 : ContainsPrimesAboveP 131 ![I131N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![131, 0, 0]]) timesTableT_eq_Table B_one_repr 131 (by decide) 𝕀

instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![38, 23, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![38, 23, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![38, 23, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![38, 23, 1], ![275, -3, 256], ![4294, 133, 113]]]
  hmulB := by decide  
  f := ![![![-37, -23, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-38, -23, 137]], ![![0, 0, 1], ![-69, -43, 256], ![0, -18, 113]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [106, 102, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 136], [0, 1]]
 g := ![![[63, 105], [1], [63], [62, 30], [99], [129], [1]], ![[39, 32], [1], [63], [16, 107], [99], [129], [1]]]
 h' := ![![[35, 136], [29, 70], [51, 136], [4, 101], [17, 116], [28, 109], [31, 35], [0, 1]], ![[0, 1], [13, 67], [16, 1], [114, 36], [104, 21], [7, 28], [23, 102], [35, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85]]
 b := ![[], [44, 111]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [106, 102, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![61701, 27110, 5795]
  a := ![-15, 5, -40]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1157, -775, 5795]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![18, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![18, 1, 0]] 
 ![![137, 0, 0], ![18, 1, 0], ![24, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![18, 1, 0], ![4, 16, 11], ![183, 5, 21]]]
  hmulB := by decide  
  f := ![![![32563, 133017, 91476], ![5343, -1139292, 0]], ![![4260, 17466, 12012], ![823, -149604, 0]], ![![5700, 23302, 16025], ![970, -199584, 0]]]
  g := ![![![1, 0, 0], ![-18, 137, 0], ![-24, 0, 137]], ![![0, 1, 0], ![-4, 16, 11], ![-3, 5, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![38, 23, 1]] ![![137, 0, 0], ![18, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![2466, 137, 0]], ![![5206, 3151, 137], ![959, 411, 274]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![18, 1, 0]]], ![![![38, 23, 1]], ![![7, 3, 2]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0)


lemma PB269I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB269I2 : PrimesBelowBoundCertificateInterval O 79 137 269 where
  m := 11
  g := ![3, 1, 2, 2, 2, 2, 2, 3, 1, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB269I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0]
    · exact ![I131N0]
    · exact ![I137N0, I137N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![83, 83, 83]
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![113, 113, 113]
    · exact ![2048383]
    · exact ![2248091]
    · exact ![18769, 137]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
      exact NI83N2
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N0, I83N1, I83N2, I97N1, I101N1, I103N1, I107N1, I109N1, I113N0, I113N1, I113N2, I137N1]
  Il := ![[I83N0, I83N1, I83N2], [], [I97N1], [I101N1], [I103N1], [I107N1], [I109N1], [I113N0, I113N1, I113N2], [], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
